// CD+G player core support.
//
// The core streams the disc itself and asks for one sector at a time over EXT_BUS:
//   UIO_CD_GET (0x34): word 0 = {command count, request count}, word 1 = LBA[15:0],
//                      word 2 = {lyrics channel [7:4], LBA[19:16]}, word 3 = {audio mode [5:4], command [3:0]},
//                      word 4 = CD+G channels the disc has used so far (bit n = channel n).
//                      Commands: 1 next track, 2 previous track, 3 restart track, 4 fast forward step, 5 rewind step
//                      (the core repeats 4 / 5 every 0.2 s while held), 6 lyrics channel changed, 7 track info (repeated
//                      every 0.5 s while held), 8 next end-of-disc mode, 9 audio mode changed.
//                      A new request count = send sector LBA; a new command count = run the command.
//   UIO_CD_SET (0x35): flags (bit 0 disc loaded, bit 1 seek, bit 2 new disc: the core forgets the channels seen and
//                      goes back to lyrics channel 1, bit 3 hold: stopped until Start), seek LBA [15:0], [19:16].
// A sector goes to the core as one download on ioctl index 2: 2448 bytes = 2352 bytes CD audio (16-bit
// little-endian, the CHD stores it big-endian) + 96 bytes subcode as stored in the CHD (raw P-W, R..W in
// bits 5..0). Tracks without subcode send zeros there (audio only).
// End of a track / the disc: the core asks ~6 sectors ahead of what it plays, so past the boundary it gets silence
// until the last real sector has played; the next request is not answered but replaced by the end action (a seek
// voids it): stop (back to the first track, held until Start), repeat the disc, or shuffle (every audio track once in
// a random order, then a new order that does not start with the track just played; next / previous follow it).
// CD drive (support/physical_disc, from Main_MiSTer_Physical_Disc): the tray is polled every 0.5 s while the core runs.
// A disc going in plays from the drive (raw P-W subcode, audio already little-endian), taking over from a CHD; picking a
// CHD in the OSD takes over from the drive; the disc coming out stops it. A disc already in when the core starts plays
// unless a CHD was mounted.

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <inttypes.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <scsi/sg.h>
#include <limits.h>
#include <linux/cdrom.h>
#include <pthread.h>

#include "../../user_io.h"
#include "../../spi.h"
#include "../../cd.h"
#include "../../menu.h"
#include "../../hardware.h"
#include "../chd/mister_chd.h"
#include "../physical_disc/physical_disc.h"
#include "cdgplayer.h"

#define CDG_SECTOR_INDEX 2
#define CDG_SECTOR_SIZE  2448
#define CDG_AUDIO_SIZE   2352
#define CDG_SCAN_FWD     60       // sectors per fast forward step (+ ~15 played per 0.2 s step = ~5x)
#define CDG_SCAN_BACK    90       // sectors per rewind step (- ~15 played = ~-5x)
#define CDG_AHEAD        6        // requests run this many sectors ahead of what plays
#define CDG_PAD          7        // silent sectors past a boundary before the end action
#define CDG_TRAY_MS      500      // CD drive tray poll period
#define CDG_PRIME        300      // CD drive: sectors (4 s) read into its cache before a disc starts playing
#define CDG_PRIME_MS     10000    // ... giving up (and playing anyway) after this long
#define CDG_HEAD         75       // CD drive: first second of the disc served from Main's own reads (see read_head)

enum { END_STOP, END_REPEAT, END_SHUFFLE };

static toc_t toc = {};
static int loaded = 0;
static uint8_t *hunkbuf = NULL;
static int hunknum = -1;
static uint8_t last_req = 0, last_cmd = 0;

static int chan_sel = 1;
static uint16_t chan_seen = 0;
static int aud_mode = 0;

static int end_mode = END_STOP;   // kept across discs
static int order[100], order_n = 0, order_idx = 0;
static int pad_cnt = 0;
static int stopped = 0;           // held at the first track after the end of the disc (stop mode)

static int drive = 0;             // playing the CD drive (else a CHD)
static int tray_in = -1;          // disc in the drive at the last poll (-1 = not known yet)
static unsigned long tray_tmr = 0;
static uint8_t head[CDG_HEAD][CDG_SECTOR_SIZE];   // start of the disc, read directly (read_head)
static int head_lba = 0, head_n = 0;

static void send_set(uint16_t flags, uint32_t lba)
{
	if (drive && (flags & 2)) physical_disc_seek_hint(lba);
	spi_uio_cmd_cont(UIO_CD_SET);
	spi_w(flags);
	spi_w(lba & 0xFFFF);
	spi_w((lba >> 16) & 0xF);
	spi_w(0);
	DisableIO();
	pad_cnt = 0;
	stopped = (flags & 8) ? 1 : 0;
}

static void read_get(uint8_t *req, uint8_t *cmd, int *lba, int *code)
{
	uint16_t w0 = spi_uio_cmd_cont(UIO_CD_GET);
	uint16_t w1 = spi_w(0);
	uint16_t w2 = spi_w(0);
	uint16_t w3 = spi_w(0);
	uint16_t w4 = spi_w(0);
	DisableIO();
	*req = w0 & 0xFF;
	*cmd = w0 >> 8;
	*lba = w1 | ((w2 & 0xF) << 16);
	*code = w3 & 0xF;
	aud_mode = (w3 >> 4) & 3;
	chan_sel = (w2 >> 4) & 0xF;
	chan_seen = w4;
}

static int is_audio(int t) { return t >= 0 && t < toc.last && toc.tracks[t].type == TT_CDDA; }

static int first_audio()
{
	for (int t = 0; t < toc.last; t++) if (is_audio(t)) return t;
	return 0;
}

static int last_audio()
{
	for (int t = toc.last - 1; t >= 0; t--) if (is_audio(t)) return t;
	return 0;
}

// new shuffle order of all audio tracks; first >= 0: that track goes first (it keeps playing),
// avoid >= 0: that track must not go first (it was just played)
static void make_order(int first, int avoid)
{
	order_n = 0;
	for (int t = 0; t < toc.last && order_n < 100; t++) if (is_audio(t)) order[order_n++] = t;
	for (int i = order_n - 1; i > 0; i--)
	{
		int j = rand() % (i + 1);
		int x = order[i]; order[i] = order[j]; order[j] = x;
	}
	if (first >= 0)
	{
		for (int i = 0; i < order_n; i++)
			if (order[i] == first) { order[i] = order[0]; order[0] = first; break; }
	}
	else if (avoid >= 0 && order_n > 1 && order[0] == avoid)
	{
		int k = 1 + rand() % (order_n - 1);
		order[0] = order[k]; order[k] = avoid;
	}
	order_idx = 0;
}

// track that is playing, from the request LBA (requests run ahead)
static int playing_track(int lba)
{
	if (stopped) return first_audio();
	if (end_mode == END_SHUFFLE && order_n) return order[order_idx];
	int at = lba > CDG_AHEAD ? lba - CDG_AHEAD : 0;
	int t = toc.GetTrackByLBA(at);
	return t >= toc.last ? toc.last - 1 : t;
}

static int playing_pos(int lba, int t)
{
	if (stopped) return toc.tracks[t].start;
	int at = lba > CDG_AHEAD ? lba - CDG_AHEAD : 0;
	if (at < toc.tracks[t].start) at = toc.tracks[t].start;
	if (at > toc.tracks[t].end) at = toc.tracks[t].end;
	return at;
}

// first sector past what plays now: end of the track (shuffle) or of the last audio track
static int boundary()
{
	if (end_mode == END_SHUFFLE && order_n) return toc.tracks[order[order_idx]].end;
	return toc.tracks[last_audio()].end;
}

static void play_track(int t) { send_set(3, toc.tracks[t].start); }

static void end_reached()
{
	switch (end_mode)
	{
	case END_STOP:   send_set(1 | 2 | 8, toc.tracks[first_audio()].start); break;
	case END_REPEAT: play_track(first_audio()); break;
	default:
		if (++order_idx >= order_n) make_order(-1, order[order_n - 1]);
		play_track(order[order_idx]);
		break;
	}
}

static void unload()
{
	if (drive) physical_disc_close();
	drive = 0;
	head_n = 0;
	if (toc.chd_f) chd_close(toc.chd_f);
	toc.chd_f = NULL;
	free(hunkbuf);
	hunkbuf = NULL;
	hunknum = -1;
	loaded = 0;
	order_n = 0;
	stopped = 0;
}

// drop the current disc and get in step with the core's counters before the next one starts
static void new_disc()
{
	unload();
	toc = toc_t();
	srand(time(NULL));
	uint8_t req, cmd; int lba, code;
	read_get(&req, &cmd, &lba, &code);
	last_req = req;
	last_cmd = cmd;
}

// One raw sector (audio + P-W subcode) straight from the drive, bypassing physical_disc's cache. Unlike
// physical_disc's scsi_read_cd it checks resid: a "successful" read that transferred less is a failure.
static int direct_read(int fd, int lba, uint8_t *dst)
{
	uint8_t cdb[12] = { 0xBE, 0x04 }, sense[32];
	cdb[2] = (lba >> 24) & 0xFF; cdb[3] = (lba >> 16) & 0xFF; cdb[4] = (lba >> 8) & 0xFF; cdb[5] = lba & 0xFF;
	cdb[8] = 1; cdb[9] = 0x10; cdb[10] = 0x01;
	struct sg_io_hdr io;
	memset(&io, 0, sizeof(io));
	io.interface_id = 'S'; io.cmd_len = 12; io.cmdp = cdb; io.dxfer_direction = SG_DXFER_FROM_DEV;
	io.dxfer_len = CDG_SECTOR_SIZE; io.dxferp = dst; io.sbp = sense; io.mx_sb_len = sizeof(sense); io.timeout = 3000;
	if (ioctl(fd, SG_IO, &io) < 0) return -1;
	if (io.status || io.host_status || io.driver_status) return -2;
	return io.resid ? -3 : 0;
}

// The first second of the disc (track 1) is read here, straight from the drive, and always served from this copy.
// HW 2026-11-15 (SuperStationOne dock drive, Information Society): physical_disc's cache held other audio for LBA 0-15
// every time (from ~17 s in after a re-insert; from LBA 300 right after a 300-sector prime). Its scsi_read_cd ignores
// resid, so a short transfer leaves the previous read in its buffer, and its read of the start after reading
// elsewhere came back short; every play of the track start, restart included, served it. Clearing its cache
// (physical_disc_load_toc) and priming again gave the same result 3 times in a row.
static void read_head()
{
	head_n = 0;
	head_lba = toc.tracks[0].start;
	int fd = open(physical_disc_device(), O_RDONLY | O_NONBLOCK);
	if (fd < 0) return;
	int n = toc.tracks[0].end - head_lba;
	if (n > CDG_HEAD) n = CDG_HEAD;
	for (int i = 0; i < n; i++)
	{
		int r = -1;
		for (int k = 0; k < 3 && r; k++) r = direct_read(fd, head_lba + i, head[i]);
		if (r) break;
		head_n++;
	}
	close(fd);
	printf("CDG: CD drive: first %d sectors read directly\n", head_n);
}

// one sector from the drive: the directly read start, else physical_disc's cache (0 = read ok)
static int drive_sector(int lba, uint8_t *buf)
{
	int i = lba - head_lba;
	if (i >= 0 && i < head_n)
	{
		memcpy(buf, head[i], CDG_SECTOR_SIZE);
		return 0;
	}
	// audio comes little-endian from the drive; read_sector_sub 0 = no subcode
	int r = physical_disc_read_sector(lba, buf, buf + CDG_AUDIO_SIZE);
	if (r || !physical_disc_read_sector_sub(lba, buf, buf + CDG_AUDIO_SIZE))
		memset(buf + CDG_AUDIO_SIZE, 0, CDG_SECTOR_SIZE - CDG_AUDIO_SIZE);
	return r;
}

// CD drive: read the start of the first track into the drive cache before playing, so the drive spinning up and
// settling at its capped speed does not starve the core (stutter at the start)
static void prime_drive(int t)
{
	static uint8_t tmp[CDG_SECTOR_SIZE];
	int lba = toc.tracks[t].start, end = lba + CDG_PRIME;
	if (end > toc.tracks[t].end) end = toc.tracks[t].end;
	unsigned long tmr = GetTimer(CDG_PRIME_MS);
	for (; lba < end && !CheckTimer(tmr); lba++) physical_disc_read_sector_sub(lba, tmp, tmp + CDG_AUDIO_SIZE);
	printf("CDG: CD drive primed %d of %d sectors\n", lba - toc.tracks[t].start, end - toc.tracks[t].start);
}

static void start_disc()
{
	loaded = 1;
	for (int t = 0; t < toc.last; t++)
		printf("CDG: track %2d start %6d end %6d %s subcode %d\n", t + 1, toc.tracks[t].start, toc.tracks[t].end,
		       toc.tracks[t].type == TT_CDDA ? "audio" : "data ", toc.tracks[t].sbc_type);
	int first = first_audio();
	if (end_mode == END_SHUFFLE)
	{
		make_order(-1, -1);
		first = order[0];
	}
	if (drive)
	{
		read_head();
		prime_drive(first);
	}
	send_set(7, toc.tracks[first].start);
}

static void open_drive()
{
	static int env_ready = 0;
	new_disc();
	if (!env_ready)
	{
		physical_disc_prepare_environment();
		env_ready = 1;
	}
	if (physical_disc_open(NULL) || physical_disc_load_toc(&toc))
	{
		physical_disc_close();
		toc = toc_t();
		Info("CD drive: cannot read the disc", 2000);
		send_set(4, 0);
		return;
	}
	int audio = 0;
	for (int t = 0; t < toc.last; t++) if (is_audio(t)) audio++;
	if (!audio)
	{
		physical_disc_close();
		toc = toc_t();
		Info("CD drive: no audio tracks", 2000);
		send_set(4, 0);
		return;
	}
	drive = 1;
	// physical_disc_prewarm_blocking() is not used: it also seeks to 1/4, 1/2 and 3/4 of the disc (for game
	// discs), which left the head away from track 1 when playback started; prime_drive() reads the start instead
	Info("CD drive: reading disc...", 10000);

	// the drive must hand over raw P-W subcode for the graphics; a sector a little into the first audio track tells
	static uint8_t probe[CDG_SECTOR_SIZE];
	int sub = physical_disc_read_sector_sub(toc.tracks[first_audio()].start + 16, probe, probe + CDG_AUDIO_SIZE);
	printf("CDG: CD drive %s, %d tracks (%d audio), subcode %s\n", physical_disc_device(), toc.last, audio, sub ? "yes" : "no");
	start_disc();
	char msg[96];
	snprintf(msg, sizeof(msg), "CD drive: %d tracks%s", audio, sub ? "" : "\nno subcode from the drive:\naudio only");
	Info(msg, sub ? 1500 : 4000);
}

// tray poll: disc in = play it from the drive, disc out = stop (only if the drive is what plays)
// Tray state from a thread of its own, on its own handle. HW 2026-11-15 (SuperStationOne dock drive): with the tray
// check on the main loop (physical_disc_tray_status every 0.5 s) a disc lost its first 1-2 s of audio when it started
// (not on a later restart of the track); with this thread it does not. Why is not measured: here the ioctl took
// <= 26 ms during the first 10 s of play.
static volatile int tray_state = -2;   // physical_disc_tray_t, -2 = not polled yet
static void *tray_thread(void *)
{
	int fd = -1;
	for (;;)
	{
		if (fd < 0)
		{
			char dev[16];
			for (int i = 0; i < 8 && fd < 0; i++)
			{
				snprintf(dev, sizeof(dev), "/dev/sr%d", i);
				fd = open(dev, O_RDONLY | O_NONBLOCK | O_CLOEXEC);
			}
		}
		int st = PHYSICAL_DISC_TRAY_NODRIVE;
		if (fd >= 0)
		{
			int r = ioctl(fd, CDROM_DRIVE_STATUS, CDSL_CURRENT);
			if (r < 0) { close(fd); fd = -1; }                                     // unplugged or reset: look again
			else st = r == CDS_DISC_OK ? PHYSICAL_DISC_TRAY_DISC :
			          r == CDS_DRIVE_NOT_READY ? PHYSICAL_DISC_TRAY_NOTREADY : PHYSICAL_DISC_TRAY_EMPTY;
		}
		tray_state = st;
		usleep(CDG_TRAY_MS * 1000);
	}
	return NULL;
}

static void poll_tray()
{
	static int started = 0;
	if (!started)
	{
		pthread_t th;
		started = !pthread_create(&th, NULL, tray_thread, NULL);
		if (started) pthread_detach(th);
	}
	if (tray_tmr && !CheckTimer(tray_tmr)) return;
	tray_tmr = GetTimer(CDG_TRAY_MS);
	int st = tray_state;
	if (st == -2 || st == PHYSICAL_DISC_TRAY_NOTREADY) return;   // not polled yet / spinning up: wait
	int in = st == PHYSICAL_DISC_TRAY_DISC;
	int was = tray_in;
	tray_in = in;
	if (in && was != 1)
	{
		if (was == 0 || !loaded) open_drive();             // at core start a mounted CHD wins
	}
	else if (!in && was == 1 && drive)
	{
		new_disc();
		send_set(4, 0);
		Info("CD drive: disc removed", 1500);
	}
}

void cdg_set_image(int num, const char *filename)
{
	(void)num;
	new_disc();

	if (!filename || !filename[0])
	{
		send_set(4, 0);
		return;
	}

	chd_error err = mister_load_chd(filename, &toc);
	if (err != CHDERR_NONE)
	{
		printf("CDG: cannot open %s: %s\n", filename, chd_error_string(err));
		toc.chd_f = NULL;
		send_set(4, 0);
		return;
	}
	hunkbuf = (uint8_t *)malloc(toc.chd_hunksize);
	if (toc.tracks[0].sbc_type == SUBCODE_RW)
		printf("CDG: subcode type RW (not RW_RAW): graphics may not decode\n");
	start_disc();
}

// returns 1 if the request was replaced by an end action (a seek, which voids it)
static int send_sector(int lba)
{
	static uint8_t buf[CDG_SECTOR_SIZE];
	memset(buf, 0, sizeof(buf));
	if (loaded && lba >= boundary())
	{
		if (++pad_cnt > CDG_PAD)
		{
			end_reached();
			return 1;
		}
	}
	else if (loaded && lba >= 0 && lba < toc.end)
	{
		int t = toc.GetTrackByLBA(lba);
		if (is_audio(t) && drive)
		{
			drive_sector(lba, buf);
		}
		else if (is_audio(t))
		{
			int f = lba + toc.tracks[t].offset;
			if (mister_chd_read_sector(toc.chd_f, f, 0, 0, CDG_AUDIO_SIZE, buf, hunkbuf, &hunknum) == CHDERR_NONE)
			{
				for (int i = 0; i < CDG_AUDIO_SIZE; i += 2)
				{
					uint8_t x = buf[i]; buf[i] = buf[i + 1]; buf[i + 1] = x;
				}
				if (toc.tracks[t].sbc_type != SUBCODE_NONE)
					mister_chd_read_sector(toc.chd_f, f, CDG_AUDIO_SIZE, CDG_AUDIO_SIZE, CDG_SECTOR_SIZE - CDG_AUDIO_SIZE,
					                       buf, hunkbuf, &hunknum);
			}
			else memset(buf, 0, sizeof(buf));
		}
	}
	user_io_set_index(CDG_SECTOR_INDEX);
	user_io_set_download(1);
	user_io_file_tx_data(buf, CDG_SECTOR_SIZE);
	user_io_set_download(0);
	return 0;
}

static const char *end_name()
{
	return end_mode == END_STOP ? "Stop" : end_mode == END_REPEAT ? "Repeat disc" : "Shuffle";
}

// popup after button A: the channel now drawn and the channels the disc has used so far (channel 0 is always drawn)
static void show_channel()
{
	char list[64] = "";
	int n = 0;
	for (int c = 1; c < 16; c++)
		if (chan_seen & (1 << c)) n += snprintf(list + n, sizeof(list) - n, "%s%d", n ? ", " : "", c);
	char msg[128];
	if (!n) snprintf(msg, sizeof(msg), "Lyrics channel %d\nNo other channels\non this disc yet", chan_sel);
	else snprintf(msg, sizeof(msg), "Lyrics channel %d\nDisc has: %s", chan_sel, list);
	Info(msg, 2000);
}

// button X (held: repeated every 0.5 s, so the popup stays up while held and goes ~0.2 s after release)
static void show_info(int lba)
{
	int t = playing_track(lba);
	int pos = (playing_pos(lba, t) - toc.tracks[t].start) / 75;
	int len = (toc.tracks[t].end - toc.tracks[t].start) / 75;
	char msg[128], mode[32];
	if (end_mode == END_SHUFFLE && order_n) snprintf(mode, sizeof(mode), "Shuffle %d of %d", order_idx + 1, order_n);
	else snprintf(mode, sizeof(mode), "End: %s", end_name());
	snprintf(msg, sizeof(msg), "%sTrack %d / %d\n%02d:%02d / %02d:%02d\n%s", stopped ? "Stopped\n" : "", t + 1, toc.last,
	         pos / 60, pos % 60, len / 60, len % 60, mode);
	Info(msg, 700);
}

static void show_end_mode()
{
	Info(end_mode == END_STOP ? "End of disc: Stop" : end_mode == END_REPEAT ? "End of disc: Repeat" :
	     "End of disc: Shuffle\nall tracks, new order\nevery pass", 2000);
}

static void show_audio()
{
	static const char *names[4] = { "Audio: Stereo", "Audio: Left channel", "Audio: Right channel", "Audio: Vocal cancel" };
	Info(names[aud_mode & 3], 2000);
}

// returns 1 if the core was told to seek (its outstanding request is then void)
static int run_command(int code, int lba)
{
	if (code == 9) { show_audio(); return 0; }
	if (!loaded || !toc.last) return 0;
	int t = playing_track(lba);
	int at = playing_pos(lba, t);
	int shuffle = end_mode == END_SHUFFLE && order_n;
	int to = -1;
	switch (code)
	{
	case 1:
		if (shuffle)
		{
			if (++order_idx >= order_n) make_order(-1, order[order_n - 1]);
			to = toc.tracks[order[order_idx]].start;
		}
		else if (stopped) to = toc.tracks[t].start;
		else
		{
			for (int n = t + 1; n < toc.last; n++) if (is_audio(n)) { to = toc.tracks[n].start; break; }
		}
		break;
	case 2:
		if (at - toc.tracks[t].start > 150 || stopped) to = toc.tracks[t].start;
		else if (shuffle) to = toc.tracks[order[order_idx > 0 ? --order_idx : 0]].start;
		else
		{
			to = toc.tracks[t].start;
			for (int n = t - 1; n >= 0; n--) if (is_audio(n)) { to = toc.tracks[n].start; break; }
		}
		break;
	case 3: to = toc.tracks[t].start; break;
	case 4: if (!stopped && at + CDG_SCAN_FWD < boundary()) to = at + CDG_SCAN_FWD; break;
	case 5:
		if (!stopped)
		{
			int lo = shuffle ? toc.tracks[t].start : toc.tracks[first_audio()].start;
			to = at - CDG_SCAN_BACK;
			if (to < lo) to = lo;
		}
		break;
	case 7: show_info(lba); return 0;
	case 8:
		end_mode = (end_mode + 1) % 3;
		if (end_mode == END_SHUFFLE) make_order(t, -1);   // the playing (or, stopped, the waiting) track stays first
		else order_n = 0;
		show_end_mode();
		return 0;
	}
	if (to < 0) return 0;
	if (code < 4) printf("CDG: command %d at LBA %d (track %d) -> LBA %d\n", code, at, t + 1, to);
	send_set(3, to);
	return 1;
}

void cdg_poll()
{
	poll_tray();
	uint8_t req, cmd; int lba, code;
	read_get(&req, &cmd, &lba, &code);
	if (cmd != last_cmd)
	{
		last_cmd = cmd;
		if (code == 6) show_channel();
		else if (run_command(code, lba))
		{
			last_req = req;
			return;
		}
	}
	if (req != last_req)
	{
		last_req = req;
		stopped = 0;          // a request = the core plays (Start after a stop)
		send_sector(lba);
	}
}
