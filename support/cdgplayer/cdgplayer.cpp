// CD+G player core support.
//
// The core plays the disc itself and asks Main for one sector at a time over EXT_BUS.
//
// UIO_CD_GET (0x34), five words read from the core:
//   0: command count (high byte), request count (low byte)
//   1: requested LBA, bits 15..0
//   2: lyrics channel in bits 7..4, LBA bits 19..16 in bits 3..0
//   3: audio mode in bits 5..4, command in bits 3..0
//   4: CD+G channels the disc has used so far, one bit per channel
// A new request count asks for the sector at that LBA. A new command count asks Main to run the command:
// 1 next track, 2 previous track, 3 restart track, 4 fast forward, 5 rewind, 6 lyrics channel changed, 7 track info,
// 8 next end-of-disc mode, 9 audio mode changed. The core repeats 4, 5 and 7 while the button is held.
//
// UIO_CD_SET (0x35), four words sent to the core: flags, seek LBA bits 15..0, LBA bits 19..16, unused.
// Flags: bit 0 disc loaded, bit 1 seek, bit 2 new disc (back to lyrics channel 1), bit 3 hold until Start.
//
// Each sector goes to the core as one download on ioctl index 2: 2352 bytes of CD audio (16-bit little-endian;
// the CHD stores it big-endian) followed by the 96 bytes of raw P-W subcode as stored in the CHD (R..W in bits 5..0).
// Tracks without subcode send zeros there.
//
// The core requests a few sectors ahead of what it plays. Past the end of the disc (in shuffle: of the track) Main
// sends silence until the last real sector has played, then answers the next request with the end action instead:
// stop at the first track, repeat the disc, or play the next track of the shuffle order.
//
// CD drive (support/physical_disc): inserting a disc plays it, taking over from a mounted CHD; mounting a CHD takes
// over from the drive; removing the disc stops playback. A disc already in the drive when the core starts plays
// unless a CHD is mounted.

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
#define CDG_SCAN_FWD     60       // sectors skipped per fast forward step (about 5x speed)
#define CDG_SCAN_BACK    90       // sectors skipped back per rewind step (about 5x speed)
#define CDG_AHEAD        6        // how far the core's requests run ahead of playback
#define CDG_PAD          7        // silent sectors sent past the end before the end action
#define CDG_TRAY_MS      500      // CD drive: tray poll period
#define CDG_PRIME        300      // CD drive: sectors read into the cache before playback starts (4 s)
#define CDG_PRIME_MS     10000    // CD drive: stop waiting for those after this long
#define CDG_HEAD         75       // CD drive: sectors at the start of track 1 read directly (see read_head)

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

// Read one sector (audio + raw P-W subcode) straight from the drive. A short transfer counts as a failure.
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

// physical_disc does not check for short transfers, and its read of the start of track 1 can come back short,
// leaving data from its previous read in the cache. The first second of track 1 is read here instead and always
// served from this copy.
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

// One sector from the drive: the start of track 1 from read_head, the rest from physical_disc's cache.
static int drive_sector(int lba, uint8_t *buf)
{
	int i = lba - head_lba;
	if (i >= 0 && i < head_n)
	{
		memcpy(buf, head[i], CDG_SECTOR_SIZE);
		return 0;
	}
	// the drive delivers audio little-endian; no subcode = zeros
	int r = physical_disc_read_sector(lba, buf, buf + CDG_AUDIO_SIZE);
	if (r || !physical_disc_read_sector_sub(lba, buf, buf + CDG_AUDIO_SIZE))
		memset(buf + CDG_AUDIO_SIZE, 0, CDG_SECTOR_SIZE - CDG_AUDIO_SIZE);
	return r;
}

// Fill physical_disc's cache with the first seconds of the track before playback starts.
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
	// physical_disc_prewarm_blocking() is not used: it also seeks across the disc, which suits game discs, not audio
	Info("CD drive: reading disc...", 10000);

	// the graphics need raw P-W subcode from the drive: check one sector
	static uint8_t probe[CDG_SECTOR_SIZE];
	int sub = physical_disc_read_sector_sub(toc.tracks[first_audio()].start + 16, probe, probe + CDG_AUDIO_SIZE);
	printf("CDG: CD drive %s, %d tracks (%d audio), subcode %s\n", physical_disc_device(), toc.last, audio, sub ? "yes" : "no");
	start_disc();
	char msg[96];
	snprintf(msg, sizeof(msg), "CD drive: %d tracks%s", audio, sub ? "" : "\nno subcode from the drive:\naudio only");
	Info(msg, sub ? 1500 : 4000);
}

// The tray is polled from a thread of its own, with its own handle on the drive. Polling it from the main loop
// made a disc lose the first seconds of audio when it started.
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

// Disc inserted: play it from the drive. Disc removed: stop, if the drive is what plays.
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

// button X: the core repeats the command every 0.5 s while held, so the popup stays up until release
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
		if (end_mode == END_SHUFFLE) make_order(t, -1);   // the current track stays first in the order
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
		stopped = 0;          // the core only requests while playing (also after Start ends a stop)
		send_sector(lba);
	}
}
