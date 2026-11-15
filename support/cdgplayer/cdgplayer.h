#ifndef CDGPLAYER_H
#define CDGPLAYER_H

// CD+G player core (CDGPLAYER): serves sectors (CD audio + raw subcode) from a CHD on the core's request.
void cdg_set_image(int num, const char *filename);
void cdg_poll();

#endif
