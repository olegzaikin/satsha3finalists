/* hash.c     April 2012
 * Groestl ANSI C code optimised for 32-bit machines
 * Author: Thomas Krinninger
 *
 *  This work is based on the implementation of
 *          Soeren S. Thomsen and Krystian Matusiewicz
 *          
 *
 */

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

#define P_TYPE 0
#define Q_TYPE 1

const int COLS512 = 8;

const uint8_t shift_Values[2][8] = {{0,1,2,3,4,5,6,7},{1,3,5,7,0,2,4,6}};

const uint8_t indices_cyclic[15] = {0,1,2,3,4,5,6,7,0,1,2,3,4,5,6};

const uint32_t T[512] = {0xa5f432c6, 0xc6a597f4, 0x84976ff8, 0xf884eb97, 0x99b05eee, 0xee99c7b0, 0x8d8c7af6, 0xf68df78c, 0xd17e8ff, 0xff0de517, 0xbddc0ad6, 0xd6bdb7dc, 0xb1c816de, 0xdeb1a7c8, 0x54fc6d91, 0x915439fc
, 0x50f09060, 0x6050c0f0, 0x3050702, 0x2030405, 0xa9e02ece, 0xcea987e0, 0x7d87d156, 0x567dac87, 0x192bcce7, 0xe719d52b, 0x62a613b5, 0xb56271a6, 0xe6317c4d, 0x4de69a31, 0x9ab559ec, 0xec9ac3b5
, 0x45cf408f, 0x8f4505cf, 0x9dbca31f, 0x1f9d3ebc, 0x40c04989, 0x894009c0, 0x879268fa, 0xfa87ef92, 0x153fd0ef, 0xef15c53f, 0xeb2694b2, 0xb2eb7f26, 0xc940ce8e, 0x8ec90740, 0xb1de6fb, 0xfb0bed1d
, 0xec2f6e41, 0x41ec822f, 0x67a91ab3, 0xb3677da9, 0xfd1c435f, 0x5ffdbe1c, 0xea256045, 0x45ea8a25, 0xbfdaf923, 0x23bf46da, 0xf7025153, 0x53f7a602, 0x96a145e4, 0xe496d3a1, 0x5bed769b, 0x9b5b2ded
, 0xc25d2875, 0x75c2ea5d, 0x1c24c5e1, 0xe11cd924, 0xaee9d43d, 0x3dae7ae9, 0x6abef24c, 0x4c6a98be, 0x5aee826c, 0x6c5ad8ee, 0x41c3bd7e, 0x7e41fcc3, 0x206f3f5, 0xf502f106, 0x4fd15283, 0x834f1dd1
, 0x5ce48c68, 0x685cd0e4, 0xf4075651, 0x51f4a207, 0x345c8dd1, 0xd134b95c, 0x818e1f9, 0xf908e918, 0x93ae4ce2, 0xe293dfae, 0x73953eab, 0xab734d95, 0x53f59762, 0x6253c4f5, 0x3f416b2a, 0x2a3f5441
, 0xc141c08, 0x80c1014, 0x52f66395, 0x955231f6, 0x65afe946, 0x46658caf, 0x5ee27f9d, 0x9d5e21e2, 0x28784830, 0x30286078, 0xa1f8cf37, 0x37a16ef8, 0xf111b0a, 0xa0f1411, 0xb5c4eb2f, 0x2fb55ec4
, 0x91b150e, 0xe091c1b, 0x365a7e24, 0x2436485a, 0x9bb6ad1b, 0x1b9b36b6, 0x3d4798df, 0xdf3da547, 0x266aa7cd, 0xcd26816a, 0x69bbf54e, 0x4e699cbb, 0xcd4c337f, 0x7fcdfe4c, 0x9fba50ea, 0xea9fcfba
, 0x1b2d3f12, 0x121b242d, 0x9eb9a41d, 0x1d9e3ab9, 0x749cc458, 0x5874b09c, 0x2e724634, 0x342e6872, 0x2d774136, 0x362d6c77, 0xb2cd11dc, 0xdcb2a3cd, 0xee299db4, 0xb4ee7329, 0xfb164d5b, 0x5bfbb616
, 0xf601a5a4, 0xa4f65301, 0x4dd7a176, 0x764decd7, 0x61a314b7, 0xb76175a3, 0xce49347d, 0x7dcefa49, 0x7b8ddf52, 0x527ba48d, 0x3e429fdd, 0xdd3ea142, 0x7193cd5e, 0x5e71bc93, 0x97a2b113, 0x139726a2
, 0xf504a2a6, 0xa6f55704, 0x68b801b9, 0xb96869b8, 0x0, 0x0, 0x2c74b5c1, 0xc12c9974, 0x60a0e040, 0x406080a0, 0x1f21c2e3, 0xe31fdd21, 0xc8433a79, 0x79c8f243, 0xed2c9ab6, 0xb6ed772c
, 0xbed90dd4, 0xd4beb3d9, 0x46ca478d, 0x8d4601ca, 0xd9701767, 0x67d9ce70, 0x4bddaf72, 0x724be4dd, 0xde79ed94, 0x94de3379, 0xd467ff98, 0x98d42b67, 0xe82393b0, 0xb0e87b23, 0x4ade5b85, 0x854a11de
, 0x6bbd06bb, 0xbb6b6dbd, 0x2a7ebbc5, 0xc52a917e, 0xe5347b4f, 0x4fe59e34, 0x163ad7ed, 0xed16c13a, 0xc554d286, 0x86c51754, 0xd762f89a, 0x9ad72f62, 0x55ff9966, 0x6655ccff, 0x94a7b611, 0x119422a7
, 0xcf4ac08a, 0x8acf0f4a, 0x1030d9e9, 0xe910c930, 0x60a0e04, 0x406080a, 0x819866fe, 0xfe81e798, 0xf00baba0, 0xa0f05b0b, 0x44ccb478, 0x7844f0cc, 0xbad5f025, 0x25ba4ad5, 0xe33e754b, 0x4be3963e
, 0xf30eaca2, 0xa2f35f0e, 0xfe19445d, 0x5dfeba19, 0xc05bdb80, 0x80c01b5b, 0x8a858005, 0x58a0a85, 0xadecd33f, 0x3fad7eec, 0xbcdffe21, 0x21bc42df, 0x48d8a870, 0x7048e0d8, 0x40cfdf1, 0xf104f90c
, 0xdf7a1963, 0x63dfc67a, 0xc1582f77, 0x77c1ee58, 0x759f30af, 0xaf75459f, 0x63a5e742, 0x426384a5, 0x30507020, 0x20304050, 0x1a2ecbe5, 0xe51ad12e, 0xe12effd, 0xfd0ee112, 0x6db708bf, 0xbf6d65b7
, 0x4cd45581, 0x814c19d4, 0x143c2418, 0x1814303c, 0x355f7926, 0x26354c5f, 0x2f71b2c3, 0xc32f9d71, 0xe13886be, 0xbee16738, 0xa2fdc835, 0x35a26afd, 0xcc4fc788, 0x88cc0b4f, 0x394b652e, 0x2e395c4b
, 0x57f96a93, 0x93573df9, 0xf20d5855, 0x55f2aa0d, 0x829d61fc, 0xfc82e39d, 0x47c9b37a, 0x7a47f4c9, 0xacef27c8, 0xc8ac8bef, 0xe73288ba, 0xbae76f32, 0x2b7d4f32, 0x322b647d, 0x95a442e6, 0xe695d7a4
, 0xa0fb3bc0, 0xc0a09bfb, 0x98b3aa19, 0x199832b3, 0xd168f69e, 0x9ed12768, 0x7f8122a3, 0xa37f5d81, 0x66aaee44, 0x446688aa, 0x7e82d654, 0x547ea882, 0xabe6dd3b, 0x3bab76e6, 0x839e950b, 0xb83169e
, 0xca45c98c, 0x8cca0345, 0x297bbcc7, 0xc729957b, 0xd36e056b, 0x6bd3d66e, 0x3c446c28, 0x283c5044, 0x798b2ca7, 0xa779558b, 0xe23d81bc, 0xbce2633d, 0x1d273116, 0x161d2c27, 0x769a37ad, 0xad76419a
, 0x3b4d96db, 0xdb3bad4d, 0x56fa9e64, 0x6456c8fa, 0x4ed2a674, 0x744ee8d2, 0x1e223614, 0x141e2822, 0xdb76e492, 0x92db3f76, 0xa1e120c, 0xc0a181e, 0x6cb4fc48, 0x486c90b4, 0xe4378fb8, 0xb8e46b37
, 0x5de7789f, 0x9f5d25e7, 0x6eb20fbd, 0xbd6e61b2, 0xef2a6943, 0x43ef862a, 0xa6f135c4, 0xc4a693f1, 0xa8e3da39, 0x39a872e3, 0xa4f7c631, 0x31a462f7, 0x37598ad3, 0xd337bd59, 0x8b8674f2, 0xf28bff86
, 0x325683d5, 0xd532b156, 0x43c54e8b, 0x8b430dc5, 0x59eb856e, 0x6e59dceb, 0xb7c218da, 0xdab7afc2, 0x8c8f8e01, 0x18c028f, 0x64ac1db1, 0xb16479ac, 0xd26df19c, 0x9cd2236d, 0xe03b7249, 0x49e0923b
, 0xb4c71fd8, 0xd8b4abc7, 0xfa15b9ac, 0xacfa4315, 0x709faf3, 0xf307fd09, 0x256fa0cf, 0xcf25856f, 0xafea20ca, 0xcaaf8fea, 0x8e897df4, 0xf48ef389, 0xe9206747, 0x47e98e20, 0x18283810, 0x10182028
, 0xd5640b6f, 0x6fd5de64, 0x888373f0, 0xf088fb83, 0x6fb1fb4a, 0x4a6f94b1, 0x7296ca5c, 0x5c72b896, 0x246c5438, 0x3824706c, 0xf1085f57, 0x57f1ae08, 0xc7522173, 0x73c7e652, 0x51f36497, 0x975135f3
, 0x2365aecb, 0xcb238d65, 0x7c8425a1, 0xa17c5984, 0x9cbf57e8, 0xe89ccbbf, 0x21635d3e, 0x3e217c63, 0xdd7cea96, 0x96dd377c, 0xdc7f1e61, 0x61dcc27f, 0x86919c0d, 0xd861a91, 0x85949b0f, 0xf851e94
, 0x90ab4be0, 0xe090dbab, 0x42c6ba7c, 0x7c42f8c6, 0xc4572671, 0x71c4e257, 0xaae529cc, 0xccaa83e5, 0xd873e390, 0x90d83b73, 0x50f0906, 0x6050c0f, 0x103f4f7, 0xf701f503, 0x12362a1c, 0x1c123836
, 0xa3fe3cc2, 0xc2a39ffe, 0x5fe18b6a, 0x6a5fd4e1, 0xf910beae, 0xaef94710, 0xd06b0269, 0x69d0d26b, 0x91a8bf17, 0x17912ea8, 0x58e87199, 0x995829e8, 0x2769533a, 0x3a277469, 0xb9d0f727, 0x27b94ed0
, 0x384891d9, 0xd938a948, 0x1335deeb, 0xeb13cd35, 0xb3cee52b, 0x2bb356ce, 0x33557722, 0x22334455, 0xbbd604d2, 0xd2bbbfd6, 0x709039a9, 0xa9704990, 0x89808707, 0x7890e80, 0xa7f2c133, 0x33a766f2
, 0xb6c1ec2d, 0x2db65ac1, 0x22665a3c, 0x3c227866, 0x92adb815, 0x15922aad, 0x2060a9c9, 0xc9208960, 0x49db5c87, 0x874915db, 0xff1ab0aa, 0xaaff4f1a, 0x7888d850, 0x5078a088, 0x7a8e2ba5, 0xa57a518e
, 0x8f8a8903, 0x38f068a, 0xf8134a59, 0x59f8b213, 0x809b9209, 0x980129b, 0x1739231a, 0x1a173439, 0xda751065, 0x65daca75, 0x315384d7, 0xd731b553, 0xc651d584, 0x84c61351, 0xb8d303d0, 0xd0b8bbd3
, 0xc35edc82, 0x82c31f5e, 0xb0cbe229, 0x29b052cb, 0x7799c35a, 0x5a77b499, 0x11332d1e, 0x1e113c33, 0xcb463d7b, 0x7bcbf646, 0xfc1fb7a8, 0xa8fc4b1f, 0xd6610c6d, 0x6dd6da61, 0x3a4e622c, 0x2c3a584e};

#define SWAP32LE(x) ((uint32_t) (x))

#define ROTL32(v, n) ((((v)<<(n))|((v)>>(32-(n))))&li_32(ffffffff))

#define li_32(h) 0x##h##u
#define EXT_BYTE(var,n) ((uint8_t)((uint32_t)(var) >> (8*n)))
#define u32BIG(a) \
  ((ROTL32(a,8) & li_32(00FF00FF)) | \
   (ROTL32(a,24) & li_32(FF00FF00)))

#define ROTATE_COLUMN_DOWN(v1, v2, amount_bytes, temp_var) {temp_var = (v1<<(8*amount_bytes))|(v2>>(8*(4-amount_bytes))); \
    v2 = (v2<<(8*amount_bytes))|(v1>>(8*(4-amount_bytes))); \
    v1 = temp_var;}

#define COLUMN(x,y,i,c0,c1,c2,c3,c4,c5,c6,c7,tv1,tv2,tu,tl,t)				\
   tu = T[2*(uint32_t)x[4*c0+0]];			    \
   tl = T[2*(uint32_t)x[4*c0+0]+1];		    \
   tv1 = T[2*(uint32_t)x[4*c1+1]];			\
   tv2 = T[2*(uint32_t)x[4*c1+1]+1];			\
   ROTATE_COLUMN_DOWN(tv1,tv2,1,t)	\
   tu ^= tv1;						\
   tl ^= tv2;						\
   tv1 = T[2*(uint32_t)x[4*c2+2]];			\
   tv2 = T[2*(uint32_t)x[4*c2+2]+1];			\
   ROTATE_COLUMN_DOWN(tv1,tv2,2,t)	\
   tu ^= tv1;						\
   tl ^= tv2;   					\
   tv1 = T[2*(uint32_t)x[4*c3+3]];			\
   tv2 = T[2*(uint32_t)x[4*c3+3]+1];			\
   ROTATE_COLUMN_DOWN(tv1,tv2,3,t)	\
   tu ^= tv1;						\
   tl ^= tv2;						\
   tl ^= T[2*(uint32_t)x[4*c4+0]];			\
   tu ^= T[2*(uint32_t)x[4*c4+0]+1];			\
   tv1 = T[2*(uint32_t)x[4*c5+1]];			\
   tv2 = T[2*(uint32_t)x[4*c5+1]+1];			\
   ROTATE_COLUMN_DOWN(tv1,tv2,1,t)	\
   tl ^= tv1;						\
   tu ^= tv2;						\
   tv1 = T[2*(uint32_t)x[4*c6+2]];			\
   tv2 = T[2*(uint32_t)x[4*c6+2]+1];			\
   ROTATE_COLUMN_DOWN(tv1,tv2,2,t)	\
   tl ^= tv1;						\
   tu ^= tv2;   					\
   tv1 = T[2*(uint32_t)x[4*c7+3]];			\
   tv2 = T[2*(uint32_t)x[4*c7+3]+1];			\
   ROTATE_COLUMN_DOWN(tv1,tv2,3,t)	\
   tl ^= tv1;						\
   tu ^= tv2;						\
   y[i] = tu;						\
   y[i+1] = tl;

/* compute one round of P (short variants) */
static void RND512P(uint8_t *x, uint32_t *y, uint32_t r) {
  uint32_t temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp;
  uint32_t* x32 = (uint32_t*)x;
  x32[ 0] ^= SWAP32LE(0x00000000)^r;
  x32[ 2] ^= SWAP32LE(0x00000010)^r;
  x32[ 4] ^= SWAP32LE(0x00000020)^r;
  x32[ 6] ^= SWAP32LE(0x00000030)^r;
  x32[ 8] ^= SWAP32LE(0x00000040)^r;
  x32[10] ^= SWAP32LE(0x00000050)^r;
  x32[12] ^= SWAP32LE(0x00000060)^r;
  x32[14] ^= SWAP32LE(0x00000070)^r;
  COLUMN(x,y, 0,  0,  2,  4,  6,  9, 11, 13, 15, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
  COLUMN(x,y, 2,  2,  4,  6,  8, 11, 13, 15,  1, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
  COLUMN(x,y, 4,  4,  6,  8, 10, 13, 15,  1,  3, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
  COLUMN(x,y, 6,  6,  8, 10, 12, 15,  1,  3,  5, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
/*
  COLUMN(x,y, 8,  8, 10, 12, 14,  1,  3,  5,  7, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
  COLUMN(x,y,10, 10, 12, 14,  0,  3,  5,  7,  9, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
  COLUMN(x,y,12, 12, 14,  0,  2,  5,  7,  9, 11, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
  COLUMN(x,y,14, 14,  0,  2,  4,  7,  9, 11, 13, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
*/
}

/* compute one round of Q (short variants) */
static void RND512Q(uint8_t *x, uint32_t *y, uint32_t r) {
  uint32_t temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp;
  uint32_t* x32 = (uint32_t*)x;
  x32[ 0] = ~x32[ 0];
  x32[ 1] ^= SWAP32LE(0xffffffff)^r;
  x32[ 2] = ~x32[ 2];
  x32[ 3] ^= SWAP32LE(0xefffffff)^r;
  x32[ 4] = ~x32[ 4];
  x32[ 5] ^= SWAP32LE(0xdfffffff)^r;
  x32[ 6] = ~x32[ 6];
  x32[ 7] ^= SWAP32LE(0xcfffffff)^r;
  x32[ 8] = ~x32[ 8];
  x32[ 9] ^= SWAP32LE(0xbfffffff)^r;
  x32[10] = ~x32[10];
  x32[11] ^= SWAP32LE(0xafffffff)^r;
  x32[12] = ~x32[12];
  x32[13] ^= SWAP32LE(0x9fffffff)^r;
  x32[14] = ~x32[14];
  x32[15] ^= SWAP32LE(0x8fffffff)^r;

  COLUMN(x,y, 0,  2,  6, 10, 14,  1,  5,  9, 13, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
  COLUMN(x,y, 2,  4,  8, 12,  0,  3,  7, 11, 15, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
  COLUMN(x,y, 4,  6, 10, 14,  2,  5,  9, 13,  1, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
  COLUMN(x,y, 6,  8, 12,  0,  4,  7, 11, 15,  3, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
  /*
  COLUMN(x,y, 8, 10, 14,  2,  6,  9, 13,  1,  5, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
  COLUMN(x,y,10, 12,  0,  4,  8, 11, 15,  3,  7, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
  COLUMN(x,y,12, 14,  2,  6, 10, 13,  1,  5,  9, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
  COLUMN(x,y,14,  0,  4,  8, 12, 15,  3,  7, 11, temp_v1, temp_v2, temp_upper_value, temp_lower_value, temp);
  */
}

/* compute compression function (short variants) */
static void compress(uint32_t h[16], const uint32_t m[16]) {
  int i;
  uint32_t Ptmp[2*COLS512];
  uint32_t Qtmp[2*COLS512];
  uint32_t y[2*COLS512];
  uint32_t z[2*COLS512];

  for (i = 0; i < 2*COLS512; i++) {
    z[i] = m[i];
    Ptmp[i] = h[i]^m[i];
  }

  /* compute Q(m) */
  // Given z (message), modify y:
  RND512Q((uint8_t*)z, y, SWAP32LE(0x00000000));
  //RND512Q((uint8_t*)y, z, SWAP32LE(0x01000000));
  //RND512Q((uint8_t*)z, y, SWAP32LE(0x02000000));
  //RND512Q((uint8_t*)y, z, SWAP32LE(0x03000000));
  //RND512Q((uint8_t*)z, y, SWAP32LE(0x04000000));
  //RND512Q((uint8_t*)y, z, SWAP32LE(0x05000000));
  //RND512Q((uint8_t*)z, y, SWAP32LE(0x06000000));
  //RND512Q((uint8_t*)y, z, SWAP32LE(0x07000000));
  //RND512Q((uint8_t*)z, y, SWAP32LE(0x08000000));
  // Given y, modify Qtmp:
  RND512Q((uint8_t*)y, Qtmp, SWAP32LE(0x09000000));

  /* compute P(h+m) */
  // Modify Ptmp given y:
  RND512P((uint8_t*)Ptmp, y, SWAP32LE(0x00000000));
  /*
  RND512P((uint8_t*)y, z, SWAP32LE(0x00000001));
  RND512P((uint8_t*)z, y, SWAP32LE(0x00000002));
  RND512P((uint8_t*)y, z, SWAP32LE(0x00000003));
  RND512P((uint8_t*)z, y, SWAP32LE(0x00000004));
  RND512P((uint8_t*)y, z, SWAP32LE(0x00000005));
  RND512P((uint8_t*)z, y, SWAP32LE(0x00000006));
  RND512P((uint8_t*)y, z, SWAP32LE(0x00000007));
  RND512P((uint8_t*)z, y, SWAP32LE(0x00000008));
  */
  // Modify Ptmp given y:
  RND512P((uint8_t*)y, Ptmp, SWAP32LE(0x00000009));

  /* compute P(h+m) + Q(m) + h */
  for (i = 0; i < 2*COLS512; i++) {
    h[i] ^= Ptmp[i]^Qtmp[i];
  }
}

int main()
{
  /* some sizes (number of bytes) */
  int ROWS = 8;
  int SIZE512 = 64;
  int ROUNDS512 = 10;
  int HASH_BIT_LEN = 256;

  uint32_t input[16];
  uint32_t chaining[16];
  uint32_t output[8];
  uint32_t block_counter1,
  block_counter2;         /* message block counter(s) */
  unsigned char buffer[SIZE512];      /* data buffer */
  int buf_ptr;              /* data buffer pointer */
  int bits_in_last_byte;    /* no. of message bits in last byte of
		           data buffer */
  int j = 0;
  int i = 0;

  /* set other variables */
  buf_ptr = 0;
  block_counter1 = 0;
  block_counter2 = 0;
  bits_in_last_byte = 0;

  /* allocate memory for state and data buffer */
  for(i = 0; i < 16; i++)
  {
    chaining[i] = 0;
  }
  /* set initial value */
  chaining[15] = SWAP32LE(u32BIG((uint32_t)HASH_BIT_LEN));

  // input data
  /*
  for(size_t i = 0; i < 16; i++)
  {
    input[i] = 0;
  }
  */

  compress(chaining, input);

  // Test: zero-input
  //for (i = 0; i < 16; ++i)
  //  __CPROVER_assume(input[i] == 0x0);

   /* store hash result in output */
  for (j = 8; j < 16; j++) {
    output[j-8] = chaining[j];
    //printf("%#x\n", output[j-8]);
  }

  // Test: output on zero-input
  /*
  __CPROVER_assume(output[0] == 0x84592ca0);
  __CPROVER_assume(output[1] == 0xe57598cf);
  __CPROVER_assume(output[2] == 0x95440030);
  __CPROVER_assume(output[3] == 0xf8640c84);
  __CPROVER_assume(output[4] == 0x5b35297f);
  __CPROVER_assume(output[5] == 0x86f0cb5d);
  __CPROVER_assume(output[6] == 0xe47c01d6);
  __CPROVER_assume(output[7] == 0x40416a05);
  */

  // Zero output:
  for (j = 0; j < 8; j++) {
    __CPROVER_assume(output[j] == 0x0);
  }

  __CPROVER_assert(0,"test");
  return 0;
}
