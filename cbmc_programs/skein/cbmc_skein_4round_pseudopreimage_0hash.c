#include <stdint.h>
#include <limits.h>
#include <stddef.h>
#include <stdio.h>

/* macro to perform a key injection (same for all block sizes) */
#define InjectKey(r)                                                \
    for (i=0;i < WCNT;i++)                                          \
         X[i] += ks[((r)+i) % (WCNT+1)];                            \
    X[WCNT-3] += ts[((r)+0) % 3];                                   \
    X[WCNT-2] += ts[((r)+1) % 3];                                   \
    X[WCNT-1] += (r);

#define SKEIN_MK_64(hi32,lo32)  ((lo32) + (((uint64_t) (hi32)) << 32))
#define SKEIN_KS_PARITY         SKEIN_MK_64(0x1BD11BDA,0xA9FC1A22)

uint64_t RotL_64(uint64_t x, unsigned int N);
void Skein_Get64_LSB_First(uint64_t *dst, const uint8_t* src, size_t wCnt);
void Skein_Put64_LSB_First(uint8_t* dst, const uint64_t* src, size_t bCnt);
void Skein_512_Process_Block(uint64_t *ctxX, const uint8_t* msgBlkPtr, const size_t byteCntAdd);

int main(int argc, char** argv) {
    // Skein_512_Ctx_t structure:
    uint64_t ctxX[8];  // chaining variables 
    uint8_t msgBlkPtr[64];
    size_t byteCntAdd = 64;
    uint8_t hash[32]; // 256-bit hash since Skein-512-256
    size_t hashBytes = 32; // 256 bits == 32 bytes
    int i;
    /*
    // Zero message block:
    for (i = 0; i < byteCntAdd; i++) {
        msgBlkPtr[i] = 0;
    }
    */

    // 0-size buffer, 1 message block, 64 bytes 
    Skein_512_Process_Block(ctxX, msgBlkPtr, byteCntAdd);

    Skein_Put64_LSB_First(hash, ctxX, hashBytes);
    /*
    for (i = 0; i < hashValBytes; i++) {
        printf("%u", hashVal[i]);
        printf("\n");
    }
    */

    // 0-hash
    for (i = 0; i < hashBytes; i++)
        __CPROVER_assume(hash[i] == 0);

    __CPROVER_assert(0, "test");
    return 0;
}


/* 64-bit rotate left */
uint64_t RotL_64(uint64_t x, unsigned int N)
{
    return (x << (N & 63)) | (x >> ((64 - N) & 63));
}

void Skein_Get64_LSB_First(uint64_t *dst, const uint8_t* src, size_t wCnt)
{
    size_t n;

    for (n = 0; n < 8 * wCnt; n += 8)
        dst[n / 8] = (((uint64_t)src[n])) +
        (((uint64_t)src[n + 1]) << 8) +
        (((uint64_t)src[n + 2]) << 16) +
        (((uint64_t)src[n + 3]) << 24) +
        (((uint64_t)src[n + 4]) << 32) +
        (((uint64_t)src[n + 5]) << 40) +
        (((uint64_t)src[n + 6]) << 48) +
        (((uint64_t)src[n + 7]) << 56);
}

void Skein_Put64_LSB_First(uint8_t* dst, const uint64_t* src, size_t bCnt)
{
    size_t n;
    for (n = 0; n < bCnt; n++)
        dst[n] = (uint8_t)(src[n >> 3] >> (8 * (n & 7)));
}

void Skein_512_Process_Block(uint64_t *ctxX, const uint8_t* msgBlkPtr, const size_t byteCntAdd)
{
    int WCNT = 8; // WCNT = SKEIN_512_STATE_WORDS
    //int BLK_BITS = WCNT * 64;
    int SKEIN_512_ROUNDS_TOTAL = 72;

    size_t i, r;
    uint64_t ts[3];        /* key schedule: tweak */
    uint64_t ks[WCNT + 1]; /* key schedule: chaining vars */
    uint64_t X[WCNT];      /* local copy of vars */
    uint64_t w[WCNT];      /* local copy of input block */

    unsigned int R_512_0_0 = 46;
    unsigned int R_512_0_1 = 36;
    unsigned int R_512_0_2 = 19;
    unsigned int R_512_0_3 = 37;
    unsigned int R_512_1_0 = 33;
    unsigned int R_512_1_1 = 27;
    unsigned int R_512_1_2 = 14;
    unsigned int R_512_1_3 = 42;
    unsigned int R_512_2_0 = 17;
    unsigned int R_512_2_1 = 49;
    unsigned int R_512_2_2 = 36;
    unsigned int R_512_2_3 = 39;
    unsigned int R_512_3_0 = 44;
    unsigned int R_512_3_1 = 9;
    unsigned int R_512_3_2 = 54;
    unsigned int R_512_3_3 = 56;
    unsigned int R_512_4_0 = 39;
    unsigned int R_512_4_1 = 30;
    unsigned int R_512_4_2 = 34;
    unsigned int R_512_4_3 = 24;
    unsigned int R_512_5_0 = 13;
    unsigned int R_512_5_1 = 50;
    unsigned int R_512_5_2 = 10;
    unsigned int R_512_5_3 = 17;
    unsigned int R_512_6_0 = 25;
    unsigned int R_512_6_1 = 29;
    unsigned int R_512_6_2 = 39;
    unsigned int R_512_6_3 = 43;
    unsigned int R_512_7_0 = 8;
    unsigned int R_512_7_1 = 35;
    unsigned int R_512_7_2 = 56;
    unsigned int R_512_7_3 = 22;

    //T[0] += byteCntAdd;            /* update processed length */

    /* precompute the key schedule for this block */
    ks[WCNT] = SKEIN_KS_PARITY;
    for (i = 0; i < WCNT; i++)
    {
        ks[i] = ctxX[i];
        ks[WCNT] ^= ctxX[i];            /* compute overall parity */
    }
    //ts[0] = T[0];
    ts[0] = byteCntAdd; // mod: T[0] is byteCntAdd
    //ts[1] = T[1];
    ts[1] = 0; // mod: 0-flag T[1]
    ts[2] = ts[0] ^ ts[1];

    Skein_Get64_LSB_First(w, msgBlkPtr, WCNT); /* get input block in little-endian format */
    for (i = 0; i < WCNT; i++)               /* do the first full key injection */
    {
        X[i] = w[i] + ks[i];
    }
    X[WCNT - 3] += ts[0];
    X[WCNT - 2] += ts[1];

    /*
    // 9 iterations, 8 rounds each:
    for (r = 1; r <= SKEIN_512_ROUNDS_TOTAL / 8; r++)
    {
        // unroll 8 rounds
        X[0] += X[1]; X[1] = RotL_64(X[1], R_512_0_0); X[1] ^= X[0];
        X[2] += X[3]; X[3] = RotL_64(X[3], R_512_0_1); X[3] ^= X[2];
        X[4] += X[5]; X[5] = RotL_64(X[5], R_512_0_2); X[5] ^= X[4];
        X[6] += X[7]; X[7] = RotL_64(X[7], R_512_0_3); X[7] ^= X[6];

        X[2] += X[1]; X[1] = RotL_64(X[1], R_512_1_0); X[1] ^= X[2];
        X[4] += X[7]; X[7] = RotL_64(X[7], R_512_1_1); X[7] ^= X[4];
        X[6] += X[5]; X[5] = RotL_64(X[5], R_512_1_2); X[5] ^= X[6];
        X[0] += X[3]; X[3] = RotL_64(X[3], R_512_1_3); X[3] ^= X[0];

        X[4] += X[1]; X[1] = RotL_64(X[1], R_512_2_0); X[1] ^= X[4];
        X[6] += X[3]; X[3] = RotL_64(X[3], R_512_2_1); X[3] ^= X[6];
        X[0] += X[5]; X[5] = RotL_64(X[5], R_512_2_2); X[5] ^= X[0];
        X[2] += X[7]; X[7] = RotL_64(X[7], R_512_2_3); X[7] ^= X[2];

        X[6] += X[1]; X[1] = RotL_64(X[1], R_512_3_0); X[1] ^= X[6];
        X[0] += X[7]; X[7] = RotL_64(X[7], R_512_3_1); X[7] ^= X[0];
        X[2] += X[5]; X[5] = RotL_64(X[5], R_512_3_2); X[5] ^= X[2];
        X[4] += X[3]; X[3] = RotL_64(X[3], R_512_3_3); X[3] ^= X[4];
        InjectKey(2 * r - 1);

        X[0] += X[1]; X[1] = RotL_64(X[1], R_512_4_0); X[1] ^= X[0];
        X[2] += X[3]; X[3] = RotL_64(X[3], R_512_4_1); X[3] ^= X[2];
        X[4] += X[5]; X[5] = RotL_64(X[5], R_512_4_2); X[5] ^= X[4];
        X[6] += X[7]; X[7] = RotL_64(X[7], R_512_4_3); X[7] ^= X[6];

        X[2] += X[1]; X[1] = RotL_64(X[1], R_512_5_0); X[1] ^= X[2];
        X[4] += X[7]; X[7] = RotL_64(X[7], R_512_5_1); X[7] ^= X[4];
        X[6] += X[5]; X[5] = RotL_64(X[5], R_512_5_2); X[5] ^= X[6];
        X[0] += X[3]; X[3] = RotL_64(X[3], R_512_5_3); X[3] ^= X[0];

        X[4] += X[1]; X[1] = RotL_64(X[1], R_512_6_0); X[1] ^= X[4];
        X[6] += X[3]; X[3] = RotL_64(X[3], R_512_6_1); X[3] ^= X[6];
        X[0] += X[5]; X[5] = RotL_64(X[5], R_512_6_2); X[5] ^= X[0];
        X[2] += X[7]; X[7] = RotL_64(X[7], R_512_6_3); X[7] ^= X[2];

        X[6] += X[1]; X[1] = RotL_64(X[1], R_512_7_0); X[1] ^= X[6];
        X[0] += X[7]; X[7] = RotL_64(X[7], R_512_7_1); X[7] ^= X[0];
        X[2] += X[5]; X[5] = RotL_64(X[5], R_512_7_2); X[5] ^= X[2];
        X[4] += X[3]; X[3] = RotL_64(X[3], R_512_7_3); X[3] ^= X[4];
        InjectKey(2 * r);
    }
    */

    // First iteration, so r == 1
    r = 1;
    // 1st round:
    X[0] += X[1]; X[1] = RotL_64(X[1], R_512_0_0); X[1] ^= X[0];
    X[2] += X[3]; X[3] = RotL_64(X[3], R_512_0_1); X[3] ^= X[2];
    X[4] += X[5]; X[5] = RotL_64(X[5], R_512_0_2); X[5] ^= X[4];
    X[6] += X[7]; X[7] = RotL_64(X[7], R_512_0_3); X[7] ^= X[6];

    // 2nd round:
    X[2] += X[1]; X[1] = RotL_64(X[1], R_512_1_0); X[1] ^= X[2];
    X[4] += X[7]; X[7] = RotL_64(X[7], R_512_1_1); X[7] ^= X[4];
    X[6] += X[5]; X[5] = RotL_64(X[5], R_512_1_2); X[5] ^= X[6];
    X[0] += X[3]; X[3] = RotL_64(X[3], R_512_1_3); X[3] ^= X[0];

    // 3rd round:
    X[4] += X[1]; X[1] = RotL_64(X[1], R_512_2_0); X[1] ^= X[4];
    X[6] += X[3]; X[3] = RotL_64(X[3], R_512_2_1); X[3] ^= X[6];
    X[0] += X[5]; X[5] = RotL_64(X[5], R_512_2_2); X[5] ^= X[0];
    X[2] += X[7]; X[7] = RotL_64(X[7], R_512_2_3); X[7] ^= X[2];

    // 4th round:
    X[6] += X[1]; X[1] = RotL_64(X[1], R_512_3_0); X[1] ^= X[6];
    X[0] += X[7]; X[7] = RotL_64(X[7], R_512_3_1); X[7] ^= X[0];
    X[2] += X[5]; X[5] = RotL_64(X[5], R_512_3_2); X[5] ^= X[2];
    X[4] += X[3]; X[3] = RotL_64(X[3], R_512_3_3); X[3] ^= X[4];
    InjectKey(2 * r - 1);
/*    
    // 5th round:
    X[0] += X[1]; X[1] = RotL_64(X[1], R_512_4_0); X[1] ^= X[0];
    X[2] += X[3]; X[3] = RotL_64(X[3], R_512_4_1); X[3] ^= X[2];
    X[4] += X[5]; X[5] = RotL_64(X[5], R_512_4_2); X[5] ^= X[4];
    X[6] += X[7]; X[7] = RotL_64(X[7], R_512_4_3); X[7] ^= X[6];

    // 6th round:
    X[2] += X[1]; X[1] = RotL_64(X[1], R_512_5_0); X[1] ^= X[2];
    X[4] += X[7]; X[7] = RotL_64(X[7], R_512_5_1); X[7] ^= X[4];
    X[6] += X[5]; X[5] = RotL_64(X[5], R_512_5_2); X[5] ^= X[6];
    X[0] += X[3]; X[3] = RotL_64(X[3], R_512_5_3); X[3] ^= X[0];

    // 7th round:
    X[4] += X[1]; X[1] = RotL_64(X[1], R_512_6_0); X[1] ^= X[4];
    X[6] += X[3]; X[3] = RotL_64(X[3], R_512_6_1); X[3] ^= X[6];
    X[0] += X[5]; X[5] = RotL_64(X[5], R_512_6_2); X[5] ^= X[0];
    X[2] += X[7]; X[7] = RotL_64(X[7], R_512_6_3); X[7] ^= X[2];
    
    // 8th round:
    X[6] += X[1]; X[1] = RotL_64(X[1], R_512_7_0); X[1] ^= X[6];
    X[0] += X[7]; X[7] = RotL_64(X[7], R_512_7_1); X[7] ^= X[0];
    X[2] += X[5]; X[5] = RotL_64(X[5], R_512_7_2); X[5] ^= X[2];
    X[4] += X[3]; X[3] = RotL_64(X[3], R_512_7_3); X[3] ^= X[4];
    InjectKey(2 * r);
*/
    /* do the final "feedforward" xor, update context chaining vars */
    for (i = 0; i < WCNT; i++)
        ctxX[i] = X[i] ^ w[i];
}
