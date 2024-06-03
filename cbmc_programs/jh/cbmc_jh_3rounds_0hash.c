/* 
   A CBMC implementation of JH-256's compression function that
   generates a 256-bit hash.
   Author: Dr. Oleg Zaikin, ISDCT SB RAS

   Based on the following reference implementation of JH taken from
   https://www3.ntu.edu.sg/home/wuhj/research/jh/jh_ref.h

   Last modified: 29 Nov 2023

   --------------------------------

   This program gives the reference implementation of JH.
   It implements the standard description of JH (not bitslice)
   The description given in this program is suitable for hardware 
   implementation

   Comparing to the original reference implementation,
   two functions are added to make the porgram more readable.
   One function is E8_initialgroup() at the beginning of E8;
   another function is E8_finaldegroup() at the end of E8.

   Last Modified: January 16, 2011
*/

#include <string.h>

/*
typedef struct {
      int hashbitlen;                     // the hash size in bits
      unsigned long long databitlen;      // the message size in bits
      unsigned long long datasize_in_buffer; // the size of the message remained in buffer; assumed to be multiple of 8bits except for the last partial block at the end of the message
      unsigned char H[128];               // the hash value H; 1024 bits (finally is truncated to 256 bits)
      unsigned char A[256];               // the temporary round value; 256 4-bit elements
      unsigned char roundconstant[64];    // round constant for one round; 64 4-bit elements
      unsigned char buffer[64];           // the message block to be hashed; 64 bytes
} hashState;
*/

/*The constant for the Round 0 of E8*/
const unsigned char roundconstant_zero[64] = {0x6,0xa,0x0,0x9,0xe,0x6,0x6,0x7,0xf,0x3,0xb,0xc,0xc,0x9,0x0,0x8,0xb,0x2,0xf,0xb,0x1,0x3,0x6,0x6,0xe,0xa,0x9,0x5,0x7,0xd,0x3,0xe,0x3,0xa,0xd,0xe,0xc,0x1,0x7,0x5,0x1,0x2,0x7,0x7,0x5,0x0,0x9,0x9,0xd,0xa,0x2,0xf,0x5,0x9,0x0,0xb,0x0,0x6,0x6,0x7,0x3,0x2,0x2,0xa};

/*The two Sboxes S0 and S1*/
unsigned char S[2][16] = {{9,0,4,11,13,12,3,15,1,10,2,6,7,5,8,14},{3,12,6,13,5,7,1,9,15,2,0,4,11,10,14,8}};

/*The linear transformation L, the MDS code*/
#define L(a, b) {                                                       \
      (b) ^= ( ( (a) << 1) ^ ( (a) >> 3) ^ (( (a) >> 2) & 2) ) & 0xf;   \
      (a) ^= ( ( (b) << 1) ^ ( (b) >> 3) ^ (( (b) >> 2) & 2) ) & 0xf;   \
}

void R8(unsigned char* roundconstant,
        unsigned char* A);                    /* The round function of E8 */
void update_roundconstant(unsigned char* roundconstant); /* Update the round constant of E8 */
void E8_initialgroup(unsigned char* H, 
                     unsigned char* A);       /* Grouping the state into 4-bit elements at the beginning of E8 */
void E8_finaldegroup(unsigned char* H,
                     unsigned char* A);       /* Inverse of the grouping at the end of E8 */
void E8(unsigned char* H, unsigned char* roundconstant,
        unsigned char* A, const unsigned rounds); /* The bijective function E8 */
void F8(unsigned char* H, unsigned char* buffer, unsigned char* roundconstant,
        unsigned char* A, const unsigned rounds); /* The compression function F8 */

/*The API functions*/
//void Init(const int hashbitlen, unsigned char* H, unsigned char* buffer,
//          unsigned char* roundconstant, unsigned char* A, 
//          const unsigned rounds);
//HashReturn Update(hashState *state, const unsigned char *data, unsigned long long databitlen);
// HashReturn Final(hashState *state, unsigned char *hashval);
//HashReturn Hash(int hashbitlen, const unsigned char *data,unsigned long long databitlen, unsigned char *hashval);

/*the round function of E8 */
void R8(unsigned char* roundconstant, unsigned char* A)
{
      unsigned int i;
      unsigned char tem[256],t;
      unsigned char roundconstant_expanded[256];  /*the round constant expanded into 256 1-bit element;*/

      /*expand the round constant into 256 one-bit element*/
      for (i = 0; i < 256; i++)  {
            roundconstant_expanded[i] = (roundconstant[i >> 2] >> (3 - (i & 3)) ) & 1;
      }

      /*S box layer, each constant bit selects one Sbox from S0 and S1*/
      for (i = 0; i < 256; i++) {
            tem[i] = S[roundconstant_expanded[i]][A[i]]; /*constant bits are used to determine which Sbox to use*/
      }

      /*MDS Layer*/
      for (i = 0; i < 256; i=i+2) L(tem[i], tem[i+1]);

      /*The following is the permuation layer P_8$

      /*initial swap Pi_8*/
      for ( i = 0; i < 256; i=i+4) {
            t = tem[i+2];
            tem[i+2] = tem[i+3];
            tem[i+3] = t;
      }

      /*permutation P'_8*/
      for (i = 0; i < 128; i=i+1) {
            A[i] = tem[i<<1];
            A[i+128] = tem[(i<<1)+1];
      }

      /*final swap Phi_8*/
      for ( i = 128; i < 256; i=i+2) {
            t = A[i];
            A[i] = A[i+1];
            A[i+1] = t;
      }
}


/*The following function generates the next round constant from the current
  round constant;  R6 is used for generating round constants for E8, with
  the round constants of R6 being set as 0;
*/
void update_roundconstant(unsigned char* roundconstant) {
      int i;
      unsigned char tem[64],t;

      /*Sbox layer*/
      for (i = 0; i < 64; i++)   tem[i] = S[0][roundconstant[i]];

      /*MDS layer*/
      for (i = 0; i < 64; i=i+2) L(tem[i], tem[i+1]);

      /*The following is the permutation layer P_6 */

      /*initial swap Pi_6*/
      for ( i = 0; i < 64; i=i+4) {
            t = tem[i+2];
            tem[i+2] = tem[i+3];
            tem[i+3] = t;
      }

      /*permutation P'_6*/
      for ( i = 0; i < 32; i=i+1) {
            roundconstant[i]    = tem[i<<1];
            roundconstant[i+32] = tem[(i<<1)+1];
      }

      /*final swap Phi_6*/
      for ( i = 32; i < 64; i=i+2 ) {
            t = roundconstant[i];
            roundconstant[i] = roundconstant[i+1];
            roundconstant[i+1] = t;
      }
}

/*initial group at the begining of E_8: group the bits of H into 4-bit elements of A.
  After the grouping, the i-th, (i+256)-th, (i+512)-th, (i+768)-th bits of state->H
  become the i-th 4-bit element of state->A
*/
void E8_initialgroup(unsigned char* H, unsigned char* A) {
      unsigned int i;
      unsigned char t0,t1,t2,t3;
      unsigned char tem[256];

      /*t0 is the i-th bit of H, i = 0, 1, 2, 3, ... , 127*/
      /*t1 is the (i+256)-th bit of H*/
      /*t2 is the (i+512)-th bit of H*/
      /*t3 is the (i+768)-th bit of H*/
      for (i = 0; i < 256; i++) {
            t0 = (H[i>>3] >> (7 - (i & 7)) ) & 1;
            t1 = (H[(i+256)>>3] >> (7 - (i & 7)) ) & 1;
            t2 = (H[(i+ 512 )>>3] >> (7 - (i & 7)) ) & 1;
            t3 = (H[(i+ 768 )>>3] >> (7 - (i & 7)) ) & 1;
            tem[i] = (t0 << 3) | (t1 << 2) | (t2 << 1) | (t3 << 0);
      }
      /*padding the odd-th elements and even-th elements separately*/
      for (i = 0; i < 128; i++) {
            A[i << 1] = tem[i];
            A[(i << 1)+1] = tem[i+128];
      }
}

/*de-group at the end of E_8:  it is the inverse of E8_initialgroup
  The 256 4-bit elements in state->A are degouped into the 1024-bit state->H
*/
void E8_finaldegroup(unsigned char* H, unsigned char* A) {
      unsigned int i;
      unsigned char t0,t1,t2,t3;
      unsigned char tem[256];

      for (i = 0; i < 128; i++) {
            tem[i] = A[i << 1];
            tem[i+128] = A[(i << 1)+1];
      }

      for (i = 0; i < 128; i++) H[i] = 0;

      for (i = 0; i < 256; i++) {
            t0 = (tem[i] >> 3) & 1;
            t1 = (tem[i] >> 2) & 1;
            t2 = (tem[i] >> 1) & 1;
            t3 = (tem[i] >> 0) & 1;

            H[i>>3] |= t0 << (7 - (i & 7));
            H[(i + 256)>>3] |= t1 << (7 - (i & 7));
            H[(i + 512)>>3] |= t2 << (7 - (i & 7));
            H[(i + 768)>>3] |= t3 << (7 - (i & 7));
      }
}

/*bijective function E8 */
void E8(unsigned char* H, unsigned char* roundconstant, 
        unsigned char* A, const unsigned rounds)
{
      unsigned int i;
      unsigned char t0,t1,t2,t3;
      unsigned char tem[256];

      /*initialize the round constant*/
      for (i = 0; i < 64; i++) roundconstant[i] = roundconstant_zero[i];

      /*initial group at the begining of E_8: group the H value into 4-bit elements and store them in A */
      E8_initialgroup(H, A);

      // A loop over rounds:
      for (i = 0; i < rounds; i++) {
            R8(roundconstant, A);
            update_roundconstant(roundconstant);
      }

      /*de-group at the end of E_8:  decompose the 4-bit elements of A into the 1024-bit H*/
      E8_finaldegroup(H, A);
}

/* compression function F8 */
void F8(unsigned char* H, unsigned char* buffer, unsigned char* roundconstant, 
        unsigned char* A, const unsigned rounds)
{
      unsigned int i;

      /*xor the message with the first half of H*/
      for (i = 0; i < 64; i++) H[i] ^= buffer[i];

      /* Bijective function E8 */
      E8(H, roundconstant, A, rounds);

      /* xor the message with the last half of H */
      for (i = 0; i < 64; i++) H[i+64] ^= buffer[i];
}

/*
// before hashing a message, initialize the hash state as H0
void Init(const int hashbitlen, unsigned char* H, unsigned char* buffer,
          unsigned char* roundconstant, unsigned char* A,
          const unsigned rounds)
{
      unsigned int i;

      for (i = 0; i < 64; i++) buffer[i] = 0;
      for (i = 0; i < 128; i++) H[i] = 0;

      // initialize the initial hash value of JH
      // step 1: set H(-1) to the message digest size
      H[1] = hashbitlen & 0xff;
      H[0] = (hashbitlen >> 8) & 0xff;
	  //step 2: compute H0 from H(-1) with message M(0) being set as 0
      F8(H, buffer, roundconstant, A, rounds);
}
*/

int main(int argc, char **argv)
{
    int hashbitlen = 256;               // the hash size in bits
    int hashBytelen = 32;               // the hash size in bytes
    unsigned char hashval[32];          // the hash; 256 bits
    unsigned char buffer[64];           // the message block to be hashed; 64 bytes
    unsigned char H[128];               // the hash value H; 1024 bits (finally is truncated to 256 bits)
    unsigned char A[256];               // the temporary round value; 256 4-bit elements
    unsigned char roundconstant[64];    // round constant for one round; 64 4-bit elements
    unsigned i = 0;
    unsigned rounds = 3;

    // Test:
    /*
    for (i=0; i<64; i++) {
        buffer[i] = 0;
    }
    */

    // Initialize:
    // Init(hashbitlen, H, buffer, roundconstant, A, rounds);
    /*initialize the initial hash value of JH*/
    /*step 1: set H(-1) to the hash size*/
    for (i = 0; i < 128; i++) H[i] = 0;
    H[1] = hashbitlen & 0xff;
    H[0] = (hashbitlen >> 8) & 0xff;

    // Call the compression function:
    F8(H, buffer, roundconstant, A, rounds);

    // Truncate H to get hash:
    // From Final(), case 256:  memcpy(hashval,state->H+96, 32);  break;
    for (i = 0; i < hashBytelen; i++) {
        hashval[i] = H[96 + i];
    }

    // Zero hash:
    for (i = 0; i < hashBytelen; i++)
    {
        __CPROVER_assume(hashval[i] == 0);
    }

    __CPROVER_assert(0, "test");

    return 0;
}
