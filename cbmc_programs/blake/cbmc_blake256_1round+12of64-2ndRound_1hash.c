#include <stdio.h>
#include <stdint.h>

#define U8TO32_BIG(p)                          \
  (((int)((p)[0]) << 24) | ((int)((p)[1]) << 16) |  \
   ((int)((p)[2]) <<  8) | ((int)((p)[3])      ))

void blake256_compress(uint32_t h[8], uint32_t s[4], uint32_t t[2], int buflen, int nullt, uint8_t buf[64], uint8_t block[64]) {
    uint32_t v[16], m[16], i;

#define ROT(x,n) (((x)<<(32-n))|( (x)>>(n)))
#define G(a,b,c,d,e)          \
  v[a] += (m[sigma[i][e]] ^ u256[sigma[i][e+1]]) + v[b]; \
  v[d] = ROT( v[d] ^ v[a],16);        \
  v[c] += v[d];           \
  v[b] = ROT( v[b] ^ v[c],12);        \
  v[a] += (m[sigma[i][e+1]] ^ u256[sigma[i][e]])+v[b]; \
  v[d] = ROT( v[d] ^ v[a], 8);        \
  v[c] += v[d];           \
  v[b] = ROT( v[b] ^ v[c], 7);

#define G2(a,b,c,d,e)          \
  v[a] += (m[sigma[i][e]] ^ u256[sigma[i][e+1]]) + v[b]; \
  v[d] = ROT( v[d] ^ v[a],16);        \
  v[c] += v[d];           \
  v[b] = ROT( v[b] ^ v[c],12);        \
  //v[a] += (m[sigma[i][e+1]] ^ u256[sigma[i][e]])+v[b]; \
  //v[d] = ROT( v[d] ^ v[a], 8);        \
  //v[c] += v[d];           \
  //v[b] = ROT( v[b] ^ v[c], 7);

    
    const uint32_t u256[16] =
    {
      0x243f6a88, 0x85a308d3, 0x13198a2e, 0x03707344,
      0xa4093822, 0x299f31d0, 0x082efa98, 0xec4e6c89,
      0x452821e6, 0x38d01377, 0xbe5466cf, 0x34e90c6c,
      0xc0ac29b7, 0xc97c50dd, 0x3f84d5b5, 0xb5470917
    };
    
    
    // задаём перестановки
    const uint8_t sigma[][16] =
    {
      { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 },
      {14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 },
      {11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4 },
      { 7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8 },
      { 9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13 },
      { 2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9 },
      {12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11 },
      {13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10 },
      { 6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5 },
      {10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13 , 0 },
      { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 },
      {14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 },
      {11, 8, 12, 0, 5, 2, 15, 1, 10, 14, 3, 6, 7, 1, 9, 4 },
      { 7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8 },
      { 9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13 },
      { 2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9 }
    };
    
    // входное значение и его длины

    for( i = 0; i < 16; ++i )  m[i] = U8TO32_BIG( block + i * 4 );

    for( i = 0; i < 8; ++i )  v[i] = h[i];

    v[ 8] = s[0] ^ u256[0];
    v[ 9] = s[1] ^ u256[1];
    v[10] = s[2] ^ u256[2];
    v[11] = s[3] ^ u256[3];
    v[12] = u256[4];
    v[13] = u256[5];
    v[14] = u256[6];
    v[15] = u256[7];

    /* don't xor t when the block is only padding */
    if (!nullt)
    {
      v[12] ^= t[0];
      v[13] ^= t[0];
      v[14] ^= t[1];
      v[15] ^= t[1];
    }

    for ( i = 0; i < 1; ++i )
    {
      /* column step */
        
      G( 0,  4,  8, 12,  0 );
      G( 1,  5,  9, 13,  2 );
      G( 2,  6, 10, 14,  4 );
      G( 3,  7, 11, 15,  6 );
         
      /* diagonal step */
      G( 0,  5, 10, 15,  8 );
      G( 1,  6, 11, 12, 10 );
      G( 2,  7,  8, 13, 12 );
      G( 3,  4,  9, 14, 14 );
    }
    
    
    G( 0,  4,  8, 12,  0 );
    G2( 1,  5,  9, 13,  2 );
    //G( 2,  6, 10, 14,  4 );
    //G( 3,  7, 11, 15,  6 );
     

    for( i = 0; i < 16; ++i )  h[i % 8] ^= v[i];
}

int main() {
    
    uint8_t in1[64];
    uint32_t h1[8];
    
    h1[0] = 0x6a09e667;
    h1[1] = 0xbb67ae85;
    h1[2] = 0x3c6ef372;
    h1[3] = 0xa54ff53a;
    h1[4] = 0x510e527f;
    h1[5] = 0x9b05688c;
    h1[6] = 0x1f83d9ab;
    h1[7] = 0x5be0cd19;
    
    uint32_t t1[2];
    int buflen1, nullpt1;
    uint32_t s1[4];
    uint8_t buf1[8];
    
    
    t1[0] = t1[1] = buflen1 = nullpt1 = 0;
    s1[0] = s1[1] = s1[2] = s1[3] = 0;
    
    blake256_compress(h1, s1, t1, buflen1, nullpt1, buf1, in1);
    
    /*
    printf("h0 : %#x\n", h1[0]);
    printf("h1 : %#x\n", h1[1]);
    printf("h2 : %#x\n", h1[2]);
    printf("h3 : %#x\n", h1[3]);
    printf("h4 : %#x\n", h1[4]);
    printf("h5 : %#x\n", h1[5]);
    printf("h6 : %#x\n", h1[6]);
    printf("h7 : %#x\n", h1[7]);
    */


    
    // test
    
    
   // for (int i = 0; i < 32; i++)
   //     __CPROVER_assume( in1[i] == 0 );
    /*
    __CPROVER_assume(h1[0] == 0x28bf9cd8); // 0: 0x28bf9cd8, 1: 0xca6e49b9
    __CPROVER_assume(h1[1] == 0x9ed786d0); // 0: 0x9ed786d0, 1: 0x54bf17e3
    __CPROVER_assume(h1[2] == 0xbd841ec0); // 0: 0xbd841ec0, 1: 0xce8a1ebe
    __CPROVER_assume(h1[3] == 0x48eaccf7); // 0: 0x48eaccf7, 1: 0xfc406458
    __CPROVER_assume(h1[4] == 0x56d1a50f); // 0: 0x56d1a50f, 1: 0x4fd62428
    __CPROVER_assume(h1[5] == 0x51651b7e); // 0: 0x51651b7e, 1: 0xefbc869f
    __CPROVER_assume(h1[6] == 0x3aea7bc0); // 0: 0x3aea7bc0, 1: 0x8958cda7
    __CPROVER_assume(h1[7] == 0x287bdc6c); // 0: 0x287bdc6c, 1: 0xaf7a82e1
    */
    
    // 1 hash
    for (int i = 0; i < 8; ++i)
        __CPROVER_assume(h1[i] == 0xffffffff);
    
    __CPROVER_assert(0,"test");
     
    
    return 0;
    


}
