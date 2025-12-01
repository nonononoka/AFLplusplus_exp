#ifndef _COVERAGE_H

#define _COVERAGE_H

#include "config.h"
#include "types.h"

#define _AFL_INTSIZEVAR u64

#if (defined(__AVX512F__) && defined(__AVX512DQ__)) || defined(__AVX2__)
  #include <immintrin.h>
#endif

u32 skim(const u64 *virgin, const u64 *current, const u64 *current_end);
u64 classify_word(u64 word);

inline u64 classify_word(u64 word) {

  u16 mem16[4];
  memcpy(mem16, &word, sizeof(mem16));

  mem16[0] = count_class_lookup16[mem16[0]];
  mem16[1] = count_class_lookup16[mem16[1]];
  mem16[2] = count_class_lookup16[mem16[2]];
  mem16[3] = count_class_lookup16[mem16[3]];

  memcpy(&word, mem16, sizeof(mem16));
  return word;

}

void simplify_trace(afl_state_t *afl, u8 *bytes) {

  u64 *mem = (u64 *)bytes;
  u32  i = (afl->fsrv.map_size >> 3);

  while (i--) {

    /* Optimize for sparse bitmaps. */

    if (unlikely(*mem)) {

      u8 *mem8 = (u8 *)mem;

      mem8[0] = simplify_lookup[mem8[0]];
      mem8[1] = simplify_lookup[mem8[1]];
      mem8[2] = simplify_lookup[mem8[2]];
      mem8[3] = simplify_lookup[mem8[3]];
      mem8[4] = simplify_lookup[mem8[4]];
      mem8[5] = simplify_lookup[mem8[5]];
      mem8[6] = simplify_lookup[mem8[6]];
      mem8[7] = simplify_lookup[mem8[7]];

    } else

      *mem = 0x0101010101010101ULL;

    mem++;

  }

}

inline void classify_counts(afl_forkserver_t *fsrv) {

  u64 *mem = (u64 *)fsrv->trace_bits;
  u32  i = (fsrv->map_size >> 3);

  while (i--) {

    /* Optimize for sparse bitmaps. */

    if (unlikely(*mem)) { *mem = classify_word(*mem); }

    mem++;

  }

}

/* Updates the virgin bits, then reflects whether a new count or a new tuple is
 * seen in ret. */
inline void discover_word(u8 *ret, u64 *current, u64 *virgin) {
  /* Optimize for (*current & *virgin) == 0 - i.e., no bits in current bitmap
     that have not been already cleared from the virgin map - since this will
     almost always be the case. */

  if (*current & *virgin) {

    if (likely(*ret < 2)) {

      u8 *cur = (u8 *)current;
      u8 *vir = (u8 *)virgin;

      /* Looks like we have not found any new bytes yet; see if any non-zero
         bytes in current[] are pristine in virgin[]. */

      if ((cur[0] && vir[0] == 0xff) || (cur[1] && vir[1] == 0xff) ||
          (cur[2] && vir[2] == 0xff) || (cur[3] && vir[3] == 0xff) ||
          (cur[4] && vir[4] == 0xff) || (cur[5] && vir[5] == 0xff) ||
          (cur[6] && vir[6] == 0xff) || (cur[7] && vir[7] == 0xff))
        *ret = 2;
      else
        *ret = 1;

    }

    *virgin &= ~*current;

  }

}

/* Updates the virgin bits, then reflects whether a new count or a new tuple is
 * seen in ret. */
// 31までの回数までのところだけ回数変化として加える
inline void discover_word_until_31_count_for_log(u8 *ret, u64 *current, u64 *virgin, int j) {

  /* Optimize for (*current & *virgin) == 0 - i.e., no bits in current bitmap
     that have not been already cleared from the virgin map - since this will
     almost always be the case. */

  if (*current & *virgin) {

    // if (likely(*ret < 2)) {

      u8 *cur = (u8 *)current;
      u8 *vir = (u8 *)virgin;

      if ((cur[0]&vir[0]) && cur[0] < 8) {
        if(vir[0] == 0xff){*ret = 2; ACTF("new edge found: %u %u", 8*j, cur[0]);}
        else if(*ret == 0){*ret = 1; ACTF("count differ: %u %u", 8*j, cur[0]);}
        vir[0] &= ~cur[0];
      }
      if ((cur[1]&vir[1]) && cur[1] < 8) {
        if(vir[1] == 0xff){*ret = 2; ACTF("new edge found: %u %u", 8*j+1, cur[1]);}
        else if(*ret == 0){*ret = 1; ACTF("count differ: %u %u", 8*j+1, cur[1]);}
        vir[1] &= ~cur[1];
        ACTF("count differ: %u %u", 8*j+1, cur[1]);
      }
      if ((cur[2]&vir[2]) && cur[2] < 8) {
        if(vir[2] == 0xff){*ret = 2; ACTF("new edge found: %u %u", 8*j+2, cur[2]);}
        else if(*ret == 0){*ret = 1; ACTF("count differ: %u %u", 8*j+2, cur[2]);}
        vir[2] &= ~cur[2];
        ACTF("count differ: %u %u", 8*j+2, cur[2]);
      }
      if ((cur[3]&vir[3]) && cur[3] < 8) {
        if(vir[3] == 0xff){*ret = 2; ACTF("new edge found: %u %u", 8*j+3, cur[3]);}
        else if(*ret == 0){*ret = 1; ACTF("count differ: %u %u", 8*j+3, cur[3]);}
        vir[3] &= ~cur[3];
        ACTF("count differ: %u %u", 8*j+3, cur[3]);
      }
      if ((cur[4]&vir[4]) && cur[4] < 8) {
        if(vir[4] == 0xff){*ret = 2; ACTF("new edge found: %u %u", 8*j+4, cur[4]);}
        else if(*ret == 0){*ret = 1; ACTF("count differ: %u %u", 8*j+4, cur[4]);}
        vir[4] &= ~cur[4];
        ACTF("count differ: %u %u", 8*j+4, cur[4]);
      }
      if ((cur[5]&vir[5]) && cur[5] < 8) {
        if(vir[5] == 0xff){*ret = 2; ACTF("new edge found: %u %u", 8*j+5, cur[5]);}
        else if(*ret == 0){*ret = 1; ACTF("count differ: %u %u", 8*j+5, cur[5]);}
        vir[5] &= ~cur[5];
      }
      if ((cur[6]&vir[6]) && cur[6] < 8) {
        if(vir[6] == 0xff){*ret = 2; ACTF("new edge found: %u %u", 8*j+6, cur[6]);}
        else if(*ret == 0){*ret = 1; ACTF("count differ: %u %u", 8*j+6, cur[6]);}
        vir[6] &= ~cur[6];
      }
      if ((cur[7]&vir[7]) && cur[7] < 8) {
       if(vir[7] == 0xff){*ret = 2; ACTF("new edge found: %u %u", 8*j+7, cur[7]);}
       else if(*ret == 0){*ret = 1; ACTF("count differ: %u %u", 8*j+7, cur[7]);}
        vir[7] &= ~cur[7];
      }

    // }

  }

}

/* Updates the virgin bits, then reflects whether a new count or a new tuple is
 * seen in ret. */
// 31までの回数までのところだけ回数変化として加える
inline void discover_word_until_31_count(u8 *ret, u64 *current, u64 *virgin) {

  /* Optimize for (*current & *virgin) == 0 - i.e., no bits in current bitmap
     that have not been already cleared from the virgin map - since this will
     almost always be the case. */

  if (*current & *virgin) {

    // if (likely(*ret < 2)) {

      u8 *cur = (u8 *)current;
      u8 *vir = (u8 *)virgin;

      if ((cur[0]&vir[0])) {
        if(vir[0] == 0xff){*ret = 2;}
        else if(*ret == 0){*ret = 1;}
        vir[0] &= ~cur[0];
      }
      if ((cur[1]&vir[1])) {
        if(vir[1] == 0xff){*ret = 2;}
        else if(*ret == 0){*ret = 1;}
        vir[1] &= ~cur[1];
      }
      if ((cur[2]&vir[2])) {
        if(vir[2] == 0xff){*ret = 2;}
        else if(*ret == 0){*ret = 1;}
        vir[2] &= ~cur[2];
      }
      if ((cur[3]&vir[3])) {
        if(vir[3] == 0xff){*ret = 2;}
        else if(*ret == 0){*ret = 1;}
        vir[3] &= ~cur[3];
      }
      if ((cur[4]&vir[4])) {
        if(vir[4] == 0xff){*ret = 2;}
        else if(*ret == 0){*ret = 1;}
        vir[4] &= ~cur[4];
      }
      if ((cur[5]&vir[5])) {
        if(vir[5] == 0xff){*ret = 2;}
        else if(*ret == 0){*ret = 1;}
        vir[5] &= ~cur[5];
      }
      if ((cur[6]&vir[6])) {
        if(vir[6] == 0xff){*ret = 2;}
        else if(*ret == 0){*ret = 1;}
        vir[6] &= ~cur[6];
      }
      if ((cur[7]&vir[7])) {
       if(vir[7] == 0xff){*ret = 2;}
       else if(*ret == 0){*ret = 1;}
        vir[7] &= ~cur[7];
      }

    // }

  }

}

/* Updates the virgin bits, then reflects whether a new count or a new tuple is
 * seen in ret. */
// 新しいエッジがビットを立てたところだけ、ビットを更新したい
// 新規エッジが立ったところだけビットを埋める
// この場合返すのは、0か2のみ
inline void discover_word_only_new_edge(u8 *ret, u64 *current, u64 *virgin) {

  /* Optimize for (*current & *virgin) == 0 - i.e., no bits in current bitmap
     that have not been already cleared from the virgin map - since this will
     almost always be the case. */

  if (*current & *virgin) {

    // if (likely(*ret < 2)) {

      u8 *cur = (u8 *)current;
      u8 *vir = (u8 *)virgin;

      /* Looks like we have not found any new bytes yet; see if any non-zero
         bytes in current[] are pristine in virgin[]. */
      if (cur[0] && vir[0] == 0xff) {
        *ret = 2;
        vir[0] &= ~cur[0];
      }
      if (cur[1] && vir[1] == 0xff) {
        *ret = 2;
        vir[1] &= ~cur[1];
      }
      if (cur[2] && vir[2] == 0xff) {
        *ret = 2;
        vir[2] &= ~cur[2];
      }
      if (cur[3] && vir[3] == 0xff) {
        *ret = 2;
        vir[3] &= ~cur[3];
      }
      if (cur[4] && vir[4] == 0xff) {
        *ret = 2;
        vir[4] &= ~cur[4];
      }
      if (cur[5] && vir[5] == 0xff) {
        *ret = 2;
        vir[5] &= ~cur[5];
      }
      if (cur[6] && vir[6] == 0xff) {
        *ret = 2;
        vir[6] &= ~cur[6];
      }
      if (cur[7] && vir[7] == 0xff) {
        *ret = 2;
        vir[7] &= ~cur[7];
      }

    // }

  }

}

/* Updates the virgin bits, then reflects whether a new count or a new tuple is
 * seen in ret. */
// 新しいエッジがビットを立てたところだけ、ビットを更新したい
// 新規エッジが立ったところだけビットを埋める
// この場合返すのは、0か2のみ
inline void discover_word_only_new_edge_for_log(u8 *ret, u64 *current, u64 *virgin, int j) {

  /* Optimize for (*current & *virgin) == 0 - i.e., no bits in current bitmap
     that have not been already cleared from the virgin map - since this will
     almost always be the case. */

  if (*current & *virgin) {

    // if (likely(*ret < 2)) {

      u8 *cur = (u8 *)current;
      u8 *vir = (u8 *)virgin;

      /* Looks like we have not found any new bytes yet; see if any non-zero
         bytes in current[] are pristine in virgin[]. */
      if (cur[0] && vir[0] == 0xff) {
        *ret = 2;
        vir[0] &= ~cur[0];
        ACTF("new edge found: %u %u", 8*j, cur[0]);
      }
      if (cur[1] && vir[1] == 0xff) {
        *ret = 2;
        vir[1] &= ~cur[1];
        ACTF("new edge found: %u %u", 8*j+1, cur[1]);
      }
      if (cur[2] && vir[2] == 0xff) {
        *ret = 2;
        vir[2] &= ~cur[2];
        ACTF("new edge found: %u %u", 8*j+2, cur[2]);
      }
      if (cur[3] && vir[3] == 0xff) {
        *ret = 2;
        vir[3] &= ~cur[3];
        ACTF("new edge found: %u %u", 8*j+3, cur[3]);
      }
      if (cur[4] && vir[4] == 0xff) {
        *ret = 2;
        vir[4] &= ~cur[4];
        ACTF("new edge found: %u %u", 8*j+4, cur[4]);
      }
      if (cur[5] && vir[5] == 0xff) {
        *ret = 2;
        vir[5] &= ~cur[5];
        ACTF("new edge found: %u %u", 8*j+5, cur[5]);
      }
      if (cur[6] && vir[6] == 0xff) {
        *ret = 2;
        vir[6] &= ~cur[6];
        ACTF("new edge found: %u %u", 8*j+6, cur[6]);
      }
      if (cur[7] && vir[7] == 0xff) {
        *ret = 2;
        vir[7] &= ~cur[7];
        ACTF("new edge found: %u %u", 8*j+7, cur[7]);
      }

    // }

  }

}

#if defined(__AVX512F__) && defined(__AVX512DQ__)
  #define PACK_SIZE 64
inline u32 skim(const u64 *virgin, const u64 *current, const u64 *current_end) {

  for (; current != current_end; virgin += 8, current += 8) {

    __m512i  value = *(__m512i *)current;
    __mmask8 mask = _mm512_testn_epi64_mask(value, value);

    /* All bytes are zero. */
    if (likely(mask == 0xff)) continue;

        /* Look for nonzero bytes and check for new bits. */
  #define UNROLL(x)                                                            \
    if (unlikely(!(mask & (1 << x)) && classify_word(current[x]) & virgin[x])) \
    return 1
    UNROLL(0);
    UNROLL(1);
    UNROLL(2);
    UNROLL(3);
    UNROLL(4);
    UNROLL(5);
    UNROLL(6);
    UNROLL(7);
  #undef UNROLL

  }

  return 0;

}

#endif

#if !defined(PACK_SIZE) && defined(__AVX2__)
  #define PACK_SIZE 32
inline u32 skim(const u64 *virgin, const u64 *current, const u64 *current_end) {

  __m256i zeroes = _mm256_setzero_si256();

  for (; current < current_end; virgin += 4, current += 4) {

    __m256i value = *(__m256i *)current;
    __m256i cmp = _mm256_cmpeq_epi64(value, zeroes);
    u32     mask = _mm256_movemask_epi8(cmp);

    /* All bytes are zero. */
    if (likely(mask == (u32)-1)) continue;

    /* Look for nonzero bytes and check for new bits. */
    if (unlikely(!(mask & 0xff) && classify_word(current[0]) & virgin[0]))
      return 1;
    if (unlikely(!(mask & 0xff00) && classify_word(current[1]) & virgin[1]))
      return 1;
    if (unlikely(!(mask & 0xff0000) && classify_word(current[2]) & virgin[2]))
      return 1;
    if (unlikely(!(mask & 0xff000000) && classify_word(current[3]) & virgin[3]))
      return 1;

  }

  return 0;

}

#endif

#if !defined(PACK_SIZE)
  #define PACK_SIZE 32
inline u32 skim(const u64 *virgin, const u64 *current, const u64 *current_end) {

  for (; current < current_end; virgin += 4, current += 4) {

    if (unlikely(current[0] && classify_word(current[0]) & virgin[0])) return 1;
    if (unlikely(current[1] && classify_word(current[1]) & virgin[1])) return 1;
    if (unlikely(current[2] && classify_word(current[2]) & virgin[2])) return 1;
    if (unlikely(current[3] && classify_word(current[3]) & virgin[3])) return 1;

  }

  return 0;

}

#endif

#endif

