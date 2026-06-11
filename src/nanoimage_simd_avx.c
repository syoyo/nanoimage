#include "nanoimage_simd_internal.h"

#if defined(NANOIMAGE_ENABLE_SIMD) &&                                         \
    (defined(__i386__) || defined(__x86_64__) || defined(_M_IX86) ||          \
     defined(_M_X64))

#include <immintrin.h>

void ni_row_add_u8_avx(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                       size_t size) {
  ni_row_add_u8_sse2(dst, src, prev, size);
  _mm256_zeroupper();
}

void ni_row_sub_u8_avx(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                       size_t size) {
  ni_row_sub_u8_sse2(dst, src, prev, size);
  _mm256_zeroupper();
}

#endif
