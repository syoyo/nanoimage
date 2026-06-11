#include "nanoimage_simd_internal.h"

#if defined(NANOIMAGE_ENABLE_SIMD) &&                                         \
    (defined(__i386__) || defined(__x86_64__) || defined(_M_IX86) ||          \
     defined(_M_X64))

#include <immintrin.h>

void ni_row_add_u8_avx2(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                        size_t size) {
  size_t i = 0u;
  for (; i + 32u <= size; i += 32u) {
    const __m256i a =
        _mm256_loadu_si256((const __m256i *)(const void *)(src + i));
    const __m256i b =
        _mm256_loadu_si256((const __m256i *)(const void *)(prev + i));
    _mm256_storeu_si256((__m256i *)(void *)(dst + i), _mm256_add_epi8(a, b));
  }
  ni_row_add_u8_sse2(dst + i, src + i, prev + i, size - i);
  _mm256_zeroupper();
}

void ni_row_sub_u8_avx2(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                        size_t size) {
  size_t i = 0u;
  for (; i + 32u <= size; i += 32u) {
    const __m256i a =
        _mm256_loadu_si256((const __m256i *)(const void *)(src + i));
    const __m256i b =
        _mm256_loadu_si256((const __m256i *)(const void *)(prev + i));
    _mm256_storeu_si256((__m256i *)(void *)(dst + i), _mm256_sub_epi8(a, b));
  }
  ni_row_sub_u8_sse2(dst + i, src + i, prev + i, size - i);
  _mm256_zeroupper();
}

#endif
