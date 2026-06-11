#include "nanoimage_simd_internal.h"

#if defined(NANOIMAGE_ENABLE_SIMD) &&                                         \
    (defined(__i386__) || defined(__x86_64__) || defined(_M_IX86) ||          \
     defined(_M_X64))

#include <emmintrin.h>

void ni_row_add_u8_sse2(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                        size_t size) {
  size_t i = 0u;
  for (; i + 16u <= size; i += 16u) {
    const __m128i a = _mm_loadu_si128((const __m128i *)(const void *)(src + i));
    const __m128i b =
        _mm_loadu_si128((const __m128i *)(const void *)(prev + i));
    _mm_storeu_si128((__m128i *)(void *)(dst + i), _mm_add_epi8(a, b));
  }
  ni_row_add_u8_scalar(dst + i, src + i, prev + i, size - i);
}

void ni_row_sub_u8_sse2(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                        size_t size) {
  size_t i = 0u;
  for (; i + 16u <= size; i += 16u) {
    const __m128i a = _mm_loadu_si128((const __m128i *)(const void *)(src + i));
    const __m128i b =
        _mm_loadu_si128((const __m128i *)(const void *)(prev + i));
    _mm_storeu_si128((__m128i *)(void *)(dst + i), _mm_sub_epi8(a, b));
  }
  ni_row_sub_u8_scalar(dst + i, src + i, prev + i, size - i);
}

#endif
