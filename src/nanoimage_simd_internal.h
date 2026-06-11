#ifndef NANOIMAGE_SIMD_INTERNAL_H_
#define NANOIMAGE_SIMD_INTERNAL_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
  int sse2;
  int sse41;
  int avx;
  int avx2;
  int pclmul;
} ni_cpu_features;

const ni_cpu_features *ni_cpu_features_get(void);

void ni_row_add_u8(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                   size_t size);
void ni_row_sub_u8(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                   size_t size);

void ni_row_add_u8_scalar(uint8_t *dst, const uint8_t *src,
                          const uint8_t *prev, size_t size);
void ni_row_sub_u8_scalar(uint8_t *dst, const uint8_t *src,
                          const uint8_t *prev, size_t size);

#if defined(NANOIMAGE_ENABLE_SIMD) &&                                         \
    (defined(__i386__) || defined(__x86_64__) || defined(_M_IX86) ||          \
     defined(_M_X64))
void ni_row_add_u8_sse2(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                        size_t size);
void ni_row_sub_u8_sse2(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                        size_t size);
void ni_row_add_u8_sse41(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                         size_t size);
void ni_row_sub_u8_sse41(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                         size_t size);
void ni_row_add_u8_avx(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                       size_t size);
void ni_row_sub_u8_avx(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                       size_t size);
void ni_row_add_u8_avx2(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                        size_t size);
void ni_row_sub_u8_avx2(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                        size_t size);
#endif

#ifdef __cplusplus
}
#endif

#endif
