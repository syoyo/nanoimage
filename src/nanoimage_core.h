#ifndef NANOIMAGE_CORE_INTERNAL_H_
#define NANOIMAGE_CORE_INTERNAL_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Shared scalar helpers used by the nanoimage format loaders. This file is
 * also the translation unit set for the Lean verified core (see
 * formal/README.md); keep the bodies free of allocation, varargs, function
 * pointers and floating point. */

uint16_t ni_read_u16le(const uint8_t *p);
uint32_t ni_read_u32le(const uint8_t *p);
int32_t ni_read_i32le(const uint8_t *p);
uint16_t ni_read_u16be(const uint8_t *p);
uint32_t ni_read_u32be(const uint8_t *p);

int ni_size_mul(size_t a, size_t b, size_t *out);
int ni_size_add(size_t a, size_t b, size_t *out);

uint8_t ni_clamp_u8(int v);
int ni_scale_to_8bit(uint32_t v, uint8_t bit_depth, uint8_t *out);
uint32_t ni_read_packed_bits(const uint8_t *row, size_t pixel_index,
                             uint8_t bit_depth);
uint8_t ni_paeth(uint8_t a, uint8_t b, uint8_t c);

/* BMP verified core (src/nanoimage_bmp_core.c). The struct has no padding:
 * offsets are pinned by _Static_assert in the core, and the Lean differential
 * harness relies on them. */
typedef struct ni_bmp_info {
  size_t row_stride;
  size_t output_size;
  size_t palette_offset;
  uint32_t width;
  uint32_t height;
  uint32_t pixel_offset;
  uint32_t palette_entries;
  uint16_t bit_count;
  uint8_t channels;
  uint8_t top_down;
} ni_bmp_info;

#define NI_BMP_OK 0
#define NI_BMP_ERR_SIGNATURE 1
#define NI_BMP_ERR_LAYOUT 2
#define NI_BMP_ERR_DIMENSIONS 3
#define NI_BMP_ERR_HEIGHT 4
#define NI_BMP_ERR_COMPRESSION 5
#define NI_BMP_ERR_BIT_DEPTH 6
#define NI_BMP_ERR_ROW_OVERFLOW 7
#define NI_BMP_ERR_OUTPUT_OVERFLOW 8
#define NI_BMP_ERR_TRUNCATED 9
#define NI_BMP_ERR_PALETTE 10
#define NI_BMP_ERR_PALETTE_INDEX 11
#define NI_BMP_ERR_OUT_CAPACITY 12

int ni_bmp_mul_fits(size_t a, size_t b);
int ni_bmp_sig_ok(const uint8_t *bytes, size_t size);
int ni_bmp_layout_ok(const uint8_t *bytes, size_t size);
int ni_bmp_geometry(const uint8_t *bytes, size_t size, ni_bmp_info *info);
int ni_bmp_header(const uint8_t *bytes, size_t size, ni_bmp_info *info);
int ni_bmp_decode_into(const uint8_t *bytes, size_t size,
                       const ni_bmp_info *info, uint8_t *out, size_t out_cap);

/* TGA verified core (src/nanoimage_tga_core.c). The struct has no padding;
 * offsets are probed by the Lean translator (formal/tools/c2lean.py). */
typedef struct ni_tga_info {
  size_t output_size;
  size_t data_offset;
  uint32_t width;
  uint32_t height;
  uint8_t channels;
  uint8_t rle;
  uint8_t top_origin;
  uint8_t right_origin;
} ni_tga_info;

#define NI_TGA_OK 0
#define NI_TGA_ERR_TRUNCATED_HEADER 1
#define NI_TGA_ERR_DIMENSIONS 2
#define NI_TGA_ERR_COLOR_MAP 3
#define NI_TGA_ERR_IMAGE_TYPE 4
#define NI_TGA_ERR_DEPTH 5
#define NI_TGA_ERR_ID_TRUNCATED 6
#define NI_TGA_ERR_OUTPUT_OVERFLOW 7
#define NI_TGA_ERR_TRUNCATED_RLE 8
#define NI_TGA_ERR_PACKET_LENGTH 9
#define NI_TGA_ERR_TRUNCATED_PIXEL 10
#define NI_TGA_ERR_TRUNCATED_RAW 11
#define NI_TGA_ERR_CHANNELS 12

int ni_tga_header(const uint8_t *bytes, size_t size, ni_tga_info *info);
int ni_tga_write_pixel(uint8_t *out, size_t base, uint8_t channels, uint8_t s0,
                       uint8_t s1, uint8_t s2, uint8_t s3);
int ni_tga_decode_into(const uint8_t *bytes, size_t size,
                       const ni_tga_info *info, uint8_t *out, size_t out_cap);

#ifdef __cplusplus
}
#endif

#endif
