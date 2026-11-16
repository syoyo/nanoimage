#include "nanoimage_core.h"

int ni_bmp_mul_fits(size_t a, size_t b) {
  return (a == 0u) || (b <= (SIZE_MAX / a));
}

int ni_bmp_sig_ok(const uint8_t *bytes, size_t size) {
  return (size >= 54u) && (bytes[0] == 'B') && (bytes[1] == 'M');
}

int ni_bmp_layout_ok(const uint8_t *bytes, size_t size) {
  const uint32_t pixel_offset = ni_read_u32le(&bytes[10]);
  const uint32_t dib_size = ni_read_u32le(&bytes[14]);
  if ((dib_size < 40u) || ((size_t)14 + (size_t)dib_size > size) ||
      ((size_t)pixel_offset < (size_t)14 + (size_t)dib_size) ||
      ((size_t)pixel_offset > size)) {
    return 0;
  }
  return 1;
}

int ni_bmp_geometry(const uint8_t *bytes, size_t size, ni_bmp_info *info) {
  int32_t width_i;
  int32_t height_i;
  uint16_t planes;
  uint16_t bit_count;
  uint32_t compression;
  uint32_t width;
  uint32_t height;
  uint8_t channels;
  uint8_t top_down;

  (void)size; /* only bytes[18..33] are read; the header length guard is in ni_bmp_layout_ok */
  width_i = ni_read_i32le(&bytes[18]);
  height_i = ni_read_i32le(&bytes[22]);
  planes = ni_read_u16le(&bytes[26]);
  bit_count = ni_read_u16le(&bytes[28]);
  compression = ni_read_u32le(&bytes[30]);

  if ((width_i <= 0) || (height_i == 0) || (planes != 1u)) {
    return NI_BMP_ERR_DIMENSIONS;
  }
  if (height_i < 0) {
    if (height_i == INT32_MIN) {
      return NI_BMP_ERR_HEIGHT;
    }
    top_down = 1u;
    height = (uint32_t)(-height_i);
  } else {
    top_down = 0u;
    height = (uint32_t)height_i;
  }
  width = (uint32_t)width_i;
  if (compression != 0u) {
    return NI_BMP_ERR_COMPRESSION;
  }
  if ((bit_count != 8u) && (bit_count != 24u) && (bit_count != 32u)) {
    return NI_BMP_ERR_BIT_DEPTH;
  }
  channels = (bit_count == 32u) ? 4u : 3u;

  info->width = width;
  info->height = height;
  info->bit_count = bit_count;
  info->channels = channels;
  info->top_down = top_down;
  return NI_BMP_OK;
}

static int ni_bmp_header_arith(uint32_t width, uint32_t height, uint16_t bit_count,
                               uint8_t channels, uint32_t pixel_offset, size_t size,
                               ni_bmp_info *info) {
  size_t row_stride, output_size, rows_bytes;
  if (!ni_bmp_mul_fits((size_t)width, (size_t)bit_count)) {
    return NI_BMP_ERR_ROW_OVERFLOW;
  }
  row_stride = ((((size_t)width * (size_t)bit_count) + 31u) >> 5u) << 2u;
  if (!ni_bmp_mul_fits((size_t)width, (size_t)channels)) {
    return NI_BMP_ERR_OUTPUT_OVERFLOW;
  }
  output_size = (size_t)width * (size_t)channels;
  if (!ni_bmp_mul_fits(output_size, (size_t)height)) {
    return NI_BMP_ERR_OUTPUT_OVERFLOW;
  }
  output_size = output_size * (size_t)height;
  if (!ni_bmp_mul_fits(row_stride, (size_t)height)) {
    return NI_BMP_ERR_TRUNCATED;
  }
  rows_bytes = row_stride * (size_t)height;
  if (((size_t)pixel_offset > SIZE_MAX - rows_bytes) ||
      ((size_t)pixel_offset + rows_bytes > size)) {
    return NI_BMP_ERR_TRUNCATED;
  }
  info->row_stride = row_stride;
  info->output_size = output_size;
  return NI_BMP_OK;
}

static int ni_bmp_header_palette(uint16_t bit_count, uint32_t colors_used, uint32_t dib_size,
                                 uint32_t pixel_offset,
                                 ni_bmp_info *info) {
  size_t palette_entries, palette_offset;
  if (bit_count == 8u) {
    palette_entries = (colors_used != 0u) ? (size_t)colors_used : 256u;
    palette_offset = (size_t)14 + (size_t)dib_size;
    if ((palette_entries == 0u) || (palette_entries > 256u) ||
        (palette_offset + (palette_entries * 4u) > (size_t)pixel_offset)) {
      return NI_BMP_ERR_PALETTE;
    }
  } else {
    palette_entries = 0u;
    palette_offset = 0u;
  }
  info->palette_entries = (uint32_t)palette_entries;
  info->palette_offset = palette_offset;
  return NI_BMP_OK;
}

int ni_bmp_header(const uint8_t *bytes, size_t size, ni_bmp_info *info) {
  uint32_t pixel_offset;
  uint32_t dib_size;
  uint16_t bit_count;
  uint32_t colors_used;
  uint32_t width;
  uint32_t height;
  uint8_t channels;
  uint8_t top_down;
  if (!ni_bmp_sig_ok(bytes, size)) {
    return NI_BMP_ERR_SIGNATURE;
  }

  if (!ni_bmp_layout_ok(bytes, size)) {
    return NI_BMP_ERR_LAYOUT;
  }
  pixel_offset = ni_read_u32le(&bytes[10]);
  dib_size = ni_read_u32le(&bytes[14]);

  colors_used = ni_read_u32le(&bytes[46]);

  {
    int geom_code;
    geom_code = ni_bmp_geometry(bytes, size, info);
    if (geom_code != NI_BMP_OK) {
      return geom_code;
    }
    width = info->width;
    height = info->height;
    bit_count = info->bit_count;
    channels = info->channels;
    top_down = info->top_down;
  }
  {
    int arith_code;
    arith_code = ni_bmp_header_arith(width, height, bit_count, channels,
                                     pixel_offset, size, info);
    if (arith_code != NI_BMP_OK) {
      return arith_code;
    }
  }
  {
    int palette_code;
    palette_code = ni_bmp_header_palette(bit_count, colors_used, dib_size,
                                         pixel_offset, info);
    if (palette_code != NI_BMP_OK) {
      return palette_code;
    }
  }

  info->width = width;
  info->height = height;
  info->pixel_offset = pixel_offset;
  info->bit_count = bit_count;
  info->channels = channels;
  info->top_down = top_down;
  return NI_BMP_OK;
}

int ni_bmp_decode_into(const uint8_t *bytes, size_t size,
                       const ni_bmp_info *info, uint8_t *out, size_t out_cap) {
  uint32_t y;
  uint32_t x;
  size_t width;
  size_t height;
  size_t channels;
  size_t row_stride;
  size_t pixel_offset;
  size_t palette_offset;
  size_t palette_entries;

  if (out_cap < info->output_size) {
    return NI_BMP_ERR_OUT_CAPACITY;
  }
  width = (size_t)info->width;
  height = (size_t)info->height;
  channels = (size_t)info->channels;
  row_stride = info->row_stride;
  pixel_offset = (size_t)info->pixel_offset;
  palette_offset = info->palette_offset;
  palette_entries = (size_t)info->palette_entries;

  if (!ni_bmp_mul_fits(row_stride, height)) {
    return NI_BMP_ERR_TRUNCATED;
  }
  if ((pixel_offset > size) || ((row_stride * height) > size - pixel_offset)) {
    return NI_BMP_ERR_TRUNCATED;
  }
  if (info->bit_count == 8u) {
    if ((palette_offset > size) || (palette_entries * 4u > size - palette_offset)) {
      return NI_BMP_ERR_TRUNCATED;
    }
    for (y = 0u; y < info->height; y++) {
      const size_t src_y = info->top_down ? (size_t)y : (height - 1u - (size_t)y);
      const size_t src_base = pixel_offset + src_y * row_stride;
      const size_t dst_base = (size_t)y * width * 3u;
      for (x = 0u; x < info->width; x++) {
        const size_t idx = (size_t)bytes[src_base + (size_t)x];
        const size_t dst = dst_base + (size_t)x * 3u;
        if (idx >= palette_entries) {
          return NI_BMP_ERR_PALETTE_INDEX;
        }
        out[dst + 0u] = bytes[palette_offset + idx * 4u + 2u];
        out[dst + 1u] = bytes[palette_offset + idx * 4u + 1u];
        out[dst + 2u] = bytes[palette_offset + idx * 4u + 0u];
      }
    }
  } else {
    const size_t src_channels = (info->bit_count == 32u) ? 4u : 3u;
    for (y = 0u; y < info->height; y++) {
      const size_t src_y = info->top_down ? (size_t)y : (height - 1u - (size_t)y);
      const size_t src_base = pixel_offset + src_y * row_stride;
      const size_t dst_base = (size_t)y * width * channels;
      for (x = 0u; x < info->width; x++) {
        const size_t s = src_base + (size_t)x * src_channels;
        const size_t d = dst_base + (size_t)x * channels;
        out[d + 0u] = bytes[s + 2u];
        out[d + 1u] = bytes[s + 1u];
        out[d + 2u] = bytes[s + 0u];
        if (channels == 4u) {
          out[d + 3u] = bytes[s + 3u];
        }
      }
    }
  }
  return NI_BMP_OK;
}
