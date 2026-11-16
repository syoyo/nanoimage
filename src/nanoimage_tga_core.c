#include "nanoimage_core.h"

int ni_tga_header(const uint8_t *bytes, size_t size, ni_tga_info *info) {
  uint8_t id_length;
  uint8_t color_map_type;
  uint8_t image_type;
  uint16_t width;
  uint16_t height;
  uint8_t pixel_depth;
  uint8_t descriptor;
  uint8_t channels;
  size_t output_size;

  if (size < 18u) {
    return NI_TGA_ERR_TRUNCATED_HEADER;
  }
  id_length = bytes[0];
  color_map_type = bytes[1];
  image_type = bytes[2];
  width = ni_read_u16le(&bytes[12]);
  height = ni_read_u16le(&bytes[14]);
  pixel_depth = bytes[16];
  descriptor = bytes[17];

  if ((width == 0u) || (height == 0u)) {
    return NI_TGA_ERR_DIMENSIONS;
  }
  if (color_map_type != 0u) {
    return NI_TGA_ERR_COLOR_MAP;
  }
  if ((image_type != 2u) && (image_type != 3u) && (image_type != 10u) &&
      (image_type != 11u)) {
    return NI_TGA_ERR_IMAGE_TYPE;
  }
  if ((image_type == 3u) || (image_type == 11u)) {
    if (pixel_depth != 8u) {
      return NI_TGA_ERR_DEPTH;
    }
    channels = 1u;
  } else if (pixel_depth == 24u) {
    channels = 3u;
  } else if (pixel_depth == 32u) {
    channels = 4u;
  } else {
    return NI_TGA_ERR_DEPTH;
  }
  if ((size_t)18 + (size_t)id_length > size) {
    return NI_TGA_ERR_ID_TRUNCATED;
  }
  if (!ni_bmp_mul_fits((size_t)width, (size_t)height)) {
    return NI_TGA_ERR_OUTPUT_OVERFLOW;
  }
  output_size = (size_t)width * (size_t)height;
  if (!ni_bmp_mul_fits(output_size, (size_t)channels)) {
    return NI_TGA_ERR_OUTPUT_OVERFLOW;
  }
  output_size = output_size * (size_t)channels;
  info->width = (uint32_t)width;
  info->height = (uint32_t)height;
  info->channels = channels;
  info->rle = (uint8_t)((image_type == 10u) || (image_type == 11u));
  info->top_origin = (uint8_t)((descriptor & 0x20u) != 0u);
  info->right_origin = (uint8_t)((descriptor & 0x10u) != 0u);
  info->data_offset = (size_t)18 + (size_t)id_length;
  info->output_size = output_size;
  return NI_TGA_OK;
}

int ni_tga_write_pixel(uint8_t *out, size_t base, uint8_t channels, uint8_t s0,
                       uint8_t s1, uint8_t s2, uint8_t s3) {
  if (channels == 1u) {
    out[base] = s0;
    return 1;
  }
  if (channels == 3u) {
    out[base] = s2;
    out[base + 1u] = s1;
    out[base + 2u] = s0;
    return 1;
  }
  if (channels == 4u) {
    out[base] = s2;
    out[base + 1u] = s1;
    out[base + 2u] = s0;
    out[base + 3u] = s3;
    return 1;
  }
  return 0;
}

int ni_tga_decode_into(const uint8_t *bytes, size_t size,
                       const ni_tga_info *info, uint8_t *out,
                       size_t out_cap) {
  size_t n_pixels;
  size_t pixel_index;
  size_t off;
  uint8_t channels;
  uint8_t rle;

  (void)out_cap; /* the caller guarantees out_cap >= info->output_size */
  channels = info->channels;
  rle = info->rle;
  n_pixels = (size_t)info->width * (size_t)info->height;
  off = info->data_offset;
  pixel_index = 0u;

  while (pixel_index < n_pixels) {
    size_t count = 1u;
    uint8_t packet_header = 0u;
    uint8_t s0 = 0u;
    uint8_t s1 = 0u;
    uint8_t s2 = 0u;
    uint8_t s3 = 255u;
    size_t i;

    if (rle != 0u) {
      if (off >= size) {
        return NI_TGA_ERR_TRUNCATED_RLE;
      }
      packet_header = bytes[off];
      off += 1u;
      count = (size_t)(packet_header & 0x7fu) + 1u;
    }
    if (count > (n_pixels - pixel_index)) {
      return NI_TGA_ERR_PACKET_LENGTH;
    }
    if ((rle == 0u) || ((packet_header & 0x80u) != 0u)) {
      if (off + (size_t)channels > size) {
        return NI_TGA_ERR_TRUNCATED_PIXEL;
      }
      s0 = bytes[off];
      if (channels > 1u) {
        s1 = bytes[off + 1u];
      }
      if (channels > 2u) {
        s2 = bytes[off + 2u];
      }
      if (channels > 3u) {
        s3 = bytes[off + 3u];
      }
      off += (size_t)channels;
    }
    for (i = 0u; i < count; i++) {
      uint8_t r0 = s0;
      uint8_t r1 = s1;
      uint8_t r2 = s2;
      uint8_t r3 = s3;
      uint32_t x;
      uint32_t y;
      uint32_t dst_x;
      uint32_t dst_y;
      size_t dst_base;
      int wr;

      if ((rle != 0u) && ((packet_header & 0x80u) == 0u)) {
        if (off + (size_t)channels > size) {
          return NI_TGA_ERR_TRUNCATED_RAW;
        }
        r0 = bytes[off];
        if (channels > 1u) {
          r1 = bytes[off + 1u];
        }
        if (channels > 2u) {
          r2 = bytes[off + 2u];
        }
        if (channels > 3u) {
          r3 = bytes[off + 3u];
        }
        off += (size_t)channels;
      }
      x = (uint32_t)(pixel_index % (size_t)info->width);
      y = (uint32_t)(pixel_index / (size_t)info->width);
      dst_x = (info->right_origin != 0u)
                  ? (uint32_t)(info->width - 1u - x)
                  : x;
      dst_y = (info->top_origin != 0u)
                  ? y
                  : (uint32_t)(info->height - 1u - y);
      dst_base = ((size_t)dst_y * (size_t)info->width + (size_t)dst_x) *
                 (size_t)channels;
      wr = ni_tga_write_pixel(out, dst_base, channels, r0, r1, r2, r3);
      if (!wr) {
        return NI_TGA_ERR_CHANNELS;
      }
      pixel_index += 1u;
    }
  }
  return NI_TGA_OK;
}
