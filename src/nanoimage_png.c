#include "nanoimage_png.h"

#include "nanoimage_zlib.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const uint8_t k_png_signature[8] = {0x89u, 0x50u, 0x4Eu, 0x47u,
                                           0x0Du, 0x0Au, 0x1Au, 0x0Au};

static void ni_set_error(char *err, size_t cap, const char *fmt, ...) {
  va_list args;

  if ((err == NULL) || (cap == 0)) {
    return;
  }

  va_start(args, fmt);
  (void)vsnprintf(err, cap, fmt, args);
  va_end(args);
}

static uint32_t ni_read_u32be(const uint8_t *p) {
  return ((uint32_t)p[0] << 24u) | ((uint32_t)p[1] << 16u) |
         ((uint32_t)p[2] << 8u) | (uint32_t)p[3];
}

static uint32_t ni_crc32(const uint8_t *data, size_t n) {
  uint32_t crc = 0xFFFFFFFFu;
  size_t i;

  for (i = 0; i < n; i++) {
    int j;
    crc ^= (uint32_t)data[i];
    for (j = 0; j < 8; j++) {
      const uint32_t mask = (uint32_t)-(int32_t)(crc & 1u);
      crc = (crc >> 1u) ^ (0xEDB88320u & mask);
    }
  }

  return crc ^ 0xFFFFFFFFu;
}

static uint8_t ni_paeth(uint8_t a, uint8_t b, uint8_t c) {
  const int p = (int)a + (int)b - (int)c;
  const int pa = p > (int)a ? p - (int)a : (int)a - p;
  const int pb = p > (int)b ? p - (int)b : (int)b - p;
  const int pc = p > (int)c ? p - (int)c : (int)c - p;

  if ((pa <= pb) && (pa <= pc)) {
    return a;
  }
  if (pb <= pc) {
    return b;
  }
  return c;
}

int ni_load_png_from_memory(const uint8_t *bytes, size_t size, ni_image *out,
                            char *err, size_t err_capacity) {
  uint32_t width = 0;
  uint32_t height = 0;
  uint8_t bit_depth = 0;
  uint8_t color_type = 0;
  uint8_t channels = 0;
  size_t samples_bytes = 0;
  size_t stride = 0;
  size_t raw_size = 0;
  uint8_t *idat = NULL;
  size_t idat_size = 0;
  uint8_t *raw = NULL;
  uint8_t *pixels = NULL;
  size_t off = 0;
  int saw_ihdr = 0;
  int saw_iend = 0;

  if ((bytes == NULL) || (out == NULL)) {
    ni_set_error(err, err_capacity, "invalid argument");
    return 0;
  }

  memset(out, 0, sizeof(*out));

  if (size < sizeof(k_png_signature)) {
    ni_set_error(err, err_capacity, "PNG too small");
    return 0;
  }

  if (memcmp(bytes, k_png_signature, sizeof(k_png_signature)) != 0) {
    ni_set_error(err, err_capacity, "invalid PNG signature");
    return 0;
  }

  off = sizeof(k_png_signature);

  while ((off + 12u) <= size) {
    const size_t chunk_start = off;
    const uint32_t chunk_len = ni_read_u32be(bytes + off);
    const uint8_t *chunk_type = bytes + off + 4u;
    const uint8_t *chunk_data = bytes + off + 8u;
    const size_t chunk_total = 12u + (size_t)chunk_len;
    uint32_t expected_crc;
    uint32_t computed_crc;

    if ((off + chunk_total) > size) {
      ni_set_error(err, err_capacity, "truncated PNG chunk");
      goto fail;
    }

    expected_crc = ni_read_u32be(bytes + off + 8u + (size_t)chunk_len);
    computed_crc = ni_crc32(chunk_type, 4u + (size_t)chunk_len);
    if (computed_crc != expected_crc) {
      ni_set_error(err, err_capacity, "PNG CRC mismatch");
      goto fail;
    }

    if (memcmp(chunk_type, "IHDR", 4) == 0) {
      if (saw_ihdr || chunk_len != 13u) {
        ni_set_error(err, err_capacity, "invalid IHDR chunk");
        goto fail;
      }
      width = ni_read_u32be(chunk_data);
      height = ni_read_u32be(chunk_data + 4u);
      bit_depth = chunk_data[8];
      color_type = chunk_data[9];
      if ((width == 0u) || (height == 0u)) {
        ni_set_error(err, err_capacity, "PNG dimensions must be non-zero");
        goto fail;
      }
      if ((bit_depth != 8u) && (bit_depth != 16u)) {
        ni_set_error(err, err_capacity, "unsupported PNG bit depth");
        goto fail;
      }
      if ((color_type != 0u) && (color_type != 2u) && (color_type != 6u)) {
        ni_set_error(err, err_capacity, "unsupported PNG color type");
        goto fail;
      }
      if ((chunk_data[10] != 0u) || (chunk_data[11] != 0u) || (chunk_data[12] != 0u)) {
        ni_set_error(err, err_capacity,
                     "unsupported PNG compression/filter/interlace");
        goto fail;
      }
      saw_ihdr = 1;
    } else if (memcmp(chunk_type, "IDAT", 4) == 0) {
      uint8_t *new_idat;
      if (!saw_ihdr) {
        ni_set_error(err, err_capacity, "IDAT appears before IHDR");
        goto fail;
      }
      if (chunk_len > (uint32_t)(SIZE_MAX - idat_size)) {
        ni_set_error(err, err_capacity, "PNG IDAT too large");
        goto fail;
      }
      new_idat = (uint8_t *)realloc(idat, idat_size + (size_t)chunk_len);
      if (new_idat == NULL) {
        ni_set_error(err, err_capacity, "out of memory while collecting IDAT");
        goto fail;
      }
      idat = new_idat;
      if (chunk_len > 0u) {
        memcpy(idat + idat_size, chunk_data, (size_t)chunk_len);
      }
      idat_size += (size_t)chunk_len;
    } else if (memcmp(chunk_type, "IEND", 4) == 0) {
      if (chunk_len != 0u) {
        ni_set_error(err, err_capacity, "invalid IEND chunk");
        goto fail;
      }
      saw_iend = 1;
      break;
    }

    off = chunk_start + chunk_total;
  }

  if (!saw_ihdr || !saw_iend || (idat_size == 0u)) {
    ni_set_error(err, err_capacity, "missing required PNG chunks");
    goto fail;
  }

  channels = (color_type == 0u) ? 1u : ((color_type == 2u) ? 3u : 4u);
  samples_bytes = (bit_depth == 16u) ? 2u : 1u;

  if ((size_t)width > (SIZE_MAX / channels) ||
      ((size_t)width * channels) > (SIZE_MAX / samples_bytes)) {
    ni_set_error(err, err_capacity, "PNG row size overflow");
    goto fail;
  }

  stride = (size_t)width * (size_t)channels * samples_bytes;

  if ((size_t)height > (SIZE_MAX / (stride + 1u))) {
    ni_set_error(err, err_capacity, "PNG raw buffer size overflow");
    goto fail;
  }

  raw_size = (stride + 1u) * (size_t)height;
  raw = (uint8_t *)malloc(raw_size);
  if (raw == NULL) {
    ni_set_error(err, err_capacity, "out of memory for PNG raw buffer");
    goto fail;
  }

  {
    size_t inflated = 0;
    if (!ni_zlib_inflate_stored(idat, idat_size, raw, raw_size, &inflated, err,
                                err_capacity)) {
      goto fail;
    }
    if (inflated != raw_size) {
      ni_set_error(err, err_capacity, "unexpected PNG inflated size");
      goto fail;
    }
  }

  if ((size_t)height > (SIZE_MAX / stride)) {
    ni_set_error(err, err_capacity, "PNG pixel buffer size overflow");
    goto fail;
  }

  pixels = (uint8_t *)malloc(stride * (size_t)height);
  if (pixels == NULL) {
    ni_set_error(err, err_capacity, "out of memory for PNG pixels");
    goto fail;
  }

  {
    size_t y;
    for (y = 0; y < (size_t)height; y++) {
      const size_t in_row = y * (stride + 1u);
      const size_t out_row = y * stride;
      const uint8_t filter = raw[in_row];
      size_t x;

      if (filter > 4u) {
        ni_set_error(err, err_capacity, "unsupported PNG filter type");
        goto fail;
      }

      for (x = 0; x < stride; x++) {
        const uint8_t src = raw[in_row + 1u + x];
        const uint8_t left = (x >= (size_t)channels * samples_bytes)
                                 ? pixels[out_row + x - ((size_t)channels * samples_bytes)]
                                 : 0u;
        const uint8_t up = (y > 0u) ? pixels[out_row + x - stride] : 0u;
        const uint8_t up_left = ((y > 0u) &&
                                 (x >= (size_t)channels * samples_bytes))
                                    ? pixels[out_row + x - stride -
                                             ((size_t)channels * samples_bytes)]
                                    : 0u;

        switch (filter) {
          case 0u:
            pixels[out_row + x] = src;
            break;
          case 1u:
            pixels[out_row + x] = (uint8_t)(src + left);
            break;
          case 2u:
            pixels[out_row + x] = (uint8_t)(src + up);
            break;
          case 3u:
            pixels[out_row + x] = (uint8_t)(src + ((uint8_t)(((uint16_t)left + up) >> 1u)));
            break;
          case 4u:
            pixels[out_row + x] = (uint8_t)(src + ni_paeth(left, up, up_left));
            break;
          default:
            ni_set_error(err, err_capacity, "invalid PNG filter");
            goto fail;
        }
      }
    }
  }

  out->width = width;
  out->height = height;
  out->channels = channels;
  out->bit_depth = bit_depth;
  out->data_size = stride * (size_t)height;
  out->data = pixels;

  free(raw);
  free(idat);
  return 1;

fail:
  free(raw);
  free(idat);
  free(pixels);
  return 0;
}
