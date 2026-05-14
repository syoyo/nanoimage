#include "nanoimage_jpeg.h"

#include <math.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  uint8_t bits[16];
  uint8_t values[256];
  uint16_t mincode[17];
  uint16_t maxcode[18];
  int16_t valptr[17];
  uint16_t value_count;
  int built;
} ni_huff_table;

typedef struct {
  const uint8_t *data;
  size_t size;
  size_t byte_pos;
  uint32_t bitbuf;
  unsigned bitcount;
  int saw_marker;
} ni_bit_reader;

static const uint8_t k_zigzag[64] = {
    0,  1,  8, 16,  9,  2,  3, 10, 17, 24, 32, 25, 18, 11,  4,  5,
   12, 19, 26, 33, 40, 48, 41, 34, 27, 20, 13,  6,  7, 14, 21, 28,
   35, 42, 49, 56, 57, 50, 43, 36, 29, 22, 15, 23, 30, 37, 44, 51,
   58, 59, 52, 45, 38, 31, 39, 46, 53, 60, 61, 54, 47, 55, 62, 63};

static void ni_set_error(char *err, size_t cap, const char *fmt, ...) {
  va_list args;

  if ((err == NULL) || (cap == 0)) {
    return;
  }

  va_start(args, fmt);
  (void)vsnprintf(err, cap, fmt, args);
  va_end(args);
}

static uint16_t ni_read_u16be(const uint8_t *p) {
  return (uint16_t)(((uint16_t)p[0] << 8u) | p[1]);
}

static int ni_build_huffman(ni_huff_table *tbl) {
  int i;
  int code = 0;
  int k = 0;

  tbl->value_count = 0;
  for (i = 0; i < 16; i++) {
    tbl->value_count = (uint8_t)(tbl->value_count + tbl->bits[i]);
  }

  if (tbl->value_count == 0u) {
    return 0;
  }

  for (i = 1; i <= 16; i++) {
    if (tbl->bits[i - 1] == 0u) {
      tbl->mincode[i] = 0;
      tbl->maxcode[i] = 0xFFFFu;
      tbl->valptr[i] = -1;
    } else {
      tbl->valptr[i] = (int16_t)k;
      tbl->mincode[i] = (uint16_t)code;
      code += tbl->bits[i - 1] - 1;
      tbl->maxcode[i] = (uint16_t)code;
      code++;
      k += tbl->bits[i - 1];
    }
    code <<= 1;
  }
  tbl->maxcode[17] = 0xFFFFu;
  tbl->built = 1;
  return 1;
}

static int ni_br_fill(ni_bit_reader *br, unsigned bits_needed) {
  while (br->bitcount < bits_needed) {
    uint8_t b;

    if (br->byte_pos >= br->size) {
      return 0;
    }

    b = br->data[br->byte_pos++];
    if (b == 0xFFu) {
      if (br->byte_pos >= br->size) {
        br->saw_marker = 1;
        return 0;
      }
      if (br->data[br->byte_pos] == 0x00u) {
        br->byte_pos++;
      } else {
        br->saw_marker = 1;
        br->byte_pos--;
        return 0;
      }
    }

    br->bitbuf = (br->bitbuf << 8u) | b;
    br->bitcount += 8u;
  }

  return 1;
}

static int ni_br_get_bits(ni_bit_reader *br, unsigned bits, uint32_t *out) {
  if ((bits == 0u) || (bits > 16u) || (out == NULL)) {
    return 0;
  }

  if (!ni_br_fill(br, bits)) {
    return 0;
  }

  *out = (br->bitbuf >> (br->bitcount - bits)) & ((1u << bits) - 1u);
  br->bitcount -= bits;
  if (br->bitcount == 0u) {
    br->bitbuf = 0u;
  } else {
    br->bitbuf &= (1u << br->bitcount) - 1u;
  }
  return 1;
}

static int ni_decode_huffman(ni_bit_reader *br, const ni_huff_table *tbl,
                             uint8_t *symbol) {
  uint32_t code = 0;
  int i;

  if ((tbl == NULL) || (symbol == NULL) || !tbl->built) {
    return 0;
  }

  for (i = 1; i <= 16; i++) {
    uint32_t bit;
    int idx;

    if (!ni_br_get_bits(br, 1u, &bit)) {
      return 0;
    }
    code = (code << 1u) | bit;

    if (tbl->valptr[i] < 0) {
      continue;
    }

    if ((code >= tbl->mincode[i]) && (code <= tbl->maxcode[i])) {
      idx = tbl->valptr[i] + (int)(code - tbl->mincode[i]);
      if ((idx < 0) || (idx >= (int)tbl->value_count)) {
        return 0;
      }
      *symbol = tbl->values[idx];
      return 1;
    }
  }

  return 0;
}

static int ni_extend(uint32_t v, unsigned bits) {
  if ((bits == 0u) || (bits >= 31u)) {
    return (int)v;
  }

  if (v < (1u << (bits - 1u))) {
    return (int)(v + ((~0u) << bits) + 1u);
  }

  return (int)v;
}

static void ni_idct_block(const int16_t in[64], uint8_t out[64]) {
  int y;

  for (y = 0; y < 8; y++) {
    int x;
    for (x = 0; x < 8; x++) {
      double sum = 0.0;
      int v;
      for (v = 0; v < 8; v++) {
        int u;
        for (u = 0; u < 8; u++) {
          const double cu = (u == 0) ? (1.0 / sqrt(2.0)) : 1.0;
          const double cv = (v == 0) ? (1.0 / sqrt(2.0)) : 1.0;
          const double basis =
              cos(((2.0 * x + 1.0) * (double)u * 3.14159265358979323846) /
                  16.0) *
              cos(((2.0 * y + 1.0) * (double)v * 3.14159265358979323846) /
                  16.0);
          sum += cu * cv * (double)in[v * 8 + u] * basis;
        }
      }
      {
        int sample = (int)lrint(sum / 4.0) + 128;
        if (sample < 0) {
          sample = 0;
        }
        if (sample > 255) {
          sample = 255;
        }
        out[y * 8 + x] = (uint8_t)sample;
      }
    }
  }
}

int ni_load_jpeg_from_memory(const uint8_t *bytes, size_t size, ni_image *out,
                             char *err, size_t err_capacity) {
  size_t off = 0;
  uint16_t restart_interval = 0;
  uint8_t quant[4][64];
  int have_quant[4] = {0, 0, 0, 0};
  ni_huff_table dc[4];
  ni_huff_table ac[4];
  uint32_t width = 0;
  uint32_t height = 0;
  uint8_t sof_precision = 0;
  uint8_t sof_components = 0;
  uint8_t sof_comp_id = 0;
  uint8_t sof_sampling = 0;
  uint8_t sof_qtable = 0;
  uint8_t *pixels = NULL;

  if ((bytes == NULL) || (out == NULL)) {
    ni_set_error(err, err_capacity, "invalid argument");
    return 0;
  }

  memset(out, 0, sizeof(*out));
  memset(dc, 0, sizeof(dc));
  memset(ac, 0, sizeof(ac));

  if ((size < 4u) || (bytes[0] != 0xFFu) || (bytes[1] != 0xD8u)) {
    ni_set_error(err, err_capacity, "invalid JPEG SOI");
    return 0;
  }

  off = 2;

  while ((off + 1u) < size) {
    uint8_t marker;

    while ((off < size) && (bytes[off] == 0xFFu)) {
      off++;
    }
    if (off >= size) {
      break;
    }

    marker = bytes[off++];

    if (marker == 0xD9u) {
      break;
    }

    if (marker == 0xDAu) {
      uint16_t seg_len;
      uint8_t scan_components;
      uint8_t scan_comp_id;
      uint8_t selector;
      uint8_t td;
      uint8_t ta;
      size_t mcu_x;
      size_t mcu_y;
      size_t bx;
      size_t by;
      ni_bit_reader br;
      int prev_dc = 0;
      size_t pixel_stride;

      if ((off + 2u) > size) {
        ni_set_error(err, err_capacity, "truncated SOS segment");
        goto fail;
      }
      seg_len = ni_read_u16be(bytes + off);
      off += 2u;
      if ((seg_len < 6u) || (off + (size_t)seg_len - 2u > size)) {
        ni_set_error(err, err_capacity, "invalid SOS segment length");
        goto fail;
      }

      if (!have_quant[sof_qtable]) {
        ni_set_error(err, err_capacity, "missing JPEG quantization table");
        goto fail;
      }

      if ((width == 0u) || (height == 0u) || (sof_components != 1u) ||
          (sof_sampling != 0x11u)) {
        ni_set_error(err, err_capacity,
                     "only baseline grayscale JPEG (1 component, 1x1 sampling) is supported");
        goto fail;
      }

      scan_components = bytes[off];
      if (scan_components != 1u) {
        ni_set_error(err, err_capacity,
                     "only single-component JPEG scan is supported");
        goto fail;
      }

      scan_comp_id = bytes[off + 1u];
      selector = bytes[off + 2u];
      td = (uint8_t)(selector >> 4u);
      ta = (uint8_t)(selector & 0x0Fu);

      if ((scan_comp_id != sof_comp_id) || (td > 3u) || (ta > 3u) ||
          !dc[td].built || !ac[ta].built) {
        ni_set_error(err, err_capacity, "invalid JPEG Huffman selector");
        goto fail;
      }

      if ((bytes[off + 3u] != 0u) || (bytes[off + 4u] != 63u) ||
          (bytes[off + 5u] != 0u)) {
        ni_set_error(err, err_capacity, "unsupported JPEG spectral selection");
        goto fail;
      }

      off += (size_t)seg_len - 2u;

      if (restart_interval != 0u) {
        ni_set_error(err, err_capacity, "JPEG restart intervals are unsupported");
        goto fail;
      }

      pixel_stride = (size_t)width;
      if ((size_t)height > (SIZE_MAX / pixel_stride)) {
        ni_set_error(err, err_capacity, "JPEG pixel buffer size overflow");
        goto fail;
      }

      pixels = (uint8_t *)malloc(pixel_stride * (size_t)height);
      if (pixels == NULL) {
        ni_set_error(err, err_capacity, "out of memory for JPEG pixels");
        goto fail;
      }

      memset(&br, 0, sizeof(br));
      br.data = bytes + off;
      br.size = size - off;

      mcu_x = ((size_t)width + 7u) / 8u;
      mcu_y = ((size_t)height + 7u) / 8u;

      for (by = 0; by < mcu_y; by++) {
        for (bx = 0; bx < mcu_x; bx++) {
          int16_t block[64];
          uint8_t decoded[64];
          uint8_t sym;
          uint32_t bits;
          unsigned k;

          memset(block, 0, sizeof(block));

          if (!ni_decode_huffman(&br, &dc[td], &sym)) {
            ni_set_error(err, err_capacity, "failed decoding JPEG DC symbol");
            goto fail;
          }

          if (sym > 11u) {
            ni_set_error(err, err_capacity, "invalid JPEG DC category");
            goto fail;
          }

          if (sym != 0u) {
            if (!ni_br_get_bits(&br, sym, &bits)) {
              ni_set_error(err, err_capacity, "truncated JPEG DC coefficient");
              goto fail;
            }
            prev_dc += ni_extend(bits, sym);
          }
          block[0] = (int16_t)(prev_dc * (int)quant[sof_qtable][0]);

          k = 1u;
          while (k < 64u) {
            uint8_t run;
            uint8_t sz;

            if (!ni_decode_huffman(&br, &ac[ta], &sym)) {
              ni_set_error(err, err_capacity, "failed decoding JPEG AC symbol");
              goto fail;
            }

            if (sym == 0x00u) {
              break;
            }

            if (sym == 0xF0u) {
              k += 16u;
              continue;
            }

            run = (uint8_t)(sym >> 4u);
            sz = (uint8_t)(sym & 0x0Fu);
            k += run;

            if ((k >= 64u) || (sz == 0u) || (sz > 10u)) {
              ni_set_error(err, err_capacity, "invalid JPEG AC run/size");
              goto fail;
            }

            if (!ni_br_get_bits(&br, sz, &bits)) {
              ni_set_error(err, err_capacity, "truncated JPEG AC coefficient");
              goto fail;
            }

            block[k_zigzag[k]] =
                (int16_t)(ni_extend(bits, sz) * (int)quant[sof_qtable][k]);
            k++;
          }

          ni_idct_block(block, decoded);

          {
            size_t yy;
            for (yy = 0; yy < 8u; yy++) {
              size_t xx;
              const size_t py = by * 8u + yy;
              if (py >= (size_t)height) {
                break;
              }
              for (xx = 0; xx < 8u; xx++) {
                const size_t px = bx * 8u + xx;
                if (px >= (size_t)width) {
                  break;
                }
                pixels[py * pixel_stride + px] = decoded[yy * 8u + xx];
              }
            }
          }
        }
      }

      out->width = width;
      out->height = height;
      out->channels = 1u;
      out->bit_depth = 8u;
      out->data_size = (size_t)width * (size_t)height;
      out->data = pixels;
      return 1;
    }

    if ((off + 2u) > size) {
      ni_set_error(err, err_capacity, "truncated JPEG segment");
      goto fail;
    }

    {
      uint16_t seg_len = ni_read_u16be(bytes + off);
      const uint8_t *seg;
      size_t seg_data_len;
      off += 2u;
      if ((seg_len < 2u) || ((off + (size_t)seg_len - 2u) > size)) {
        ni_set_error(err, err_capacity, "invalid JPEG segment length");
        goto fail;
      }
      seg = bytes + off;
      seg_data_len = (size_t)seg_len - 2u;

      if (marker == 0xDBu) {
        size_t p = 0;
        while (p < seg_data_len) {
          uint8_t info;
          uint8_t precision;
          uint8_t table_id;
          size_t qsize;
          size_t i;

          if ((p + 1u) > seg_data_len) {
            ni_set_error(err, err_capacity, "truncated DQT");
            goto fail;
          }

          info = seg[p++];
          precision = (uint8_t)(info >> 4u);
          table_id = (uint8_t)(info & 0x0Fu);

          if ((table_id > 3u) || (precision != 0u)) {
            ni_set_error(err, err_capacity,
                         "only 8-bit JPEG quantization tables are supported");
            goto fail;
          }

          qsize = 64u;
          if ((p + qsize) > seg_data_len) {
            ni_set_error(err, err_capacity, "truncated DQT values");
            goto fail;
          }

          for (i = 0; i < 64u; i++) {
            quant[table_id][i] = seg[p + i];
          }
          have_quant[table_id] = 1;
          p += qsize;
        }
      } else if (marker == 0xC0u) {
        if (seg_data_len < 6u) {
          ni_set_error(err, err_capacity, "truncated SOF0");
          goto fail;
        }
        sof_precision = seg[0];
        height = ni_read_u16be(seg + 1u);
        width = ni_read_u16be(seg + 3u);
        sof_components = seg[5];

        if ((sof_precision != 8u) || (width == 0u) || (height == 0u)) {
          ni_set_error(err, err_capacity, "unsupported SOF0 precision or dimensions");
          goto fail;
        }

        if (sof_components != 1u) {
          ni_set_error(err, err_capacity,
                       "only grayscale JPEG is supported in this implementation");
          goto fail;
        }

        if (seg_data_len < (size_t)(6u + 3u * sof_components)) {
          ni_set_error(err, err_capacity, "truncated SOF0 component data");
          goto fail;
        }

        sof_comp_id = seg[6];
        sof_sampling = seg[7];
        sof_qtable = seg[8];
        if ((sof_qtable > 3u) || (sof_sampling != 0x11u)) {
          ni_set_error(err, err_capacity,
                       "unsupported JPEG sampling factor or quant table index");
          goto fail;
        }
      } else if (marker == 0xC4u) {
        size_t p = 0;
        while (p < seg_data_len) {
          uint8_t info;
          uint8_t cls;
          uint8_t id;
          unsigned count = 0;
          int i;
          ni_huff_table *tbl;

          if ((p + 17u) > seg_data_len) {
            ni_set_error(err, err_capacity, "truncated DHT header");
            goto fail;
          }

          info = seg[p++];
          cls = (uint8_t)(info >> 4u);
          id = (uint8_t)(info & 0x0Fu);

          if ((id > 3u) || (cls > 1u)) {
            ni_set_error(err, err_capacity, "invalid DHT table class/id");
            goto fail;
          }

          tbl = (cls == 0u) ? &dc[id] : &ac[id];
          memset(tbl, 0, sizeof(*tbl));
          for (i = 0; i < 16; i++) {
            tbl->bits[i] = seg[p + (size_t)i];
            count += tbl->bits[i];
          }
          p += 16u;

          if ((p + count) > seg_data_len) {
            ni_set_error(err, err_capacity, "truncated DHT values");
            goto fail;
          }

          for (i = 0; i < (int)count; i++) {
            tbl->values[i] = seg[p + (size_t)i];
          }
          p += count;

          if (!ni_build_huffman(tbl)) {
            ni_set_error(err, err_capacity, "invalid DHT table");
            goto fail;
          }
        }
      } else if (marker == 0xDDu) {
        if (seg_data_len != 2u) {
          ni_set_error(err, err_capacity, "invalid DRI length");
          goto fail;
        }
        restart_interval = ni_read_u16be(seg);
      } else if ((marker >= 0xC1u && marker <= 0xCFu && marker != 0xC4u &&
                  marker != 0xC8u && marker != 0xCCu) ||
                 marker == 0xC2u) {
        ni_set_error(err, err_capacity,
                     "unsupported JPEG encoding (progressive/lossless)");
        goto fail;
      }

      off += seg_data_len;
    }
  }

  ni_set_error(err, err_capacity, "no JPEG scan data found");

fail:
  free(pixels);
  return 0;
}
