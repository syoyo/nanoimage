#include "nanoimage_zlib.h"

#include <stdarg.h>
#include <stdio.h>

static void ni_set_error(char *err, size_t cap, const char *fmt, ...) {
  va_list args;

  if ((err == NULL) || (cap == 0)) {
    return;
  }

  va_start(args, fmt);
  (void)vsnprintf(err, cap, fmt, args);
  va_end(args);
}

static uint32_t ni_adler32(const uint8_t *data, size_t n) {
  uint32_t s1 = 1;
  uint32_t s2 = 0;
  size_t i;

  for (i = 0; i < n; i++) {
    s1 = (s1 + data[i]) % 65521u;
    s2 = (s2 + s1) % 65521u;
  }

  return (s2 << 16u) | s1;
}

int ni_zlib_inflate_stored(const uint8_t *input, size_t input_len,
                           uint8_t *output, size_t output_len,
                           size_t *out_written, char *err,
                           size_t err_capacity) {
  size_t in_off = 0;
  size_t out_off = 0;
  uint32_t bitbuf = 0;
  unsigned bitcount = 0;
  int bfinal = 0;

  if ((input == NULL) || (output == NULL) || (out_written == NULL)) {
    ni_set_error(err, err_capacity, "invalid argument");
    return 0;
  }

  *out_written = 0;

  if (input_len < 6) {
    ni_set_error(err, err_capacity, "zlib stream too small");
    return 0;
  }

  {
    const uint8_t cmf = input[0];
    const uint8_t flg = input[1];
    const uint16_t cmfflg = (uint16_t)(((uint16_t)cmf << 8u) | flg);

    if ((cmf & 0x0Fu) != 8u) {
      ni_set_error(err, err_capacity, "unsupported compression method");
      return 0;
    }

    if ((cmfflg % 31u) != 0u) {
      ni_set_error(err, err_capacity, "invalid zlib header checksum");
      return 0;
    }

    if ((flg & 0x20u) != 0u) {
      ni_set_error(err, err_capacity, "preset dictionary is unsupported");
      return 0;
    }

    in_off = 2;
  }

  while (!bfinal) {
    unsigned btype;
    unsigned i;

    while (bitcount < 3u) {
      if (in_off >= input_len) {
        ni_set_error(err, err_capacity, "unexpected end of deflate stream");
        return 0;
      }
      bitbuf |= ((uint32_t)input[in_off++]) << bitcount;
      bitcount += 8u;
    }

    bfinal = (int)(bitbuf & 1u);
    btype = (bitbuf >> 1u) & 0x3u;
    bitbuf >>= 3u;
    bitcount -= 3u;

    if (btype != 0u) {
      ni_set_error(err, err_capacity,
                   "unsupported deflate block type (only stored blocks)");
      return 0;
    }

    bitbuf = 0;
    bitcount = 0;

    if ((in_off + 4u) > input_len) {
      ni_set_error(err, err_capacity, "truncated stored block header");
      return 0;
    }

    {
      const uint16_t len = (uint16_t)(input[in_off] | ((uint16_t)input[in_off + 1u] << 8u));
      const uint16_t nlen = (uint16_t)(input[in_off + 2u] | ((uint16_t)input[in_off + 3u] << 8u));
      in_off += 4u;

      if ((uint16_t)(len ^ 0xFFFFu) != nlen) {
        ni_set_error(err, err_capacity, "stored block length check failed");
        return 0;
      }

      if ((in_off + (size_t)len) > input_len) {
        ni_set_error(err, err_capacity, "stored block exceeds input");
        return 0;
      }

      if ((out_off + (size_t)len) > output_len) {
        ni_set_error(err, err_capacity, "inflate output buffer too small");
        return 0;
      }

      for (i = 0; i < (unsigned)len; i++) {
        output[out_off++] = input[in_off++];
      }
    }
  }

  if ((in_off + 4u) > input_len) {
    ni_set_error(err, err_capacity, "missing zlib adler32");
    return 0;
  }

  {
    const uint32_t expected = ((uint32_t)input[in_off] << 24u) |
                              ((uint32_t)input[in_off + 1u] << 16u) |
                              ((uint32_t)input[in_off + 2u] << 8u) |
                              (uint32_t)input[in_off + 3u];
    const uint32_t actual = ni_adler32(output, out_off);

    if (actual != expected) {
      ni_set_error(err, err_capacity, "zlib adler32 mismatch");
      return 0;
    }
  }

  *out_written = out_off;
  return 1;
}
