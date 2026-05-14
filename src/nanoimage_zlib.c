#include "nanoimage_zlib.h"

#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <zlib.h>

static void ni_set_error(char *err, size_t cap, const char *fmt, ...) {
  va_list args;

  if ((err == NULL) || (cap == 0)) {
    return;
  }

  va_start(args, fmt);
  (void)vsnprintf(err, cap, fmt, args);
  va_end(args);
}

static int ni_zlib_inflate_impl(const uint8_t *input, size_t input_len,
                                uint8_t *output, size_t output_len,
                                size_t *out_written, char *err,
                                size_t err_capacity, int raw_stream) {
  z_stream zs;
  int zret;

  if ((input == NULL) || (output == NULL) || (out_written == NULL)) {
    ni_set_error(err, err_capacity, "invalid argument");
    return 0;
  }

  *out_written = 0;

  if (input_len == 0u) {
    ni_set_error(err, err_capacity, "empty deflate input");
    return 0;
  }

  memset(&zs, 0, sizeof(zs));
  zs.next_in = (Bytef *)input;
  zs.avail_in = (uInt)input_len;
  zs.next_out = output;
  zs.avail_out = (uInt)output_len;

  zret = inflateInit2(&zs, raw_stream ? -MAX_WBITS : MAX_WBITS);
  if (zret != Z_OK) {
    ni_set_error(err, err_capacity, "zlib init failed (%d)", zret);
    return 0;
  }

  zret = inflate(&zs, Z_FINISH);
  if ((zret == Z_STREAM_END) && (zs.total_out <= output_len)) {
    *out_written = (size_t)zs.total_out;
    (void)inflateEnd(&zs);
    return 1;
  }

  (void)inflateEnd(&zs);
  if (zret == Z_BUF_ERROR) {
    ni_set_error(err, err_capacity, "inflate output buffer too small");
  } else if (zret == Z_MEM_ERROR) {
    ni_set_error(err, err_capacity, "out of memory while inflating zlib");
  } else if (zret == Z_DATA_ERROR) {
    ni_set_error(err, err_capacity, "invalid zlib stream");
  } else {
    ni_set_error(err, err_capacity, "zlib inflate failed (%d)", zret);
  }
  return 0;
}

int ni_zlib_inflate_stored(const uint8_t *input, size_t input_len,
                           uint8_t *output, size_t output_len,
                           size_t *out_written, char *err,
                           size_t err_capacity) {
  return ni_zlib_inflate_impl(input, input_len, output, output_len, out_written,
                              err, err_capacity, 0);
}

int ni_zlib_inflate_raw(const uint8_t *input, size_t input_len, uint8_t *output,
                        size_t output_len, size_t *out_written, char *err,
                        size_t err_capacity) {
  return ni_zlib_inflate_impl(input, input_len, output, output_len, out_written,
                              err, err_capacity, 1);
}
