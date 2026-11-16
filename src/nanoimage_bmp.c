#include "nanoimage_bmp.h"
#include "nanoimage_core.h"

#include "nanoimage_alloc_internal.h"

#include <stdarg.h>
#include <stdio.h>
#include <string.h>

static void ni_set_error(char *err, size_t cap, const char *fmt, ...) {
  va_list args;

  if ((err == NULL) || (cap == 0u)) {
    return;
  }

  va_start(args, fmt);
  (void)vsnprintf(err, cap, fmt, args);
  va_end(args);
}

static const char *ni_bmp_error_message(int code) {
  switch (code) {
    case NI_BMP_ERR_SIGNATURE:
      return "invalid BMP signature";
    case NI_BMP_ERR_LAYOUT:
      return "invalid BMP header layout";
    case NI_BMP_ERR_DIMENSIONS:
      return "unsupported BMP dimensions or planes";
    case NI_BMP_ERR_HEIGHT:
      return "invalid BMP height";
    case NI_BMP_ERR_COMPRESSION:
      return "unsupported BMP compression";
    case NI_BMP_ERR_BIT_DEPTH:
      return "unsupported BMP bit depth";
    case NI_BMP_ERR_ROW_OVERFLOW:
      return "BMP row size overflow";
    case NI_BMP_ERR_OUTPUT_OVERFLOW:
      return "BMP output size overflow";
    case NI_BMP_ERR_TRUNCATED:
      return "truncated BMP pixel data";
    case NI_BMP_ERR_PALETTE:
      return "invalid BMP palette";
    case NI_BMP_ERR_PALETTE_INDEX:
      return "BMP palette index out of range";
    default:
      return "invalid BMP";
  }
}

int ni_load_bmp_from_memory(const uint8_t *bytes, size_t size, ni_image *out,
                            char *err, size_t err_capacity) {
  ni_bmp_info info;
  uint8_t *pixels;
  int code;

  if ((bytes == NULL) || (out == NULL)) {
    ni_set_error(err, err_capacity, "invalid argument");
    return 0;
  }
  memset(out, 0, sizeof(*out));

  code = ni_bmp_header(bytes, size, &info);
  if (code != NI_BMP_OK) {
    ni_set_error(err, err_capacity, "%s", ni_bmp_error_message(code));
    return 0;
  }

  pixels = (uint8_t *)ni_stbi_malloc(info.output_size);
  if (pixels == NULL) {
    ni_set_error(err, err_capacity, "out of memory for BMP pixels");
    return 0;
  }

  code = ni_bmp_decode_into(bytes, size, &info, pixels, info.output_size);
  if (code != NI_BMP_OK) {
    ni_stbi_free(pixels);
    ni_set_error(err, err_capacity, "%s", ni_bmp_error_message(code));
    return 0;
  }

  out->width = info.width;
  out->height = info.height;
  out->channels = info.channels;
  out->bit_depth = 8u;
  out->data_size = info.output_size;
  out->data = pixels;
  return 1;
}
