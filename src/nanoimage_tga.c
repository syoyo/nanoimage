#include "nanoimage_tga.h"
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

static const char *ni_tga_error_message(int code) {
  switch (code) {
    case NI_TGA_ERR_TRUNCATED_HEADER:
      return "truncated TGA header";
    case NI_TGA_ERR_DIMENSIONS:
      return "TGA dimensions must be non-zero";
    case NI_TGA_ERR_COLOR_MAP:
      return "unsupported TGA color map";
    case NI_TGA_ERR_IMAGE_TYPE:
      return "unsupported TGA image type";
    case NI_TGA_ERR_DEPTH:
      return "unsupported TGA pixel depth";
    case NI_TGA_ERR_ID_TRUNCATED:
      return "truncated TGA image ID";
    case NI_TGA_ERR_OUTPUT_OVERFLOW:
      return "TGA output size overflow";
    case NI_TGA_ERR_TRUNCATED_RLE:
      return "truncated TGA RLE data";
    case NI_TGA_ERR_PACKET_LENGTH:
      return "invalid TGA packet length";
    case NI_TGA_ERR_TRUNCATED_PIXEL:
      return "truncated TGA pixel data";
    case NI_TGA_ERR_TRUNCATED_RAW:
      return "truncated TGA raw packet";
    case NI_TGA_ERR_CHANNELS:
      return "invalid TGA channels";
    default:
      return "invalid TGA";
  }
}

int ni_load_tga_from_memory(const uint8_t *bytes, size_t size, ni_image *out,
                            char *err, size_t err_capacity) {
  ni_tga_info info;
  uint8_t *pixels;
  int code;

  if ((bytes == NULL) || (out == NULL)) {
    ni_set_error(err, err_capacity, "invalid argument");
    return 0;
  }
  memset(out, 0, sizeof(*out));

  code = ni_tga_header(bytes, size, &info);
  if (code != NI_TGA_OK) {
    ni_set_error(err, err_capacity, "%s", ni_tga_error_message(code));
    return 0;
  }

  pixels = (uint8_t *)ni_stbi_malloc(info.output_size);
  if (pixels == NULL) {
    ni_set_error(err, err_capacity, "out of memory for TGA pixels");
    return 0;
  }

  code = ni_tga_decode_into(bytes, size, &info, pixels, info.output_size);
  if (code != NI_TGA_OK) {
    ni_stbi_free(pixels);
    ni_set_error(err, err_capacity, "%s", ni_tga_error_message(code));
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
