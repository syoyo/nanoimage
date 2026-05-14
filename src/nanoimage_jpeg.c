#include "nanoimage_jpeg.h"

#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

#define STBI_NO_STDIO
#define STBI_ONLY_JPEG
#define STBI_ONLY_PNG
#include "stb_image.h"

static void ni_set_error(char *err, size_t cap, const char *fmt, ...) {
  va_list args;

  if ((err == NULL) || (cap == 0)) {
    return;
  }

  va_start(args, fmt);
  (void)vsnprintf(err, cap, fmt, args);
  va_end(args);
}

static int ni_size_mul(size_t a, size_t b, size_t *out) {
  if ((a != 0u) && (b > (SIZE_MAX / a))) {
    return 0;
  }
  *out = a * b;
  return 1;
}

int ni_load_jpeg_from_memory(const uint8_t *bytes, size_t size, ni_image *out,
                             char *err, size_t err_capacity) {
  int w = 0;
  int h = 0;
  int channels = 0;
  size_t data_size = 0;
  size_t pixel_count = 0;

  if ((bytes == NULL) || (out == NULL)) {
    ni_set_error(err, err_capacity, "invalid argument");
    return 0;
  }

  memset(out, 0, sizeof(*out));

  if (size < 2u || bytes[0] != 0xffu || bytes[1] != 0xd8u) {
    ni_set_error(err, err_capacity, "invalid JPEG SOI");
    return 0;
  }

  if (size > (size_t)INT_MAX) {
    ni_set_error(err, err_capacity, "input too large for stb_image");
    return 0;
  }

  {
    stbi_uc *decoded = stbi_load_from_memory(bytes, (int)size, &w, &h, &channels, 0);
    if (decoded == NULL) {
      ni_set_error(err, err_capacity, "JPEG decode failed: %s",
                   stbi_failure_reason() ? stbi_failure_reason() : "unknown");
      return 0;
    }

    if ((w <= 0) || (h <= 0) || (channels <= 0)) {
      stbi_image_free(decoded);
      ni_set_error(err, err_capacity, "invalid decoded JPEG metadata");
      return 0;
    }

    if (!ni_size_mul((size_t)w, (size_t)h, &pixel_count) ||
        !ni_size_mul(pixel_count, (size_t)channels, &data_size)) {
      stbi_image_free(decoded);
      ni_set_error(err, err_capacity, "decoded JPEG size overflow");
      return 0;
    }

    out->width = (uint32_t)w;
    out->height = (uint32_t)h;
    out->channels = (uint8_t)channels;
    out->bit_depth = 8u;
    out->data_size = data_size;
    out->data = decoded;
    return 1;
  }
}
