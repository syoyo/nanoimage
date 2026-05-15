#include "nanoimage_bmp.h"
#include "nanoimage_gif.h"
#include "nanoimage_jpeg.h"
#include "nanoimage_png.h"
#include "nanoimage_tga.h"
#include "nanoimage_zlib.h"

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  ni_image image;
  char err[128] = {0};

  if (size >= 8 && memcmp(data, "\x89PNG\r\n\x1a\n", 8) == 0) {
    if (ni_load_png_from_memory(data, size, &image, err, sizeof(err))) {
      ni_image_free(&image);
    }
  }

  if (size >= 2 && data[0] == 0xff && data[1] == 0xd8) {
    if (ni_load_jpeg_from_memory(data, size, &image, err, sizeof(err))) {
      ni_image_free(&image);
    }
  }

  if (size >= 2 && data[0] == 'B' && data[1] == 'M') {
    if (ni_load_bmp_from_memory(data, size, &image, err, sizeof(err))) {
      ni_image_free(&image);
    }
  }

  if (size >= 6 &&
      (memcmp(data, "GIF87a", 6) == 0 || memcmp(data, "GIF89a", 6) == 0)) {
    if (ni_load_gif_from_memory(data, size, &image, err, sizeof(err))) {
      ni_image_free(&image);
    }
  }

  if (size >= 18 && data[1] == 0x00 &&
      (data[2] == 2 || data[2] == 3 || data[2] == 10 || data[2] == 11)) {
    if (ni_load_tga_from_memory(data, size, &image, err, sizeof(err))) {
      ni_image_free(&image);
    }
  }

  if (size >= 2 && data[0] == 0x78) {
    uint8_t *out = NULL;
    size_t out_cap = 1u << 20;
    size_t written = 0;

    out = (uint8_t *)malloc(out_cap);
    if (out != NULL) {
      (void)ni_zlib_inflate_stored(data, size, out, out_cap, &written, err,
                                   sizeof(err));
      free(out);
    }
  }

  return 0;
}
