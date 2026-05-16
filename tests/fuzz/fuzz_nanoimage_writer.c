#include "nanoimage_bmp.h"
#include "nanoimage_gif.h"
#include "nanoimage_jpeg.h"
#include "nanoimage_png.h"
#include "nanoimage_tga.h"

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef enum {
  NI_WRITER_FUZZ_PNG,
  NI_WRITER_FUZZ_JPEG,
  NI_WRITER_FUZZ_BMP,
  NI_WRITER_FUZZ_GIF,
  NI_WRITER_FUZZ_TGA
} ni_writer_fuzz_format;

static void *ni_fuzz_malloc(size_t size, void *user_data) {
  (void)user_data;
  return malloc(size);
}

static void *ni_fuzz_realloc(void *ptr, size_t size, void *user_data) {
  (void)user_data;
  return realloc(ptr, size);
}

static void ni_fuzz_free(void *ptr, void *user_data) {
  (void)user_data;
  free(ptr);
}

static ni_writer_fuzz_format ni_writer_fuzz_mode(void) {
  const char *mode = getenv("NI_FUZZ_WRITER_FORMAT");
  if ((mode == NULL) || (strcmp(mode, "png") == 0)) {
    return NI_WRITER_FUZZ_PNG;
  }
  if (strcmp(mode, "jpeg") == 0) {
    return NI_WRITER_FUZZ_JPEG;
  }
  if (strcmp(mode, "bmp") == 0) {
    return NI_WRITER_FUZZ_BMP;
  }
  if (strcmp(mode, "gif") == 0) {
    return NI_WRITER_FUZZ_GIF;
  }
  return NI_WRITER_FUZZ_TGA;
}

static uint8_t ni_pick_u8(const uint8_t *data, size_t size, size_t *off,
                          uint8_t fallback) {
  if (*off >= size) {
    return fallback;
  }
  return data[(*off)++];
}

static int ni_make_test_image(const uint8_t *data, size_t size,
                              ni_writer_fuzz_format format, ni_image *image) {
  uint8_t channels = 4u;
  uint8_t bit_depth = 8u;
  uint32_t width;
  uint32_t height;
  size_t off = 0u;
  size_t sample_bytes;
  size_t row_stride;
  size_t total_size;
  uint8_t *pixels;
  size_t i;

  if (format == NI_WRITER_FUZZ_JPEG) {
    channels = (ni_pick_u8(data, size, &off, 0u) & 1u) ? 3u : 1u;
  } else if ((format == NI_WRITER_FUZZ_BMP) || (format == NI_WRITER_FUZZ_TGA)) {
    static const uint8_t k_options[4] = {1u, 3u, 4u, 3u};
    channels = k_options[ni_pick_u8(data, size, &off, 0u) & 3u];
  } else if (format == NI_WRITER_FUZZ_GIF) {
    static const uint8_t k_options[4] = {1u, 2u, 3u, 4u};
    channels = k_options[ni_pick_u8(data, size, &off, 0u) & 3u];
  } else {
    static const uint8_t k_options[4] = {1u, 2u, 3u, 4u};
    channels = k_options[ni_pick_u8(data, size, &off, 0u) & 3u];
    bit_depth = (ni_pick_u8(data, size, &off, 0u) & 1u) ? 16u : 8u;
  }

  width = (uint32_t)(1u + (uint32_t)(ni_pick_u8(data, size, &off, 0u) % 32u));
  height = (uint32_t)(1u + (uint32_t)(ni_pick_u8(data, size, &off, 0u) % 32u));
  sample_bytes = (bit_depth == 16u) ? 2u : 1u;
  row_stride = (size_t)width * (size_t)channels * sample_bytes;
  total_size = row_stride * (size_t)height;

  pixels = (uint8_t *)malloc(total_size);
  if (pixels == NULL) {
    return 0;
  }

  for (i = 0u; i < total_size; i++) {
    pixels[i] = ni_pick_u8(data, size, &off, (uint8_t)(i * 37u + 11u));
  }

  image->width = width;
  image->height = height;
  image->channels = channels;
  image->bit_depth = bit_depth;
  image->data_size = total_size;
  image->data = pixels;
  return 1;
}

static void ni_free_test_image(ni_image *image) {
  free(image->data);
  image->data = NULL;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  ni_writer_fuzz_format format = ni_writer_fuzz_mode();
  ni_image image;
  ni_image decoded;
  ni_buffer out = {0};
  ni_jpeg_write_options jpeg_options;
  ni_allocator allocator = {ni_fuzz_malloc, ni_fuzz_realloc, ni_fuzz_free, NULL,
                            8u * 1024u * 1024u, 8u * 1024u * 1024u};
  char err[128] = {0};

  memset(&image, 0, sizeof(image));
  memset(&decoded, 0, sizeof(decoded));
  jpeg_options.quality = (int)(1u + (unsigned)ni_pick_u8(data, size, &(size_t){0u}, 90u) % 100u);

  ni_set_allocator(&allocator);
  if (!ni_make_test_image(data, size, format, &image)) {
    ni_reset_allocator();
    return 0;
  }

  if (format == NI_WRITER_FUZZ_PNG) {
    if (ni_write_png_to_memory(&image, &out, err, sizeof(err))) {
      if (ni_load_png_from_memory(out.data, out.size, &decoded, err, sizeof(err))) {
        ni_image_free(&decoded);
      }
      ni_buffer_free(&out);
    }
  } else if (format == NI_WRITER_FUZZ_JPEG) {
    if (ni_write_jpeg_to_memory(&image, &jpeg_options, &out, err, sizeof(err))) {
      if (ni_load_jpeg_from_memory(out.data, out.size, &decoded, err, sizeof(err))) {
        ni_image_free(&decoded);
      }
      ni_buffer_free(&out);
    }
  } else if (format == NI_WRITER_FUZZ_BMP) {
    if (ni_write_bmp_to_memory(&image, &out, err, sizeof(err))) {
      if (ni_load_bmp_from_memory(out.data, out.size, &decoded, err, sizeof(err))) {
        ni_image_free(&decoded);
      }
      ni_buffer_free(&out);
    }
  } else if (format == NI_WRITER_FUZZ_GIF) {
    if (ni_write_gif_to_memory(&image, &out, err, sizeof(err))) {
      if (ni_load_gif_from_memory(out.data, out.size, &decoded, err, sizeof(err))) {
        ni_image_free(&decoded);
      }
      ni_buffer_free(&out);
    }
  } else {
    if (ni_write_tga_to_memory(&image, &out, err, sizeof(err))) {
      if (ni_load_tga_from_memory(out.data, out.size, &decoded, err, sizeof(err))) {
        ni_image_free(&decoded);
      }
      ni_buffer_free(&out);
    }
  }

  ni_free_test_image(&image);
  ni_reset_allocator();
  return 0;
}
