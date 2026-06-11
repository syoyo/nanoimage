#include "nanoimage_png.h"

#if defined(NANOIMAGE_ENABLE_CUSTOM_PNG_CODEC)
#include "../src/nanoimage_png_custom_internal.h"
#endif

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static volatile uint64_t g_benchmark_sink = 0u;

static double ni_bench_now_seconds(void) {
  struct timespec ts;
  if (timespec_get(&ts, TIME_UTC) != TIME_UTC) {
    return 0.0;
  }
  return (double)ts.tv_sec + (double)ts.tv_nsec * 1.0e-9;
}

static uint64_t ni_bench_checksum(const uint8_t *data, size_t size) {
  uint64_t h = 1469598103934665603ull;
  size_t i;
  for (i = 0u; i < size; i++) {
    h ^= (uint64_t)data[i];
    h *= 1099511628211ull;
  }
  return h;
}

static void ni_bench_fill_image(uint8_t *data, uint32_t width, uint32_t height,
                                uint8_t channels) {
  uint32_t y;
  for (y = 0u; y < height; y++) {
    uint32_t x;
    for (x = 0u; x < width; x++) {
      const size_t off = ((size_t)y * (size_t)width + (size_t)x) * channels;
      const uint8_t r = (uint8_t)((x * 13u + y * 3u) & 255u);
      const uint8_t g = (uint8_t)((x * 5u + y * 17u) & 255u);
      const uint8_t b = (uint8_t)(((x ^ y) * 11u + (x >> 3u)) & 255u);
      data[off + 0u] = r;
      if (channels > 1u) {
        data[off + 1u] = g;
      }
      if (channels > 2u) {
        data[off + 2u] = b;
      }
      if (channels > 3u) {
        data[off + 3u] = (uint8_t)(192u + ((x + y) & 63u));
      }
    }
  }
}

static int ni_bench_encode_once(const ni_image *image,
                                const ni_png_write_options *options,
                                ni_buffer *out, char *err,
                                size_t err_capacity) {
  if (options == NULL) {
    return ni_write_png_to_memory(image, out, err, err_capacity);
  }
  return ni_write_png_to_memory_ex(image, options, out, err, err_capacity);
}

static int ni_bench_run_encode(const char *name, const ni_image *image,
                               const ni_png_write_options *options,
                               int iterations, ni_buffer *sample_out) {
  char err[256] = {0};
  double t0;
  double elapsed;
  double mpixels;
  int i;
  size_t encoded_size = 0u;

  if (!ni_bench_encode_once(image, options, sample_out, err, sizeof(err))) {
    fprintf(stderr, "%s encode setup failed: %s\n", name, err);
    return 0;
  }
  encoded_size = sample_out->size;
  g_benchmark_sink ^= ni_bench_checksum(sample_out->data, sample_out->size);

  t0 = ni_bench_now_seconds();
  for (i = 0; i < iterations; i++) {
    ni_buffer out;
    err[0] = '\0';
    if (!ni_bench_encode_once(image, options, &out, err, sizeof(err))) {
      fprintf(stderr, "%s encode failed: %s\n", name, err);
      return 0;
    }
    g_benchmark_sink ^= (uint64_t)out.size;
    ni_buffer_free(&out);
  }
  elapsed = ni_bench_now_seconds() - t0;
  mpixels = ((double)image->width * (double)image->height *
             (double)iterations) /
            1000000.0;
  printf("%-18s encode %8.2f MP/s  %8.3f ms/iter  size %9zu bytes\n", name,
         mpixels / elapsed, elapsed * 1000.0 / (double)iterations,
         encoded_size);
  return 1;
}

static int ni_bench_run_decode(const char *name, const ni_buffer *encoded,
                               uint32_t pixels_per_image, int iterations) {
  char err[256] = {0};
  double t0;
  double elapsed;
  double mpixels;
  int i;

  t0 = ni_bench_now_seconds();
  for (i = 0; i < iterations; i++) {
    ni_image image;
    err[0] = '\0';
    if (!ni_load_png_from_memory(encoded->data, encoded->size, &image, err,
                                 sizeof(err))) {
      fprintf(stderr, "%s decode failed: %s\n", name, err);
      return 0;
    }
    g_benchmark_sink ^= ni_bench_checksum(image.data, image.data_size);
    ni_image_free(&image);
  }
  elapsed = ni_bench_now_seconds() - t0;
  mpixels = ((double)pixels_per_image * (double)iterations) / 1000000.0;
  printf("%-18s decode %8.2f MP/s  %8.3f ms/iter  input %8zu bytes\n", name,
         mpixels / elapsed, elapsed * 1000.0 / (double)iterations,
         encoded->size);
  return 1;
}

#if defined(NANOIMAGE_ENABLE_CUSTOM_PNG_CODEC)
static int ni_bench_run_fpng_encode(const char *name, const ni_image *image,
                                    int iterations, ni_buffer *sample_out) {
  ni_image_info info;
  char err[256] = {0};
  double t0;
  double elapsed;
  double mpixels;
  int i;
  size_t encoded_size;

  info.width = image->width;
  info.height = image->height;
  info.channels = image->channels;
  info.bit_depth = image->bit_depth;
  info.row_stride = (size_t)image->width * (size_t)image->channels;
  if (!ni_fpng_write_png_to_memory(&info, image->data, info.row_stride,
                                   sample_out, err, sizeof(err))) {
    fprintf(stderr, "%s encode setup failed: %s\n", name, err);
    return 0;
  }
  encoded_size = sample_out->size;
  g_benchmark_sink ^= ni_bench_checksum(sample_out->data, sample_out->size);

  t0 = ni_bench_now_seconds();
  for (i = 0; i < iterations; i++) {
    ni_buffer out;
    err[0] = '\0';
    if (!ni_fpng_write_png_to_memory(&info, image->data, info.row_stride, &out,
                                     err, sizeof(err))) {
      fprintf(stderr, "%s encode failed: %s\n", name, err);
      return 0;
    }
    g_benchmark_sink ^= (uint64_t)out.size;
    ni_buffer_free(&out);
  }
  elapsed = ni_bench_now_seconds() - t0;
  mpixels = ((double)image->width * (double)image->height *
             (double)iterations) /
            1000000.0;
  printf("%-18s encode %8.2f MP/s  %8.3f ms/iter  size %9zu bytes\n", name,
         mpixels / elapsed, elapsed * 1000.0 / (double)iterations,
         encoded_size);
  return 1;
}
#endif

static int ni_bench_parse_u32(const char *s, uint32_t *out) {
  char *end = NULL;
  unsigned long value = strtoul(s, &end, 10);
  if ((s == end) || (end == NULL) || (*end != '\0') || (value == 0ul) ||
      (value > 0xfffffffful)) {
    return 0;
  }
  *out = (uint32_t)value;
  return 1;
}

static int ni_bench_parse_int(const char *s, int *out) {
  char *end = NULL;
  long value = strtol(s, &end, 10);
  if ((s == end) || (end == NULL) || (*end != '\0') || (value <= 0l) ||
      (value > 1000000l)) {
    return 0;
  }
  *out = (int)value;
  return 1;
}

int main(int argc, char **argv) {
  uint32_t width = 1024u;
  uint32_t height = 1024u;
  int iterations = 20;
  uint8_t channels = 4u;
  size_t pixel_size;
  uint8_t *pixels;
  ni_image image;
  ni_png_write_options fast_options = {NI_PNG_WRITE_FAST, -1};
  ni_buffer default_png;
  ni_buffer fast_png;
#if defined(NANOIMAGE_ENABLE_CUSTOM_PNG_CODEC)
  ni_buffer fpng_png;
#endif
  int ok = 1;

  if (argc > 1 && !ni_bench_parse_u32(argv[1], &width)) {
    fprintf(stderr, "invalid width: %s\n", argv[1]);
    return 2;
  }
  if (argc > 2 && !ni_bench_parse_u32(argv[2], &height)) {
    fprintf(stderr, "invalid height: %s\n", argv[2]);
    return 2;
  }
  if (argc > 3 && !ni_bench_parse_int(argv[3], &iterations)) {
    fprintf(stderr, "invalid iteration count: %s\n", argv[3]);
    return 2;
  }
  if (argc > 4) {
    uint32_t parsed_channels;
    if (!ni_bench_parse_u32(argv[4], &parsed_channels) ||
        ((parsed_channels != 3u) && (parsed_channels != 4u))) {
      fprintf(stderr, "channels must be 3 or 4\n");
      return 2;
    }
    channels = (uint8_t)parsed_channels;
  }

  pixel_size = (size_t)width * (size_t)height * (size_t)channels;
  pixels = (uint8_t *)malloc(pixel_size);
  if (pixels == NULL) {
    fprintf(stderr, "out of memory allocating benchmark image\n");
    return 1;
  }
  ni_bench_fill_image(pixels, width, height, channels);

  image.width = width;
  image.height = height;
  image.channels = channels;
  image.bit_depth = 8u;
  image.data_size = pixel_size;
  image.data = pixels;
  default_png.data = NULL;
  default_png.size = 0u;
  fast_png.data = NULL;
  fast_png.size = 0u;
#if defined(NANOIMAGE_ENABLE_CUSTOM_PNG_CODEC)
  fpng_png.data = NULL;
  fpng_png.size = 0u;
#endif

  printf("nanoimage PNG benchmark: %ux%u x %u channels, %d iterations\n",
         width, height, channels, iterations);
  printf("pixels per image: %.3f MP\n",
         ((double)width * (double)height) / 1000000.0);

  ok = ok && ni_bench_run_encode("default", &image, NULL, iterations,
                                 &default_png);
  ok = ok && ni_bench_run_decode("default", &default_png, width * height,
                                 iterations);
  ok = ok && ni_bench_run_encode("fast", &image, &fast_options, iterations,
                                 &fast_png);
  ok = ok && ni_bench_run_decode("fast", &fast_png, width * height,
                                 iterations);

#if defined(NANOIMAGE_ENABLE_CUSTOM_PNG_CODEC)
  if (ni_bench_run_fpng_encode("fpng", &image, iterations, &fpng_png)) {
    ok = ok && ni_bench_run_decode("fpng", &fpng_png, width * height,
                                   iterations);
  }
#endif

  printf("checksum sink: 0x%016" PRIx64 "\n", (uint64_t)g_benchmark_sink);

  ni_buffer_free(&default_png);
  ni_buffer_free(&fast_png);
#if defined(NANOIMAGE_ENABLE_CUSTOM_PNG_CODEC)
  ni_buffer_free(&fpng_png);
#endif
  free(pixels);
  return ok ? 0 : 1;
}
