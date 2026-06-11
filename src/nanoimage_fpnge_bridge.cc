#include "nanoimage_png_custom_internal.h"

#if defined(NANOIMAGE_ENABLE_CUSTOM_PNG_CODEC)

#include "nanoimage_simd_internal.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <vector>

#ifndef NI_FPNGE_SOURCE
#define NI_FPNGE_SOURCE "/mnt/disk1/work/fpnge/fpnge.cc"
#endif

#include NI_FPNGE_SOURCE

static void ni_custom_set_error(char *err, size_t cap, const char *msg) {
  if ((err != NULL) && (cap > 0u)) {
    (void)snprintf(err, cap, "%s", msg);
  }
}

extern "C" int ni_png_custom_codec_available(void) {
  const ni_cpu_features *features = ni_cpu_features_get();
  return features->sse41;
}

static int ni_fpnge_level_from_options(const ni_png_write_options *options) {
  if ((options == NULL) || (options->compression_level < 0)) {
    return FPNGE_COMPRESS_LEVEL_DEFAULT;
  }
  if (options->compression_level <= 1) {
    return 1;
  }
  if (options->compression_level <= 3) {
    return 2;
  }
  if (options->compression_level <= 6) {
    return FPNGE_COMPRESS_LEVEL_DEFAULT;
  }
  return FPNGE_COMPRESS_LEVEL_BEST;
}

extern "C" int ni_fpnge_write_png_rows(const ni_image_info *info,
                                        const uint8_t *data, size_t row_stride,
                                        const ni_png_write_options *options,
                                        ni_write_callback write_fn,
                                        void *user_data, char *err,
                                        size_t err_capacity) {
  struct FPNGEOptions fpnge_options;
  size_t bytes_per_channel;
  size_t output_capacity;
  size_t written;
  std::vector<uint8_t> output;

  if ((info == NULL) || (data == NULL) || (write_fn == NULL)) {
    ni_custom_set_error(err, err_capacity, "invalid custom PNG encoder argument");
    return 0;
  }
  if (!ni_png_custom_codec_available()) {
    ni_custom_set_error(err, err_capacity,
                        "custom PNG codec requires runtime SSE4.1 support");
    return 0;
  }
  if ((info->channels == 0u) || (info->channels > 4u) ||
      ((info->bit_depth != 8u) && (info->bit_depth != 16u))) {
    ni_custom_set_error(err, err_capacity,
                        "custom PNG encoder supports 8/16-bit 1-4 channel images");
    return 0;
  }

  bytes_per_channel = (info->bit_depth == 16u) ? 2u : 1u;
  if (row_stride <
      (size_t)info->width * (size_t)info->channels * bytes_per_channel) {
    ni_custom_set_error(err, err_capacity, "custom PNG row stride is too small");
    return 0;
  }

  FPNGEFillOptions(&fpnge_options, ni_fpnge_level_from_options(options),
                   FPNGE_CICP_NONE);
  output_capacity = FPNGEOutputAllocSize(bytes_per_channel, info->channels,
                                         info->width, info->height);
  output.resize(output_capacity);

  written = FPNGEEncode(bytes_per_channel, info->channels, data, info->width,
                        row_stride, info->height, output.data(),
                        &fpnge_options);
  if (written == 0u || written > output.size()) {
    ni_custom_set_error(err, err_capacity, "fpnge PNG encode failed");
    return 0;
  }
  if (!write_fn(output.data(), written, user_data)) {
    ni_custom_set_error(err, err_capacity, "writer callback failed");
    return 0;
  }
  return 1;
}

#endif
