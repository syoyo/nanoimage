#include "nanoimage_png_custom_internal.h"

#if defined(NANOIMAGE_ENABLE_CUSTOM_PNG_CODEC)

#include "nanoimage_alloc_internal.h"
#include "nanoimage_simd_internal.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <vector>

#ifndef NI_FPNG_SOURCE
#define NI_FPNG_SOURCE "/mnt/disk1/work/fpng/src/fpng.cpp"
#endif

#include NI_FPNG_SOURCE

static void ni_fpng_set_error(char *err, size_t cap, const char *msg) {
  if ((err != NULL) && (cap > 0u)) {
    (void)snprintf(err, cap, "%s", msg);
  }
}

extern "C" int ni_fpng_load_png_from_memory(const uint8_t *bytes, size_t size,
                                             ni_image *out, char *err,
                                             size_t err_capacity) {
  std::vector<uint8_t> pixels;
  uint32_t width = 0u;
  uint32_t height = 0u;
  uint32_t channels_in_file = 0u;
  uint8_t *owned_pixels;
  size_t output_size;
  int status;

  if ((bytes == NULL) || (out == NULL) || (size > UINT32_MAX)) {
    return 0;
  }
  if (!ni_png_custom_codec_available()) {
    return 0;
  }

  fpng::fpng_init();
  status = fpng::fpng_get_info(bytes, (uint32_t)size, width, height,
                               channels_in_file);
  if (status != fpng::FPNG_DECODE_SUCCESS) {
    return 0;
  }
  status = fpng::fpng_decode_memory(bytes, (uint32_t)size, pixels, width,
                                    height, channels_in_file,
                                    channels_in_file);
  if (status != fpng::FPNG_DECODE_SUCCESS) {
    return 0;
  }
  if ((channels_in_file != 3u) && (channels_in_file != 4u)) {
    return 0;
  }
  output_size = pixels.size();
  owned_pixels = (uint8_t *)ni_stbi_malloc(output_size);
  if (owned_pixels == NULL) {
    ni_fpng_set_error(err, err_capacity, "out of memory for fpng pixels");
    return 0;
  }
  memcpy(owned_pixels, pixels.data(), output_size);
  memset(out, 0, sizeof(*out));
  out->width = width;
  out->height = height;
  out->channels = (uint8_t)channels_in_file;
  out->bit_depth = 8u;
  out->data_size = output_size;
  out->data = owned_pixels;
  return 1;
}

extern "C" int ni_fpng_write_png_to_memory(const ni_image_info *info,
                                            const uint8_t *data,
                                            size_t row_stride, ni_buffer *out,
                                            char *err, size_t err_capacity) {
  std::vector<uint8_t> encoded;
  uint8_t *owned_encoded;
  bool ok;

  if ((info == NULL) || (data == NULL) || (out == NULL)) {
    ni_fpng_set_error(err, err_capacity, "invalid fpng encoder argument");
    return 0;
  }
  out->data = NULL;
  out->size = 0u;
  if (!ni_png_custom_codec_available()) {
    ni_fpng_set_error(err, err_capacity,
                      "fpng encoder requires runtime SSE4.1 support");
    return 0;
  }
  if ((info->bit_depth != 8u) ||
      ((info->channels != 3u) && (info->channels != 4u))) {
    ni_fpng_set_error(err, err_capacity,
                      "fpng encoder supports only 8-bit RGB/RGBA");
    return 0;
  }
  if (row_stride != (size_t)info->width * (size_t)info->channels) {
    ni_fpng_set_error(err, err_capacity,
                      "fpng encoder requires tightly packed rows");
    return 0;
  }

  fpng::fpng_init();
  ok = fpng::fpng_encode_image_to_memory(data, info->width, info->height,
                                         info->channels, encoded, 0u);
  if (!ok) {
    ni_fpng_set_error(err, err_capacity, "fpng encode failed");
    return 0;
  }
  owned_encoded = (uint8_t *)ni_stbi_malloc(encoded.size());
  if (owned_encoded == NULL) {
    ni_fpng_set_error(err, err_capacity, "out of memory for fpng PNG");
    return 0;
  }
  memcpy(owned_encoded, encoded.data(), encoded.size());
  out->data = owned_encoded;
  out->size = encoded.size();
  return 1;
}

#endif
