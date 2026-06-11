#ifndef NANOIMAGE_PNG_CUSTOM_INTERNAL_H_
#define NANOIMAGE_PNG_CUSTOM_INTERNAL_H_

#include "nanoimage_png.h"

#ifdef __cplusplus
extern "C" {
#endif

#if defined(NANOIMAGE_ENABLE_CUSTOM_PNG_CODEC)
int ni_png_custom_codec_available(void);
int ni_fpnge_write_png_rows(const ni_image_info *info, const uint8_t *data,
                            size_t row_stride,
                            const ni_png_write_options *options,
                            ni_write_callback write_fn, void *user_data,
                            char *err, size_t err_capacity);
int ni_fpng_load_png_from_memory(const uint8_t *bytes, size_t size,
                                 ni_image *out, char *err,
                                 size_t err_capacity);
int ni_fpng_write_png_to_memory(const ni_image_info *info, const uint8_t *data,
                                size_t row_stride, ni_buffer *out, char *err,
                                size_t err_capacity);
#else
static inline int ni_png_custom_codec_available(void) { return 0; }
static inline int ni_fpnge_write_png_rows(const ni_image_info *info,
                                          const uint8_t *data,
                                          size_t row_stride,
                                          const ni_png_write_options *options,
                                          ni_write_callback write_fn,
                                          void *user_data, char *err,
                                          size_t err_capacity) {
  (void)info;
  (void)data;
  (void)row_stride;
  (void)options;
  (void)write_fn;
  (void)user_data;
  (void)err;
  (void)err_capacity;
  return 0;
}
static inline int ni_fpng_load_png_from_memory(const uint8_t *bytes,
                                               size_t size, ni_image *out,
                                               char *err,
                                               size_t err_capacity) {
  (void)bytes;
  (void)size;
  (void)out;
  (void)err;
  (void)err_capacity;
  return 0;
}
#endif

#ifdef __cplusplus
}
#endif

#endif
