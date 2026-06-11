#ifndef NANOIMAGE_PNG_H_
#define NANOIMAGE_PNG_H_

#include <stddef.h>
#include <stdint.h>

#include "nanoimage.h"

#define NI_PNG_WRITE_FAST (1u << 0u)
#define NI_PNG_WRITE_REQUIRE_FAST (1u << 1u)

typedef struct {
  uint32_t flags;
  int compression_level;
} ni_png_write_options;

int ni_load_png_from_memory(const uint8_t *bytes, size_t size, ni_image *out,
                            char *err, size_t err_capacity);
int ni_load_png_rows_from_memory(const uint8_t *bytes, size_t size,
                                 ni_row_sink_callback row_fn, void *user_data,
                                 char *err, size_t err_capacity);
int ni_write_png(const ni_image *image, ni_write_callback write_fn,
                 void *user_data, char *err, size_t err_capacity);
int ni_write_png_ex(const ni_image *image, const ni_png_write_options *options,
                    ni_write_callback write_fn, void *user_data, char *err,
                    size_t err_capacity);
int ni_write_png_rows(const ni_image_info *info,
                      ni_row_source_callback row_fn, void *row_user_data,
                      const ni_png_write_options *options,
                      ni_write_callback write_fn, void *write_user_data,
                      char *err, size_t err_capacity);
int ni_write_png_to_memory(const ni_image *image, ni_buffer *out, char *err,
                           size_t err_capacity);
int ni_write_png_to_memory_ex(const ni_image *image,
                              const ni_png_write_options *options,
                              ni_buffer *out, char *err, size_t err_capacity);
int ni_write_png_rows_to_memory(const ni_image_info *info,
                                ni_row_source_callback row_fn,
                                void *row_user_data,
                                const ni_png_write_options *options,
                                ni_buffer *out, char *err,
                                size_t err_capacity);

#endif
