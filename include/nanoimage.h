#ifndef NANOIMAGE_H_
#define NANOIMAGE_H_

#include <stddef.h>
#include <stdint.h>

#ifndef NI_DEFAULT_MAX_ALLOCATION
#define NI_DEFAULT_MAX_ALLOCATION ((size_t)1024u * 1024u * 1024u)
#endif

typedef void *(*ni_malloc_callback)(size_t size, void *user_data);
typedef void *(*ni_realloc_callback)(void *ptr, size_t size, void *user_data);
typedef void (*ni_free_callback)(void *ptr, void *user_data);
typedef int (*ni_write_callback)(const uint8_t *data, size_t size,
                                 void *user_data);

typedef struct {
  uint32_t width;
  uint32_t height;
  uint8_t channels;
  uint8_t bit_depth;
  size_t row_stride;
} ni_image_info;

typedef int (*ni_row_source_callback)(uint32_t y, uint8_t *dst,
                                      size_t dst_size, void *user_data);
typedef int (*ni_row_sink_callback)(const ni_image_info *info, uint32_t y,
                                    const uint8_t *src, size_t src_size,
                                    void *user_data);

typedef struct {
  ni_malloc_callback malloc_fn;
  ni_realloc_callback realloc_fn;
  ni_free_callback free_fn;
  void *user_data;
  size_t max_allocation;
  size_t max_total_allocation;
} ni_allocator;

typedef struct {
  uint32_t width;
  uint32_t height;
  uint8_t channels;
  uint8_t bit_depth;
  size_t data_size;
  uint8_t *data;
} ni_image;

typedef struct {
  uint8_t *data;
  size_t size;
} ni_buffer;

void ni_set_allocator(const ni_allocator *allocator);
void ni_reset_allocator(void);
void ni_image_free(ni_image *image);
void ni_buffer_free(ni_buffer *buffer);

#endif
