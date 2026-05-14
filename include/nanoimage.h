#ifndef NANOIMAGE_H_
#define NANOIMAGE_H_

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

typedef struct {
  uint32_t width;
  uint32_t height;
  uint8_t channels;
  uint8_t bit_depth;
  size_t data_size;
  uint8_t *data;
} ni_image;

static inline void ni_image_free(ni_image *image) {
  if (image == NULL) {
    return;
  }
  free(image->data);
  image->data = NULL;
  image->data_size = 0;
  image->width = 0;
  image->height = 0;
  image->channels = 0;
  image->bit_depth = 0;
}

#endif
