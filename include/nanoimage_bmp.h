#ifndef NANOIMAGE_BMP_H_
#define NANOIMAGE_BMP_H_

#include <stddef.h>
#include <stdint.h>

#include "nanoimage.h"

int ni_load_bmp_from_memory(const uint8_t *bytes, size_t size, ni_image *out,
                            char *err, size_t err_capacity);

#endif
