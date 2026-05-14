#include "nanoimage.h"

#include <stdlib.h>

typedef struct {
  ni_allocator allocator;
} ni_allocator_state;

static void *ni_default_malloc(size_t size, void *user_data) {
  (void)user_data;
  return malloc(size);
}

static void *ni_default_realloc(void *ptr, size_t size, void *user_data) {
  (void)user_data;
  return realloc(ptr, size);
}

static void ni_default_free(void *ptr, void *user_data) {
  (void)user_data;
  free(ptr);
}

static ni_allocator_state g_allocator = {{
    ni_default_malloc,
    ni_default_realloc,
    ni_default_free,
    NULL,
    SIZE_MAX,
}};

void ni_set_allocator(const ni_allocator *allocator) {
  if ((allocator == NULL) || (allocator->malloc_fn == NULL) ||
      (allocator->realloc_fn == NULL) || (allocator->free_fn == NULL)) {
    return;
  }

  g_allocator.allocator = *allocator;
  if (g_allocator.allocator.max_allocation == 0u) {
    g_allocator.allocator.max_allocation = SIZE_MAX;
  }
}

void ni_reset_allocator(void) {
  g_allocator.allocator.malloc_fn = ni_default_malloc;
  g_allocator.allocator.realloc_fn = ni_default_realloc;
  g_allocator.allocator.free_fn = ni_default_free;
  g_allocator.allocator.user_data = NULL;
  g_allocator.allocator.max_allocation = SIZE_MAX;
}

void *ni_stbi_malloc(size_t size) {
  if (size > g_allocator.allocator.max_allocation) {
    return NULL;
  }
  return g_allocator.allocator.malloc_fn(size, g_allocator.allocator.user_data);
}

void *ni_stbi_realloc(void *ptr, size_t size) {
  if (size > g_allocator.allocator.max_allocation) {
    return NULL;
  }
  return g_allocator.allocator.realloc_fn(ptr, size, g_allocator.allocator.user_data);
}

void ni_stbi_free(void *ptr) {
  g_allocator.allocator.free_fn(ptr, g_allocator.allocator.user_data);
}

void ni_image_free(ni_image *image) {
  if (image == NULL) {
    return;
  }
  ni_stbi_free(image->data);
  image->data = NULL;
  image->data_size = 0;
  image->width = 0;
  image->height = 0;
  image->channels = 0;
  image->bit_depth = 0;
}
