#include "nanoimage_jpeg.h"
#include "nanoimage_png.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int load_file(const char *path, unsigned char **out, size_t *out_size) {
  FILE *fp = fopen(path, "rb");
  long size = 0;
  unsigned char *data = NULL;
  size_t read_size = 0;

  if (fp == NULL) {
    return 0;
  }

  if (fseek(fp, 0, SEEK_END) != 0) {
    fclose(fp);
    return 0;
  }
  size = ftell(fp);
  if (size < 0) {
    fclose(fp);
    return 0;
  }
  if (fseek(fp, 0, SEEK_SET) != 0) {
    fclose(fp);
    return 0;
  }

  data = (unsigned char *)malloc((size_t)size);
  if (data == NULL) {
    fclose(fp);
    return 0;
  }

  read_size = fread(data, 1, (size_t)size, fp);
  fclose(fp);

  if (read_size != (size_t)size) {
    free(data);
    return 0;
  }

  *out = data;
  *out_size = (size_t)size;
  return 1;
}

static int is_png(const unsigned char *data, size_t size) {
  static const unsigned char sig[8] = {0x89, 0x50, 0x4e, 0x47,
                                       0x0d, 0x0a, 0x1a, 0x0a};
  return size >= 8 && memcmp(data, sig, 8) == 0;
}

static int is_jpeg(const unsigned char *data, size_t size) {
  return size >= 2 && data[0] == 0xff && data[1] == 0xd8;
}

int main(int argc, char **argv) {
  unsigned char *bytes = NULL;
  size_t size = 0;
  ni_image image;
  char err[256] = {0};
  int ok = 0;

  if (argc != 2) {
    fprintf(stderr, "Usage: %s <input.(png|jpg|jpeg)>\n", argv[0]);
    return 1;
  }

  if (!load_file(argv[1], &bytes, &size)) {
    fprintf(stderr, "Failed to read file: %s\n", argv[1]);
    return 1;
  }

  if (is_png(bytes, size)) {
    ok = ni_load_png_from_memory(bytes, size, &image, err, sizeof(err));
  } else if (is_jpeg(bytes, size)) {
    ok = ni_load_jpeg_from_memory(bytes, size, &image, err, sizeof(err));
  } else {
    fprintf(stderr, "Unsupported input format: %s\n", argv[1]);
    free(bytes);
    return 1;
  }

  free(bytes);

  if (!ok) {
    fprintf(stderr, "Decode failed: %s\n", err);
    return 1;
  }

  fprintf(stdout, "Decoded image: %ux%u channels=%u bit_depth=%u bytes=%zu\n",
          image.width, image.height, image.channels, image.bit_depth,
          image.data_size);
  ni_image_free(&image);
  return 0;
}
