#include "nanoimage_png.h"

#include "nanoimage_alloc_internal.h"
#include "nanoimage_png_custom_internal.h"
#include "nanoimage_simd_internal.h"
#include "nanoimage_write_internal.h"

#include <limits.h>
#include <string.h>
#include <zlib.h>

static const uint8_t k_png_signature[8] = {0x89u, 0x50u, 0x4Eu, 0x47u,
                                           0x0Du, 0x0Au, 0x1Au, 0x0Au};

static uint32_t ni_png_crc32(const uint8_t *data, size_t n) {
  uint32_t crc = 0xffffffffu;
  size_t i;
  for (i = 0u; i < n; i++) {
    int j;
    crc ^= (uint32_t)data[i];
    for (j = 0; j < 8; j++) {
      const uint32_t mask = (uint32_t)-(int32_t)(crc & 1u);
      crc = (crc >> 1u) ^ (0xedb88320u & mask);
    }
  }
  return crc ^ 0xffffffffu;
}

static int ni_png_write_chunk(ni_stream_writer *writer, const char type[4],
                              const uint8_t *data, uint32_t size) {
  uint8_t combined[4u + 4096u];
  uint32_t crc_value;

  if (size > 0u) {
    if (size <= 4096u) {
      memcpy(combined, type, 4u);
      memcpy(combined + 4u, data, size);
      crc_value = ni_png_crc32(combined, 4u + (size_t)size);
    } else {
      crc_value = (uint32_t)crc32(0L, Z_NULL, 0);
      crc_value = (uint32_t)crc32(crc_value, (const Bytef *)type, 4u);
      crc_value = (uint32_t)crc32(crc_value, data, size);
    }
  } else {
    crc_value = ni_png_crc32((const uint8_t *)type, 4u);
  }

  if (!ni_stream_write_u32be(writer, size) ||
      !ni_stream_write(writer, type, 4u) ||
      ((size > 0u) && !ni_stream_write(writer, data, size))) {
    return 0;
  }
  return ni_stream_write_u32be(writer, crc_value);
}

static int ni_png_deflate_data(ni_stream_writer *writer, z_stream *zs,
                               const uint8_t *data, size_t size, int flush) {
  uint8_t outbuf[4096];
  int zret = Z_OK;

  if (size > (size_t)UINT_MAX) {
    ni_write_set_error(writer->err, writer->err_capacity, "PNG row exceeds zlib limit");
    return 0;
  }

  zs->next_in = (Bytef *)data;
  zs->avail_in = (uInt)size;
  do {
    size_t produced;
    zs->next_out = outbuf;
    zs->avail_out = (uInt)sizeof(outbuf);
    zret = deflate(zs, flush);
    if ((zret != Z_OK) && (zret != Z_STREAM_END)) {
      ni_write_set_error(writer->err, writer->err_capacity,
                         "zlib deflate failed (%d)", zret);
      return 0;
    }
    produced = sizeof(outbuf) - (size_t)zs->avail_out;
    if ((produced > 0u) &&
        !ni_png_write_chunk(writer, "IDAT", outbuf, (uint32_t)produced)) {
      return 0;
    }
  } while ((zs->avail_in > 0u) || (zs->avail_out == 0u) ||
           ((flush == Z_FINISH) && (zret != Z_STREAM_END)));

  return 1;
}

typedef struct {
  const uint8_t *data;
  size_t row_stride;
} ni_png_image_row_source;

static int ni_png_image_row_callback(uint32_t y, uint8_t *dst, size_t dst_size,
                                     void *user_data) {
  const ni_png_image_row_source *source = (const ni_png_image_row_source *)user_data;
  memcpy(dst, source->data + (size_t)y * source->row_stride, dst_size);
  return 1;
}

static int ni_png_validate_info(const ni_image_info *info, uint8_t max_channels,
                                size_t *row_stride, size_t *disk_row_stride,
                                char *err, size_t err_capacity) {
  size_t sample_bytes;
  size_t computed_stride;

  if ((info == NULL) || (row_stride == NULL) || (disk_row_stride == NULL)) {
    ni_write_set_error(err, err_capacity, "invalid argument");
    return 0;
  }
  if ((info->width == 0u) || (info->height == 0u)) {
    ni_write_set_error(err, err_capacity, "image dimensions must be non-zero");
    return 0;
  }
  if ((info->channels == 0u) || (info->channels > max_channels)) {
    ni_write_set_error(err, err_capacity, "unsupported image channel count");
    return 0;
  }
  if ((info->bit_depth != 8u) && (info->bit_depth != 16u)) {
    ni_write_set_error(err, err_capacity,
                       "PNG writer supports only 8-bit and 16-bit images");
    return 0;
  }

  sample_bytes = (info->bit_depth == 16u) ? 2u : 1u;
  if (!ni_write_size_mul((size_t)info->width, (size_t)info->channels,
                         &computed_stride) ||
      !ni_write_size_mul(computed_stride, sample_bytes, &computed_stride)) {
    ni_write_set_error(err, err_capacity, "image row size overflow");
    return 0;
  }
  if ((info->row_stride != 0u) && (info->row_stride < computed_stride)) {
    ni_write_set_error(err, err_capacity, "image row stride is too small");
    return 0;
  }

  *disk_row_stride = computed_stride;
  *row_stride = (info->row_stride != 0u) ? info->row_stride : computed_stride;
  return 1;
}

static int ni_write_png_rows_impl(const ni_image_info *info,
                                  ni_row_source_callback row_fn,
                                  void *row_user_data,
                                  const ni_png_write_options *options,
                                  ni_stream_writer *writer) {
  size_t row_stride = 0u;
  size_t disk_row_stride = 0u;
  uint8_t ihdr[13];
  uint8_t color_type;
  uint8_t *row = NULL;
  uint8_t *prev_row = NULL;
  uint8_t *filtered_row = NULL;
  z_stream zs;
  uint32_t y;
  const uint32_t flags = (options != NULL) ? options->flags : 0u;
  const int compression_level =
      (options != NULL) ? options->compression_level : Z_DEFAULT_COMPRESSION;
  int use_fast_filter = 0;

  if (row_fn == NULL) {
    ni_write_set_error(writer->err, writer->err_capacity, "invalid row callback");
    return 0;
  }
  if (!ni_png_validate_info(info, 4u, &row_stride, &disk_row_stride,
                            writer->err, writer->err_capacity)) {
    return 0;
  }
  if ((compression_level < Z_DEFAULT_COMPRESSION) || (compression_level > 9)) {
    ni_write_set_error(writer->err, writer->err_capacity,
                       "invalid PNG compression level");
    return 0;
  }

  if (info->channels == 1u) {
    color_type = 0u;
  } else if (info->channels == 2u) {
    color_type = 4u;
  } else if (info->channels == 3u) {
    color_type = 2u;
  } else {
    color_type = 6u;
  }

  if ((flags & NI_PNG_WRITE_FAST) != 0u) {
    if (ni_png_custom_codec_available()) {
      size_t pixel_size;
      uint8_t *pixels;
      int ok;
      if (!ni_write_size_mul(disk_row_stride, (size_t)info->height, &pixel_size)) {
        ni_write_set_error(writer->err, writer->err_capacity,
                           "image buffer size overflow");
        return 0;
      }
      pixels = (uint8_t *)ni_stbi_malloc(pixel_size);
      if (pixels == NULL) {
        ni_write_set_error(writer->err, writer->err_capacity,
                           "out of memory for custom PNG encoder input");
        return 0;
      }
      for (y = 0u; y < info->height; y++) {
        if (!row_fn(y, pixels + (size_t)y * disk_row_stride, disk_row_stride,
                    row_user_data)) {
          ni_write_set_error(writer->err, writer->err_capacity,
                             "row callback failed");
          ni_stbi_free(pixels);
          return 0;
        }
      }
      ok = ni_fpnge_write_png_rows(info, pixels, disk_row_stride, options,
                                   writer->write_fn, writer->user_data,
                                   writer->err, writer->err_capacity);
      ni_stbi_free(pixels);
      if (ok) {
        return 1;
      }
      if ((flags & NI_PNG_WRITE_REQUIRE_FAST) != 0u) {
        return 0;
      }
    }
    use_fast_filter = (info->bit_depth == 8u) &&
                      ((info->channels == 3u) || (info->channels == 4u));
    if (!use_fast_filter && ((flags & NI_PNG_WRITE_REQUIRE_FAST) != 0u)) {
      ni_write_set_error(writer->err, writer->err_capacity,
                         "fast PNG writer supports only 8-bit RGB/RGBA");
      return 0;
    }
  }

  row = (uint8_t *)ni_stbi_malloc(disk_row_stride);
  if (row == NULL) {
    ni_write_set_error(writer->err, writer->err_capacity, "out of memory for PNG row");
    return 0;
  }
  if (use_fast_filter) {
    prev_row = (uint8_t *)ni_stbi_malloc(disk_row_stride);
    filtered_row = (uint8_t *)ni_stbi_malloc(disk_row_stride);
    if ((prev_row == NULL) || (filtered_row == NULL)) {
      ni_write_set_error(writer->err, writer->err_capacity,
                         "out of memory for PNG filter rows");
      ni_stbi_free(row);
      ni_stbi_free(prev_row);
      ni_stbi_free(filtered_row);
      return 0;
    }
    memset(prev_row, 0, disk_row_stride);
  }

  if (!ni_stream_write(writer, k_png_signature, sizeof(k_png_signature))) {
    ni_stbi_free(row);
    ni_stbi_free(prev_row);
    ni_stbi_free(filtered_row);
    return 0;
  }

  ihdr[0] = (uint8_t)(info->width >> 24u);
  ihdr[1] = (uint8_t)(info->width >> 16u);
  ihdr[2] = (uint8_t)(info->width >> 8u);
  ihdr[3] = (uint8_t)(info->width & 0xffu);
  ihdr[4] = (uint8_t)(info->height >> 24u);
  ihdr[5] = (uint8_t)(info->height >> 16u);
  ihdr[6] = (uint8_t)(info->height >> 8u);
  ihdr[7] = (uint8_t)(info->height & 0xffu);
  ihdr[8] = info->bit_depth;
  ihdr[9] = color_type;
  ihdr[10] = 0u;
  ihdr[11] = 0u;
  ihdr[12] = 0u;
  if (!ni_png_write_chunk(writer, "IHDR", ihdr, sizeof(ihdr))) {
    ni_stbi_free(row);
    ni_stbi_free(prev_row);
    ni_stbi_free(filtered_row);
    return 0;
  }

  memset(&zs, 0, sizeof(zs));
  if (deflateInit(&zs, compression_level) != Z_OK) {
    ni_write_set_error(writer->err, writer->err_capacity, "zlib init failed");
    ni_stbi_free(row);
    ni_stbi_free(prev_row);
    ni_stbi_free(filtered_row);
    return 0;
  }

  for (y = 0u; y < info->height; y++) {
    uint8_t filter = 0u;
    const uint8_t *encoded_row = row;
    if (!row_fn(y, row, disk_row_stride, row_user_data)) {
      ni_write_set_error(writer->err, writer->err_capacity, "row callback failed");
      (void)deflateEnd(&zs);
      ni_stbi_free(row);
      ni_stbi_free(prev_row);
      ni_stbi_free(filtered_row);
      return 0;
    }
    (void)row_stride;

    if (use_fast_filter && (y > 0u)) {
      filter = 2u;
      ni_row_sub_u8(filtered_row, row, prev_row, disk_row_stride);
      encoded_row = filtered_row;
    }

    if (!ni_png_deflate_data(writer, &zs, &filter, 1u, Z_NO_FLUSH) ||
        !ni_png_deflate_data(writer, &zs, encoded_row, disk_row_stride,
                             Z_NO_FLUSH)) {
      (void)deflateEnd(&zs);
      ni_stbi_free(row);
      ni_stbi_free(prev_row);
      ni_stbi_free(filtered_row);
      return 0;
    }
    if (use_fast_filter) {
      memcpy(prev_row, row, disk_row_stride);
    }
  }

  if (!ni_png_deflate_data(writer, &zs, NULL, 0u, Z_FINISH)) {
    (void)deflateEnd(&zs);
    ni_stbi_free(row);
    ni_stbi_free(prev_row);
    ni_stbi_free(filtered_row);
    return 0;
  }
  (void)deflateEnd(&zs);

  ni_stbi_free(row);
  ni_stbi_free(prev_row);
  ni_stbi_free(filtered_row);
  return ni_png_write_chunk(writer, "IEND", NULL, 0u);
}

static int ni_write_png_impl(const ni_image *image,
                             const ni_png_write_options *options,
                             ni_stream_writer *writer) {
  size_t row_stride = 0u;
  size_t required_size = 0u;
  ni_image_info info;
  ni_png_image_row_source source;

  if (!ni_write_image_layout(image, 4u, &row_stride, &required_size, writer->err,
                             writer->err_capacity)) {
    return 0;
  }
  (void)required_size;

  info.width = image->width;
  info.height = image->height;
  info.channels = image->channels;
  info.bit_depth = image->bit_depth;
  info.row_stride = row_stride;
  source.data = image->data;
  source.row_stride = row_stride;

  return ni_write_png_rows_impl(&info, ni_png_image_row_callback, &source,
                                options, writer);
}

int ni_write_png(const ni_image *image, ni_write_callback write_fn,
                 void *user_data, char *err, size_t err_capacity) {
  return ni_write_png_ex(image, NULL, write_fn, user_data, err, err_capacity);
}

int ni_write_png_ex(const ni_image *image, const ni_png_write_options *options,
                    ni_write_callback write_fn, void *user_data, char *err,
                    size_t err_capacity) {
  ni_stream_writer writer;
  if (write_fn == NULL) {
    ni_write_set_error(err, err_capacity, "invalid writer callback");
    return 0;
  }
  writer.write_fn = write_fn;
  writer.user_data = user_data;
  writer.err = err;
  writer.err_capacity = err_capacity;
  return ni_write_png_impl(image, options, &writer);
}

int ni_write_png_rows(const ni_image_info *info,
                      ni_row_source_callback row_fn, void *row_user_data,
                      const ni_png_write_options *options,
                      ni_write_callback write_fn, void *write_user_data,
                      char *err, size_t err_capacity) {
  ni_stream_writer writer;
  if (write_fn == NULL) {
    ni_write_set_error(err, err_capacity, "invalid writer callback");
    return 0;
  }
  writer.write_fn = write_fn;
  writer.user_data = write_user_data;
  writer.err = err;
  writer.err_capacity = err_capacity;
  return ni_write_png_rows_impl(info, row_fn, row_user_data, options, &writer);
}

int ni_write_png_to_memory(const ni_image *image, ni_buffer *out, char *err,
                           size_t err_capacity) {
  return ni_write_png_to_memory_ex(image, NULL, out, err, err_capacity);
}

int ni_write_png_to_memory_ex(const ni_image *image,
                              const ni_png_write_options *options,
                              ni_buffer *out, char *err,
                              size_t err_capacity) {
  ni_memory_writer memory_writer;
  ni_stream_writer writer;
  if (!ni_memory_writer_init(&memory_writer, out)) {
    ni_write_set_error(err, err_capacity, "invalid output buffer");
    return 0;
  }
  writer.write_fn = ni_memory_write_callback;
  writer.user_data = &memory_writer;
  writer.err = err;
  writer.err_capacity = err_capacity;
  if (!ni_write_png_impl(image, options, &writer)) {
    ni_buffer_free(out);
    return 0;
  }
  return 1;
}

int ni_write_png_rows_to_memory(const ni_image_info *info,
                                ni_row_source_callback row_fn,
                                void *row_user_data,
                                const ni_png_write_options *options,
                                ni_buffer *out, char *err,
                                size_t err_capacity) {
  ni_memory_writer memory_writer;
  ni_stream_writer writer;
  if (!ni_memory_writer_init(&memory_writer, out)) {
    ni_write_set_error(err, err_capacity, "invalid output buffer");
    return 0;
  }
  writer.write_fn = ni_memory_write_callback;
  writer.user_data = &memory_writer;
  writer.err = err;
  writer.err_capacity = err_capacity;
  if (!ni_write_png_rows_impl(info, row_fn, row_user_data, options, &writer)) {
    ni_buffer_free(out);
    return 0;
  }
  return 1;
}
