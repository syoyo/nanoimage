#include "nanoimage_core.h"

uint16_t ni_read_u16le(const uint8_t *p) {
  return (uint16_t)((uint16_t)p[0] | ((uint16_t)p[1] << 8u));
}

uint32_t ni_read_u32le(const uint8_t *p) {
  return (uint32_t)p[0] | ((uint32_t)p[1] << 8u) | ((uint32_t)p[2] << 16u) |
         ((uint32_t)p[3] << 24u);
}

int32_t ni_read_i32le(const uint8_t *p) {
  return (int32_t)ni_read_u32le(p);
}
uint16_t ni_read_u16be(const uint8_t *p) {
  return (uint16_t)(((uint16_t)p[0] << 8u) | p[1]);
}

uint32_t ni_read_u32be(const uint8_t *p) {
  return ((uint32_t)p[0] << 24u) | ((uint32_t)p[1] << 16u) |
         ((uint32_t)p[2] << 8u) | (uint32_t)p[3];
}

int ni_size_mul(size_t a, size_t b, size_t *out) {
  if ((a != 0u) && (b > (SIZE_MAX / a))) {
    return 0;
  }
  *out = a * b;
  return 1;
}

int ni_size_add(size_t a, size_t b, size_t *out) {
  if (a > (SIZE_MAX - b)) {
    return 0;
  }
  *out = a + b;
  return 1;
}

uint8_t ni_clamp_u8(int v) {
  if (v < 0) {
    return 0u;
  }
  if (v > 255) {
    return 255u;
  }
  return (uint8_t)v;
}

int ni_scale_to_8bit(uint32_t v, uint8_t bit_depth, uint8_t *out) {
  uint32_t maxv;
  if ((bit_depth == 0u) || (bit_depth > 8u) || (out == NULL)) {
    return 0;
  }
  maxv = (1u << bit_depth) - 1u;
  *out = (uint8_t)((v * 255u + (maxv / 2u)) / maxv);
  return 1;
}

uint32_t ni_read_packed_bits(const uint8_t *row, size_t pixel_index,
                             uint8_t bit_depth) {
  const size_t bit_index = pixel_index * (size_t)bit_depth;
  const size_t byte_index = bit_index >> 3u;
  const uint8_t shift = (uint8_t)(8u - bit_depth - (bit_index & 7u));
  const uint8_t mask = (uint8_t)((1u << bit_depth) - 1u);
  return (uint32_t)((row[byte_index] >> shift) & mask);
}

uint8_t ni_paeth(uint8_t a, uint8_t b, uint8_t c) {
  const int p = (int)a + (int)b - (int)c;
  const int pa = (p > (int)a) ? (p - (int)a) : ((int)a - p);
  const int pb = (p > (int)b) ? (p - (int)b) : ((int)b - p);
  const int pc = (p > (int)c) ? (p - (int)c) : ((int)c - p);
  if ((pa <= pb) && (pa <= pc)) {
    return a;
  }
  if (pb <= pc) {
    return b;
  }
  return c;
}
