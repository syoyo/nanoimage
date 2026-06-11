#include "nanoimage_simd_internal.h"

#include <string.h>

#if defined(NANOIMAGE_ENABLE_SIMD) && defined(_MSC_VER) &&                    \
    (defined(_M_IX86) || defined(_M_X64))
#include <intrin.h>
#endif

typedef void (*ni_row_op)(uint8_t *dst, const uint8_t *src,
                          const uint8_t *prev, size_t size);

static ni_cpu_features g_features;
static int g_features_initialized;
static ni_row_op g_row_add = ni_row_add_u8_scalar;
static ni_row_op g_row_sub = ni_row_sub_u8_scalar;

void ni_row_add_u8_scalar(uint8_t *dst, const uint8_t *src,
                          const uint8_t *prev, size_t size) {
  size_t i;
  for (i = 0u; i < size; i++) {
    dst[i] = (uint8_t)(src[i] + prev[i]);
  }
}

void ni_row_sub_u8_scalar(uint8_t *dst, const uint8_t *src,
                          const uint8_t *prev, size_t size) {
  size_t i;
  for (i = 0u; i < size; i++) {
    dst[i] = (uint8_t)(src[i] - prev[i]);
  }
}

#if defined(NANOIMAGE_ENABLE_SIMD) &&                                         \
    (defined(__i386__) || defined(__x86_64__) || defined(_M_IX86) ||          \
     defined(_M_X64))

static void ni_cpuid(uint32_t leaf, uint32_t subleaf, uint32_t out[4]) {
#if defined(_MSC_VER)
  int regs[4];
  __cpuidex(regs, (int)leaf, (int)subleaf);
  out[0] = (uint32_t)regs[0];
  out[1] = (uint32_t)regs[1];
  out[2] = (uint32_t)regs[2];
  out[3] = (uint32_t)regs[3];
#elif defined(__GNUC__) || defined(__clang__)
#if defined(__i386__) && defined(__PIC__)
  uint32_t eax = leaf;
  uint32_t ebx;
  uint32_t ecx = subleaf;
  uint32_t edx;
  __asm__ volatile("xchgl %%ebx, %1\n\t"
                   "cpuid\n\t"
                   "xchgl %%ebx, %1"
                   : "+a"(eax), "=&r"(ebx), "+c"(ecx), "=d"(edx)
                   :
                   : "cc");
  out[0] = eax;
  out[1] = ebx;
  out[2] = ecx;
  out[3] = edx;
#else
  uint32_t eax = leaf;
  uint32_t ebx;
  uint32_t ecx = subleaf;
  uint32_t edx;
  __asm__ volatile("cpuid"
                   : "+a"(eax), "=b"(ebx), "+c"(ecx), "=d"(edx)
                   :
                   : "cc");
  out[0] = eax;
  out[1] = ebx;
  out[2] = ecx;
  out[3] = edx;
#endif
#else
  (void)leaf;
  (void)subleaf;
  memset(out, 0, sizeof(uint32_t) * 4u);
#endif
}

static uint64_t ni_xgetbv0(void) {
#if defined(_MSC_VER)
  return _xgetbv(0);
#elif defined(__GNUC__) || defined(__clang__)
  uint32_t eax;
  uint32_t edx;
  __asm__ volatile("xgetbv" : "=a"(eax), "=d"(edx) : "c"(0) : "cc");
  return ((uint64_t)edx << 32u) | (uint64_t)eax;
#else
  return 0u;
#endif
}

static void ni_detect_x86_features(ni_cpu_features *features) {
  uint32_t regs[4] = {0u, 0u, 0u, 0u};
  uint32_t max_leaf;
  int os_avx = 0;

  ni_cpuid(0u, 0u, regs);
  max_leaf = regs[0];
  if (max_leaf >= 1u) {
    ni_cpuid(1u, 0u, regs);
    features->sse2 = ((regs[3] & (1u << 26u)) != 0u);
    features->sse41 = ((regs[2] & (1u << 19u)) != 0u);
    features->pclmul = ((regs[2] & (1u << 1u)) != 0u);
    if (((regs[2] & (1u << 27u)) != 0u) &&
        ((regs[2] & (1u << 28u)) != 0u)) {
      const uint64_t xcr0 = ni_xgetbv0();
      os_avx = ((xcr0 & 0x6u) == 0x6u);
      features->avx = os_avx;
    }
  }
  if ((max_leaf >= 7u) && os_avx) {
    ni_cpuid(7u, 0u, regs);
    features->avx2 = ((regs[1] & (1u << 5u)) != 0u);
  }
}
#endif

const ni_cpu_features *ni_cpu_features_get(void) {
  if (!g_features_initialized) {
    memset(&g_features, 0, sizeof(g_features));
#if defined(NANOIMAGE_ENABLE_SIMD) &&                                         \
    (defined(__i386__) || defined(__x86_64__) || defined(_M_IX86) ||          \
     defined(_M_X64))
    ni_detect_x86_features(&g_features);
    if (g_features.avx2) {
      g_row_add = ni_row_add_u8_avx2;
      g_row_sub = ni_row_sub_u8_avx2;
    } else if (g_features.avx) {
      g_row_add = ni_row_add_u8_avx;
      g_row_sub = ni_row_sub_u8_avx;
    } else if (g_features.sse41) {
      g_row_add = ni_row_add_u8_sse41;
      g_row_sub = ni_row_sub_u8_sse41;
    } else if (g_features.sse2) {
      g_row_add = ni_row_add_u8_sse2;
      g_row_sub = ni_row_sub_u8_sse2;
    }
#endif
    g_features_initialized = 1;
  }
  return &g_features;
}

void ni_row_add_u8(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                   size_t size) {
  (void)ni_cpu_features_get();
  g_row_add(dst, src, prev, size);
}

void ni_row_sub_u8(uint8_t *dst, const uint8_t *src, const uint8_t *prev,
                   size_t size) {
  (void)ni_cpu_features_get();
  g_row_sub(dst, src, prev, size);
}
