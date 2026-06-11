# nanoimage

Embeddable image loading and writing in C11.

## Current implementation

- `src/nanoimage_png.c` + `include/nanoimage_png.h`
  - Decodes PNG with interlace (Adam7) and non-interlace scan paths
  - Supported color types: grayscale (0), RGB (2), indexed (3), gray+alpha (4), RGBA (6)
  - Supports bit depths 1/2/4/8/16 where valid for the color type
  - Validates PNG chunk CRC
  - Supports iPhone CgBI PNG streams
  - Uses `src/nanoimage_zlib.c` for zlib/raw-deflate inflate
  - Writes 8-bit/16-bit grayscale, gray+alpha, RGB, and RGBA PNG via streaming callback or in-memory buffer
- `src/nanoimage_jpeg.c` + `include/nanoimage_jpeg.h`
  - Decodes baseline 8-bit JPEG for grayscale and 3-component YCbCr->RGB
  - Supports common 1x1/2x1/1x2/2x2 component sampling factors
  - Writes baseline 8-bit JPEG with configurable quality (`1..100`), grayscale or RGB output, and alpha-drop for GA/RGBA inputs
- `src/nanoimage_bmp.c` + `include/nanoimage_bmp.h`
  - Decodes uncompressed BMP in 8-bit paletted, 24-bit BGR, and 32-bit BGRA layouts
  - Writes uncompressed 8-bit grayscale-paletted, 24-bit RGB, and 32-bit BGRA BMP
- `src/nanoimage_tga.c` + `include/nanoimage_tga.h`
  - Decodes uncompressed and RLE TGA for grayscale, 24-bit truecolor, and 32-bit truecolor+alpha
  - Writes uncompressed grayscale, 24-bit truecolor, and 32-bit truecolor+alpha TGA
- `src/nanoimage_gif.c` + `include/nanoimage_gif.h`
  - Decodes the first GIF image/frame with palette, transparency, interlace, and LZW support
  - Writes still-image GIF with streaming LZW output, fixed-palette quantization, and optional single transparent index from alpha
- `src/nanoimage_zlib.c` + `include/nanoimage_zlib.h`
  - Inflate helper for zlib and raw-deflate streams (uses zlib library)

## Writer API

All writers support:

- `ni_write_<format>()` for low-memory streaming output through a callback
- `ni_write_<format>_to_memory()` for an allocator-owned `ni_buffer`
- PNG also supports row callbacks:
  - `ni_load_png_rows_from_memory()` emits decoded image rows to a callback
  - `ni_write_png_rows()` and `ni_write_png_rows_to_memory()` read source rows
    from a callback
  - `ni_write_png_ex()` and `ni_write_png_to_memory_ex()` accept
    `ni_png_write_options`, including opt-in `NI_PNG_WRITE_FAST`

Use `ni_buffer_free()` to release buffers returned by `*_to_memory()`.

Example:

```c
ni_image image = {/* packed 8-bit or 16-bit pixels */};
ni_buffer encoded;
char err[128] = {0};

if (ni_write_png_to_memory(&image, &encoded, err, sizeof(err))) {
  /* use encoded.data / encoded.size */
  ni_buffer_free(&encoded);
}
```

Writers validate dimensions, channel counts, bit depth, and packed buffer size
before emitting output. PNG, GIF, JPEG, BMP, and TGA all stream rows or blocks
incrementally so applications can avoid building a second full output buffer when
using the callback-based API.

## Build and test

```bash
make test
```

## xmake

Build all targets (example + unit test + fuzzer):

```bash
xmake
```

Run unit tests:

```bash
xmake run nanoimage_test
```

SIMD PNG helpers are off by default. Enable SSE2/SSE4.1/AVX/AVX2 helper builds
with runtime CPUID dispatch using:

```bash
make test SIMD=1
xmake f --simd=y && xmake run nanoimage_test
```

The full upstream custom Deflate codec bridge is also off by default. Enable it
with:

```bash
make test CUSTOM_PNG_CODEC=1
xmake f --custom_png_codec=y && xmake run nanoimage_test
```

This opt-in path compiles the local upstream sources from
`/mnt/disk1/work/fpnge/fpnge.cc` for `NI_PNG_WRITE_FAST` encoding and
`/mnt/disk1/work/fpng/src/fpng.cpp` for fpng-marked PNG decode fast paths. It
requires runtime SSE4.1 support; otherwise nanoimage falls back to the built-in
portable PNG paths unless `NI_PNG_WRITE_REQUIRE_FAST` is requested.

### Custom PNG codec attribution

The optional `CUSTOM_PNG_CODEC=1` bridge builds against upstream codec sources
that are not part of nanoimage's default portable C path:

- fpnge: Copyright 2021 Google LLC. Licensed under the Apache License, Version
  2.0. See `/mnt/disk1/work/fpnge/LICENSE` in the local upstream checkout.
- fpng: Released under the Unlicense / public domain dedication. The upstream
  source also attributes public-domain PNG writer code by Alex Evans, original
  miniz Deflate/Huffman code by R. Geldreich, Jr., and Huffman code-size logic
  by Alistair Moffat and Jyrki Katajainen. See
  `/mnt/disk1/work/fpng/src/fpng.cpp` and `/mnt/disk1/work/fpng/README.md` in
  the local upstream checkout.

## Allocation hardening

Decoders consume in-memory buffers (`pointer + size`) and return decoded pixels
through `ni_image.data`.

Use `ni_set_allocator()` to provide custom `malloc/realloc/free` callbacks,
`max_allocation` per-allocation bound checking, and `max_total_allocation`
active-footprint bound checking. Use `ni_reset_allocator()` to restore defaults.

By default, nanoimage caps both a single allocation and total active allocations
at `NI_DEFAULT_MAX_ALLOCATION` (`1 GiB` unless overridden at compile time before
including `nanoimage.h`). Set either field explicitly if your application needs
a tighter bound, or use `SIZE_MAX` if you intentionally want an unbounded policy.
