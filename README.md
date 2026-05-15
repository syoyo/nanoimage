# nanoimage

Embeddable image loading in C11.

## Current implementation

- `src/nanoimage_png.c` + `include/nanoimage_png.h`
  - Decodes PNG with interlace (Adam7) and non-interlace scan paths
  - Supported color types: grayscale (0), RGB (2), indexed (3), gray+alpha (4), RGBA (6)
  - Supports bit depths 1/2/4/8/16 where valid for the color type
  - Validates PNG chunk CRC
  - Supports iPhone CgBI PNG streams
  - Uses `src/nanoimage_zlib.c` for zlib/raw-deflate inflate
- `src/nanoimage_jpeg.c` + `include/nanoimage_jpeg.h`
  - Decodes baseline 8-bit JPEG for grayscale and 3-component YCbCr->RGB
  - Supports common 1x1/2x1/1x2/2x2 component sampling factors
- `src/nanoimage_bmp.c` + `include/nanoimage_bmp.h`
  - Decodes uncompressed BMP in 8-bit paletted, 24-bit BGR, and 32-bit BGRA layouts
- `src/nanoimage_tga.c` + `include/nanoimage_tga.h`
  - Decodes uncompressed and RLE TGA for grayscale, 24-bit truecolor, and 32-bit truecolor+alpha
- `src/nanoimage_gif.c` + `include/nanoimage_gif.h`
  - Decodes the first GIF image/frame with palette, transparency, interlace, and LZW support
- `src/nanoimage_zlib.c` + `include/nanoimage_zlib.h`
  - Inflate helper for zlib and raw-deflate streams (uses zlib library)

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

## Allocation hardening

Decoders consume in-memory buffers (`pointer + size`) and return decoded pixels
through `ni_image.data`.

Use `ni_set_allocator()` to provide custom `malloc/realloc/free` callbacks and
`max_allocation` bound checking. Use `ni_reset_allocator()` to restore defaults.

By default, nanoimage now caps a single allocation at `NI_DEFAULT_MAX_ALLOCATION`
(`1 GiB` unless overridden at compile time before including `nanoimage.h`).
Set `max_allocation` explicitly if your application needs a tighter bound, or
use `SIZE_MAX` if you intentionally want an unbounded policy.
