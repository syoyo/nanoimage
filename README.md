# nanoimage

Embeddable image loading in C11.

## Current implementation

- `src/nanoimage_png.c` + `include/nanoimage_png.h`
  - Uses `stb_image` backend for broad PNG support (1/2/4/8/16-bit input)
- `src/nanoimage_jpeg.c` + `include/nanoimage_jpeg.h`
  - Uses `stb_image` backend for baseline/progressive JPEG decoding
- `src/nanoimage_zlib.c` + `include/nanoimage_zlib.h`
  - Internal secure inflater for zlib streams with stored deflate blocks
- `third_party/stb_image.h`
  - Vendored stb_image single-header decoder

## Build and test

```bash
make test
```

## xmake

Build all targets (example + unit test + fuzzer):

```bash
xmake
```

Run the unit test binary:

```bash
xmake run nanoimage_test
```

Run the example program:

```bash
xmake run nanoimage_example -- path/to/input.png
```

Run libFuzzer target:

```bash
xmake run nanoimage_fuzz -- tests/fuzz/corpus
```
