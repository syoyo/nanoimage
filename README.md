# nanoimage

Embeddable, dependency-free image loading in C11.

## Current implementation

- `src/nanoimage_png.c` + `include/nanoimage_png.h`
  - Decodes non-interlaced PNG with 8-bit or 16-bit samples
  - Supported color types: grayscale (0), RGB (2), RGBA (6)
  - Validates PNG chunk CRC
  - Uses internal zlib inflater (`src/nanoimage_zlib.c`)
- `src/nanoimage_jpeg.c` + `include/nanoimage_jpeg.h`
  - Decodes baseline 8-bit grayscale JPEG (single component, 1x1 sampling)
- `src/nanoimage_zlib.c` + `include/nanoimage_zlib.h`
  - Internal secure inflater for zlib streams with stored deflate blocks

## Build and test

```bash
make test
```
