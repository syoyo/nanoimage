CC ?= cc
CXX ?= c++
CFLAGS ?= -std=c11 -O2 -Wall -Wextra -Werror -pedantic
CXXFLAGS ?= -std=c++17 -O2 -Wall -Wextra -fno-strict-aliasing
CPPFLAGS ?= -Iinclude
SIMD ?= 0
CUSTOM_PNG_CODEC ?= 0

SRC = src/nanoimage_alloc.c src/nanoimage_write.c src/nanoimage_simd.c src/nanoimage_zlib.c src/nanoimage_png.c src/nanoimage_png_write.c src/nanoimage_jpeg.c src/nanoimage_jpeg_write.c src/nanoimage_bmp.c src/nanoimage_bmp_write.c src/nanoimage_tga.c src/nanoimage_tga_write.c src/nanoimage_gif.c src/nanoimage_gif_write.c
SIMD_SRC = src/nanoimage_simd_sse2.c src/nanoimage_simd_sse41.c src/nanoimage_simd_avx.c src/nanoimage_simd_avx2.c
CUSTOM_CODEC_SRC = src/nanoimage_fpnge_bridge.cc src/nanoimage_fpng_bridge.cc
TEST_SRC = tests/test_nanoimage.c
BENCH_SRC = benchmarks/png_benchmark.c
TEST_BIN = tests/test_nanoimage
BENCH_BIN = build/nanoimage_png_benchmark
EXAMPLE_BIN = build/linux/x86_64/release/nanoimage_example

OBJ = $(SRC:.c=.o)
TEST_OBJ = $(TEST_SRC:.c=.o)
BENCH_OBJ = $(BENCH_SRC:.c=.o)
LINKER = $(CC)

ifneq ($(filter 1,$(SIMD) $(CUSTOM_PNG_CODEC)),)
CPPFLAGS += -DNANOIMAGE_ENABLE_SIMD
OBJ += $(SIMD_SRC:.c=.o)
endif
ifeq ($(CUSTOM_PNG_CODEC),1)
CPPFLAGS += -DNANOIMAGE_ENABLE_CUSTOM_PNG_CODEC
OBJ += $(CUSTOM_CODEC_SRC:.cc=.o)
LINKER = $(CXX)
endif

PNGSUITE_DIR ?= /home/syoyo/work/stb/tests/pngsuite

.PHONY: all test benchmark pngsuite clean

all: test

test: $(TEST_BIN)
	./$(TEST_BIN)

$(TEST_BIN): $(OBJ) $(TEST_OBJ)
	$(LINKER) $(OBJ) $(TEST_OBJ) -lm -lz -o $(TEST_BIN)

benchmark: $(BENCH_BIN)
	./$(BENCH_BIN)

$(BENCH_BIN): $(OBJ) $(BENCH_OBJ) | build
	$(LINKER) $(OBJ) $(BENCH_OBJ) -lm -lz -o $(BENCH_BIN)

build:
	mkdir -p build

%.o: %.c
	$(CC) $(CFLAGS) $(CPPFLAGS) -c $< -o $@

%.o: %.cc
	$(CXX) $(CXXFLAGS) $(CPPFLAGS) -msse4.1 -mpclmul -c $< -o $@

src/nanoimage_simd_sse2.o: src/nanoimage_simd_sse2.c
	$(CC) $(CFLAGS) $(CPPFLAGS) -msse2 -c $< -o $@

src/nanoimage_simd_sse41.o: src/nanoimage_simd_sse41.c
	$(CC) $(CFLAGS) $(CPPFLAGS) -msse4.1 -c $< -o $@

src/nanoimage_simd_avx.o: src/nanoimage_simd_avx.c
	$(CC) $(CFLAGS) $(CPPFLAGS) -mavx -c $< -o $@

src/nanoimage_simd_avx2.o: src/nanoimage_simd_avx2.c
	$(CC) $(CFLAGS) $(CPPFLAGS) -mavx2 -c $< -o $@

# Run pngsuite sweep:
#   PASS  - valid file decoded successfully
#   FAIL  - valid file failed to decode         (counts toward exit failure)
#   XFAIL - corrupt file rejected as expected   (excluded from fail count)
#   XPASS - corrupt file decoded unexpectedly   (counts toward exit failure)
pngsuite: $(EXAMPLE_BIN)
	@pass=0; fail=0; xfail=0; xpass=0; \
	for f in $$(find $(PNGSUITE_DIR) -name "*.png" ! -path "*/corrupt/*"); do \
	  if timeout 8s $(EXAMPLE_BIN) "$$f" >/dev/null 2>&1; then pass=$$((pass+1)); \
	  else echo "FAIL: $$f"; fail=$$((fail+1)); fi; \
	done; \
	for f in $(PNGSUITE_DIR)/corrupt/*.png; do \
	  if timeout 8s $(EXAMPLE_BIN) "$$f" >/dev/null 2>&1; then \
	    echo "XPASS: $$f"; xpass=$$((xpass+1)); \
	  else xfail=$$((xfail+1)); fi; \
	done; \
	echo "$$pass passed, $$fail failed, $$xfail xfailed, $$xpass xpassed"; \
	if [ $$fail -ne 0 ] || [ $$xpass -ne 0 ]; then exit 1; fi

clean:
	rm -f $(TEST_BIN) $(BENCH_BIN) $(OBJ) $(TEST_OBJ) $(BENCH_OBJ) $(SIMD_SRC:.c=.o) $(CUSTOM_CODEC_SRC:.cc=.o)
