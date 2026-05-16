CC ?= cc
CFLAGS ?= -std=c11 -O2 -Wall -Wextra -Werror -pedantic
CPPFLAGS ?= -Iinclude

SRC = src/nanoimage_alloc.c src/nanoimage_write.c src/nanoimage_zlib.c src/nanoimage_png.c src/nanoimage_png_write.c src/nanoimage_jpeg.c src/nanoimage_jpeg_write.c src/nanoimage_bmp.c src/nanoimage_bmp_write.c src/nanoimage_tga.c src/nanoimage_tga_write.c src/nanoimage_gif.c src/nanoimage_gif_write.c
TEST_SRC = tests/test_nanoimage.c
TEST_BIN = tests/test_nanoimage
EXAMPLE_BIN = build/linux/x86_64/release/nanoimage_example

PNGSUITE_DIR ?= /home/syoyo/work/stb/tests/pngsuite

.PHONY: all test pngsuite clean

all: test

test: $(TEST_BIN)
	./$(TEST_BIN)

$(TEST_BIN): $(SRC) $(TEST_SRC)
	$(CC) $(CFLAGS) $(CPPFLAGS) $(SRC) $(TEST_SRC) -lm -lz -o $(TEST_BIN)

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
	rm -f $(TEST_BIN)
