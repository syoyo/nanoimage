CC ?= cc
CFLAGS ?= -std=c11 -O2 -Wall -Wextra -Werror -pedantic
CPPFLAGS ?= -Iinclude

SRC = src/nanoimage_alloc.c src/nanoimage_zlib.c src/nanoimage_png.c src/nanoimage_jpeg.c
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
#   - Files NOT in corrupt/  must decode successfully  (pass = success)
#   - Files inside  corrupt/ must be rejected by decoder (pass = failure)
pngsuite: $(EXAMPLE_BIN)
	@pass=0; fail=0; \
	for f in $$(find $(PNGSUITE_DIR) -name "*.png" ! -path "*/corrupt/*"); do \
	  if timeout 8s $(EXAMPLE_BIN) "$$f" >/dev/null 2>&1; then pass=$$((pass+1)); \
	  else echo "DECODE FAIL (should succeed): $$f"; fail=$$((fail+1)); fi; \
	done; \
	corrupt_pass=0; corrupt_fail=0; \
	for f in $(PNGSUITE_DIR)/corrupt/*.png; do \
	  if timeout 8s $(EXAMPLE_BIN) "$$f" >/dev/null 2>&1; then \
	    echo "UNEXPECTED SUCCESS (should fail): $$f"; corrupt_fail=$$((corrupt_fail+1)); \
	  else corrupt_pass=$$((corrupt_pass+1)); fi; \
	done; \
	echo "Valid PNGs:   $$pass pass, $$fail fail"; \
	echo "Corrupt PNGs: $$corrupt_pass correctly rejected, $$corrupt_fail wrongly accepted"; \
	if [ $$fail -ne 0 ] || [ $$corrupt_fail -ne 0 ]; then exit 1; fi

clean:
	rm -f $(TEST_BIN)
