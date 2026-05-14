CC ?= cc
CFLAGS ?= -std=c11 -O2 -Wall -Wextra -Werror -pedantic
CPPFLAGS ?= -Iinclude

SRC = src/nanoimage_zlib.c src/nanoimage_png.c src/nanoimage_jpeg.c
TEST_SRC = tests/test_nanoimage.c
TEST_BIN = tests/test_nanoimage

.PHONY: all test clean

all: test

test: $(TEST_BIN)
	./$(TEST_BIN)

$(TEST_BIN): $(SRC) $(TEST_SRC)
	$(CC) $(CFLAGS) $(CPPFLAGS) $(SRC) $(TEST_SRC) -lm -o $(TEST_BIN)

clean:
	rm -f $(TEST_BIN)
