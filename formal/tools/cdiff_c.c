/* Differential-testing harness: runs the real compiled verified-core C
 * functions on the inputs read from stdin (same format as formal/CDiff.lean).
 * Build with ASan/UBSan (formal/tools/cdiff.py does). */
#include "../../src/nanoimage_core.c"
#include "../../src/nanoimage_bmp_core.c"
#include <stdlib.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int hexval(int c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return c - 'A' + 10;
}

static int parsehex(const char *hex, size_t len, uint8_t *out) {
    for (size_t i = 0; i < len; ++i)
        out[i] = (uint8_t)(hexval(hex[2 * i]) * 16 + hexval(hex[2 * i + 1]));
    return 0;
}

int main(void) {
    static char line[1 << 20];
    while (fgets(line, sizeof(line), stdin)) {
        size_t n = strlen(line);
        while (n && (line[n - 1] == '\n' || line[n - 1] == '\r')) line[--n] = 0;
        char kind[32] = {0}, rest[1 << 20] = {0};
        if (sscanf(line, "%31s %[^\n]", kind, rest) == EOF) { puts("BADLINE"); continue; }
        if (strcmp(kind, "u16le") == 0 || strcmp(kind, "u32le") == 0 ||
            strcmp(kind, "i32le") == 0 || strcmp(kind, "u16be") == 0 ||
            strcmp(kind, "u32be") == 0) {
            size_t len = strlen(rest) / 2;
            uint8_t d[8192];
            if (len > sizeof(d)) { puts("BADLINE"); continue; }
            parsehex(rest, len, d);
            if (strcmp(kind, "u16le") == 0) printf("%u\n", (unsigned)ni_read_u16le(d));
            else if (strcmp(kind, "u32le") == 0) printf("%u\n", (unsigned)ni_read_u32le(d));
            else if (strcmp(kind, "i32le") == 0) printf("%u\n", (unsigned)ni_read_i32le(d));
            else if (strcmp(kind, "u16be") == 0) printf("%u\n", (unsigned)ni_read_u16be(d));
            else printf("%u\n", (unsigned)ni_read_u32be(d));
        } else if (strcmp(kind, "size_mul") == 0 || strcmp(kind, "size_add") == 0) {
            unsigned long long a = 0, b = 0;
            if (sscanf(rest, "%llu %llu", &a, &b) != 2) { puts("BADLINE"); continue; }
            size_t out = 12345;
            int r;
            if (strcmp(kind, "size_mul") == 0) r = ni_size_mul((size_t)a, (size_t)b, &out);
            else r = ni_size_add((size_t)a, (size_t)b, &out);
            if (r) printf("1 %llu\n", (unsigned long long)out);
            else printf("0\n");
        } else if (strcmp(kind, "clamp_u8") == 0) {
            int v = 0;
            if (sscanf(rest, "%d", &v) != 1) { puts("BADLINE"); continue; }
            printf("%u\n", (unsigned)ni_clamp_u8(v));
        } else if (strcmp(kind, "scale_to_8bit") == 0) {
            unsigned v = 0, depth = 0;
            if (sscanf(rest, "%u %u", &v, &depth) != 2) { puts("BADLINE"); continue; }
            uint8_t out = 0xAA;
            int r = ni_scale_to_8bit((uint32_t)v, (uint8_t)depth, &out);
            if (r) printf("1 %u\n", (unsigned)out);
            else printf("0\n");
        } else if (strcmp(kind, "packed_bits") == 0) {
            char rowhex[1 << 18] = {0};
            unsigned long long pi = 0;
            unsigned depth = 0;
            if (sscanf(rest, "%262143s %llu %u", rowhex, &pi, &depth) != 3) { puts("BADLINE"); continue; }
            size_t len = strlen(rowhex) / 2;
            uint8_t d[131072];
            if (len > sizeof(d)) { puts("BADLINE"); continue; }
            parsehex(rowhex, len, d);
            printf("%u\n", (unsigned)ni_read_packed_bits(d, (size_t)pi, (uint8_t)depth));
        } else if (strcmp(kind, "paeth") == 0) {
            unsigned a = 0, b = 0, c = 0;
            if (sscanf(rest, "%u %u %u", &a, &b, &c) != 3) { puts("BADLINE"); continue; }
            printf("%u\n", (unsigned)ni_paeth((uint8_t)a, (uint8_t)b, (uint8_t)c));
        } else if (strcmp(kind, "bmp_sig") == 0) {
            size_t len = strlen(rest) / 2;
            uint8_t *d = (uint8_t *)malloc(len ? len : 1);
            parsehex(rest, len, d);
            printf("%d\n", ni_bmp_sig_ok(d, len));
            free(d);
        } else if (strcmp(kind, "bmp_layout") == 0) {
            size_t len = strlen(rest) / 2;
            uint8_t *d = (uint8_t *)malloc(len ? len : 1);
            parsehex(rest, len, d);
            printf("%d\n", ni_bmp_layout_ok(d, len));
            free(d);
        } else if (strcmp(kind, "bmp_mulfits") == 0) {
            unsigned long long a = 0, b = 0;
            if (sscanf(rest, "%llu %llu", &a, &b) != 2) { puts("BADLINE"); continue; }
            printf("%d\n", ni_bmp_mul_fits((size_t)a, (size_t)b));
        } else if (strcmp(kind, "bmp_geometry") == 0) {
            size_t len = strlen(rest) / 2;
            uint8_t *d = (uint8_t *)malloc(len ? len : 1);
            ni_bmp_info info;
            int code;
            memset(&info, 0, sizeof(info));
            parsehex(rest, len, d);
            if (len < 54) { puts("SKIP"); free(d); continue; }
            code = ni_bmp_geometry(d, len, &info);
            if (code == NI_BMP_OK) {
                printf("0 %u %u %u %u %u\n", (unsigned)info.width, (unsigned)info.height,
                       (unsigned)info.bit_count, (unsigned)info.channels, (unsigned)info.top_down);
            } else {
                printf("%d\n", code);
            }
            free(d);
        } else if (strcmp(kind, "bmp_header") == 0) {
            size_t len = strlen(rest) / 2;
            uint8_t *d = (uint8_t *)malloc(len ? len : 1);
            ni_bmp_info info;
            int code;
            memset(&info, 0, sizeof(info));
            parsehex(rest, len, d);
            code = ni_bmp_header(d, len, &info);
            if (code == NI_BMP_OK) {
                printf("0 %zu %zu %zu %u %u %u %u %u %u %u\n", info.row_stride, info.output_size,
                       info.palette_offset, (unsigned)info.width, (unsigned)info.height,
                       (unsigned)info.pixel_offset, (unsigned)info.palette_entries,
                       (unsigned)info.bit_count, (unsigned)info.channels, (unsigned)info.top_down);
            } else {
                printf("%d\n", code);
            }
            free(d);
        } else if (strcmp(kind, "bmp_decode") == 0) {
            size_t len = strlen(rest) / 2;
            uint8_t *d = (uint8_t *)malloc(len ? len : 1);
            ni_bmp_info info;
            int code;
            memset(&info, 0, sizeof(info));
            parsehex(rest, len, d);
            code = ni_bmp_header(d, len, &info);
            if (code == NI_BMP_OK) {
                uint8_t *out = (uint8_t *)malloc(info.output_size ? info.output_size : 1);
                code = ni_bmp_decode_into(d, len, &info, out, info.output_size);
                if (code == NI_BMP_OK) {
                    size_t i;
                    printf("0 ");
                    for (i = 0; i < info.output_size; i++) printf("%02x", (unsigned)out[i]);
                    printf("\n");
                } else {
                    printf("%d\n", code);
                }
                free(out);
            } else {
                printf("%d\n", code);
            }
            free(d);
        } else {
            puts("BADLINE");
        }
    }
    return 0;
}
