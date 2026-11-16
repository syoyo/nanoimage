#!/usr/bin/env python3
"""Three-way differential test of the verified core:

  real C (compiled, ASan/UBSan)  ==  MiniC semantics of the translated C  ==  Lean spec

Validates the trusted parts of the C-to-Lean pipeline (translator and MiniC
semantics) against the real compiler, and the spec against both.

Usage: python3 formal/tools/cdiff.py [--n N] [--seed S]
"""
import os
import random
import struct
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
FORMAL = os.path.join(ROOT, "formal")


def u32(v):
    return struct.pack("<I", v & 0xFFFFFFFF)


def hexb(rng, n):
    return bytes(rng.randint(0, 255) for _ in range(n)).hex()


def bmp_file(rng):
    """A BMP file, mostly well formed, with header and payload mutations."""
    w = rng.choice([1, 2, 3, 4, 5, 7, 8, rng.randint(1, 12)])
    h = rng.choice([1, 2, 3, 4, 6, rng.randint(1, 10)])
    bit = rng.choice([8, 8, 24, 24, 32, 32, 1, 4, 16])
    top_down = rng.random() < 0.3
    dib = rng.choice([40, 40, 40, 52, 56, 108, 124, rng.randint(0, 60)])
    comp = rng.choice([0] * 12 + [1, 3])
    colors = rng.choice([0, 0, 0, 2, 16, 256, rng.randint(0, 300)])
    planes = 1 if rng.random() < 0.95 else rng.choice([0, 2])
    width = w
    height = -h if top_down else h
    if rng.random() < 0.03:
        height = -2147483648
    if rng.random() < 0.03:
        width = rng.choice([0, -3, 2147483647])
    entries = (colors if colors else 256) if bit == 8 else 0
    pal = bytes(rng.randint(0, 255) for _ in range(entries * 4 if bit == 8 else 0))
    pix_off = 14 + dib + len(pal)
    if rng.random() < 0.1:
        pix_off += rng.choice([-1, 1, 4, 100])
    stride = ((w * bit + 31) // 32) * 4
    body = bytes(rng.randint(0, 255) for _ in range(stride * h + 8))
    if bit == 8 and rng.random() < 0.5:
        body = bytes(rng.randint(0, min(entries, 255)) if entries else 0 for _ in range(len(body)))
    dib_hdr = (u32(dib) + struct.pack("<i", width) + struct.pack("<i", height)
               + struct.pack("<H", planes) + struct.pack("<H", bit) + u32(comp)
               + u32(0) + u32(0) + u32(0) + u32(colors) + u32(0))
    dib_hdr = (dib_hdr + b"\0" * dib)[:dib]
    if dib < 40:
        dib_hdr = dib_hdr[:dib]
    file_hdr = b"BM" + u32(0) + u32(0) + u32(max(pix_off, 0))
    data = file_hdr + dib_hdr + pal + body
    data = data[:max(0, min(len(data), pix_off + stride * h + 8))]
    if rng.random() < 0.15 and len(data) > 0:
        data = data[: rng.randint(0, len(data))]
    if rng.random() < 0.15 and len(data) > 0:
        data = bytearray(data)
        data[rng.randrange(len(data))] ^= 1 << rng.randrange(8)
        data = bytes(data)
    return data


def bmp_cases(rng, n):
    out = []
    for _ in range(n):
        d = bmp_file(rng).hex()
        out.append("bmp_geometry " + d)
        out.append("bmp_header " + d)
        out.append("bmp_decode " + d)
    return out


def tga_file(rng):
    """A TGA file, mostly well formed, with header and payload mutations."""
    w = rng.choice([1, 2, 3, 4, 5, 7, 8, rng.randint(1, 12)])
    h = rng.choice([1, 2, 3, 4, 6, rng.randint(1, 10)])
    image_type = rng.choice([2, 2, 3, 10, 10, 11, rng.choice([0, 1, 4, 32])])
    depth = rng.choice([24, 24, 32, 32, 8, 8, rng.choice([15, 16, 1])])
    descriptor = rng.choice([0, 0x20, 0x10, 0x30, rng.randint(0, 255)])
    id_len = rng.choice([0, 0, rng.randint(0, 5), rng.randint(0, 40)])
    cmap = 0 if rng.random() < 0.9 else rng.choice([1, 2])
    hdr = (bytes([id_len, cmap, image_type])
           + bytes(rng.randint(0, 255) for _ in range(9))
           + struct.pack("<HH", w, h) + bytes([depth, descriptor]))
    idb = bytes(rng.randint(0, 255) for _ in range(id_len))
    if (image_type in (3, 11)) and depth == 8:
        ch = 1
    elif depth == 24:
        ch = 3
    elif depth == 32:
        ch = 4
    else:
        ch = 1
    n = w * h
    rle = image_type in (10, 11)
    body = b""
    if rle:
        left = n
        while left > 0:
            run = rng.random() < 0.5
            cnt = rng.randint(1, min(128, left))
            if rng.random() < 0.08:
                cnt = min(128, left + rng.choice([1, 2]))  # overrun mutation
            hb = (cnt - 1) | (0x80 if run else 0)
            body += bytes([hb])
            if run:
                body += bytes(rng.randint(0, 255) for _ in range(ch))
            else:
                body += bytes(rng.randint(0, 255) for _ in range(cnt * ch))
            left -= min(cnt, left)
    else:
        body = bytes(rng.randint(0, 255) for _ in range(n * ch))
    data = hdr + idb + body
    if rng.random() < 0.15 and len(data) > 0:
        data = data[: rng.randint(0, len(data))]
    if rng.random() < 0.15 and len(data) > 0:
        data = bytearray(data)
        data[rng.randrange(len(data))] ^= 1 << rng.randrange(8)
        data = bytes(data)
    return data


def tga_cases(rng, n):
    out = []
    for _ in range(n):
        d = tga_file(rng).hex()
        out.append("tga_header " + d)
        out.append("tga_decode " + d)
    return out


def cases(rng, n):
    out = []
    # Big-endian readers: exact reads + trailing bytes.
    for _ in range(n):
        out.append("u16le " + hexb(rng, 2) + (hexb(rng, rng.randint(0, 4)) if rng.random() < 0.3 else ""))
        out.append("u32le " + hexb(rng, 4) + (hexb(rng, rng.randint(0, 4)) if rng.random() < 0.3 else ""))
        out.append("i32le " + hexb(rng, 4))
        out.append("u16be " + hexb(rng, 2) + (hexb(rng, rng.randint(0, 4)) if rng.random() < 0.3 else ""))
        out.append("u32be " + hexb(rng, 4) + (hexb(rng, rng.randint(0, 4)) if rng.random() < 0.3 else ""))
    # Boundary-focused size arithmetic.
    edge = [0, 1, 2, 0xFFFFFFFF, 0x100000000, 2**32 - 1, 2**32, 2**63 - 1, 2**63, 2**64 - 1, 2**64 - 2]
    for _ in range(n):
        out.append(f"size_mul {edge[rng.randrange(len(edge))]} {edge[rng.randrange(len(edge))]}")
        out.append(f"size_add {edge[rng.randrange(len(edge))]} {edge[rng.randrange(len(edge))]}")
    # Clamp.
    for _ in range(n):
        out.append(f"clamp_u8 {rng.choice([rng.randint(-5, 300), 0, -2147483648, 2147483647, 254, 255, 256])}")
    # Scale to 8-bit.
    for _ in range(n):
        out.append(f"scale_to_8bit {rng.choice([rng.randint(0, 65535), 0xFFFFFFFF, rng.randint(0, 2**32 - 1)])} {rng.choice([1, 2, 4, 8, 0, 9, 16])}")
    # Packed bits: random row, depth in {1,2,4,8}, in-range pixel index.
    for _ in range(n):
        depth = rng.choice([1, 2, 4, 8])
        rowlen = rng.choice([1, 2, 4, 8, 16])
        maxpix = rowlen * 8 // depth
        out.append(f"packed_bits {hexb(rng, rowlen)} {rng.randrange(max(maxpix, 1))} {depth}")
    # Paeth.
    for _ in range(n):
        out.append(f"paeth {rng.randint(0, 255)} {rng.randint(0, 255)} {rng.randint(0, 255)}")
    return out


def main():
    n = 300
    seed = 1
    args = sys.argv[1:]
    if "--n" in args:
        n = int(args[args.index("--n") + 1])
    if "--seed" in args:
        seed = int(args[args.index("--seed") + 1])
    rng = random.Random(seed)
    lines = cases(rng, n) + bmp_cases(rng, n) + tga_cases(rng, n)
    inp = "\n".join(lines) + "\n"
    with tempfile.TemporaryDirectory() as d:
        exe = os.path.join(d, "cdiff_c")
        subprocess.check_call([os.environ.get("CC", "cc"), "-std=c11", "-O1", "-w",
                               "-fsanitize=address,undefined", "-fno-sanitize-recover=all",
                               "-I" + ROOT, "-o", exe, os.path.join(FORMAL, "tools", "cdiff_c.c")])
        c_out = subprocess.run([exe], input=inp.encode(), capture_output=True, check=True).stdout.decode().splitlines()
    subprocess.check_call(["lake", "build", "cdiff"], cwd=FORMAL, stdout=subprocess.DEVNULL)
    lean_out = subprocess.run([os.path.join(FORMAL, ".lake", "build", "bin", "cdiff")], input=inp.encode(),
                              capture_output=True, check=True).stdout.decode().splitlines()
    bad = 0
    for line, c, l in zip(lines, c_out, lean_out):
        minic, spec = [x.strip() for x in l.split("|")]
        if not (c == minic == spec):
            bad += 1
            if bad <= 10:
                print(f"MISMATCH (case is reproducible with --n and --seed) {line[:120]}...\n  C:     {c}\n  MiniC: {minic}\n  spec:  {spec}")
    if len(c_out) != len(lines) or len(lean_out) != len(lines):
        print(f"output length mismatch (c: {len(c_out)}, lean: {len(lean_out)}, expected {len(lines)})")
        return 1
    print(f"cdiff: {len(lines)} cases, {bad} mismatches")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
