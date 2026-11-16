/-
  Specification of the TGA loader core (src/nanoimage_tga_core.c).

  `tgaHeader` mirrors `ni_tga_header` check by check; `tgaPixels` mirrors
  `ni_tga_decode_into`: a sequential packet stream (raw or RLE) writing each
  pixel once at the origin-flipped destination. Error codes are the
  `NI_TGA_ERR_*` values of src/nanoimage_core.h.
-/
import NANO.Basic
import NANO.Spec

namespace NANO

/-- The fields of `ni_tga_info`. -/
structure TgaInfo where
  outputSize : Nat
  dataOffset : Nat
  width : Nat
  height : Nat
  channels : Nat
  rle : Nat
  topOrigin : Nat
  rightOrigin : Nat
  deriving Repr, DecidableEq

/-- The header fields and validation, in the C's order. -/
def tgaHeader (size : Nat) (d : List UInt8) : Except Nat TgaInfo := do
  if size < 18 then throw 1
  let idLength : Nat := byteAt d 0
  let colorMapType : Nat := byteAt d 1
  let imageType : Nat := byteAt d 2
  let width : Nat := rd16le d 12
  let height : Nat := rd16le d 14
  let pixelDepth : Nat := byteAt d 16
  let descriptor : Nat := byteAt d 17
  if width = 0 ∨ height = 0 then throw 2
  if colorMapType ≠ 0 then throw 3
  if imageType ≠ 2 ∧ imageType ≠ 3 ∧ imageType ≠ 10 ∧ imageType ≠ 11 then throw 4
  let channels ←
    if imageType = 3 ∨ imageType = 11 then
      if pixelDepth ≠ 8 then throw 5 else pure 1
    else if pixelDepth = 24 then pure 3
    else if pixelDepth = 32 then pure 4
    else throw 5
  if 18 + idLength > size then throw 6
  if !sizeMulOK width height then throw 7
  let outputSize := width * height
  if !sizeMulOK outputSize channels then throw 7
  pure { outputSize := outputSize * channels, dataOffset := 18 + idLength,
         width, height, channels,
         rle := if imageType = 10 ∨ imageType = 11 then 1 else 0,
         topOrigin := if descriptor &&& 0x20 ≠ 0 then 1 else 0,
         rightOrigin := if descriptor &&& 0x10 ≠ 0 then 1 else 0 }

/-- The header verdict as a C error code (0 on success). -/
def tgaHeaderCode (size : Nat) (d : List UInt8) : Nat :=
  match tgaHeader size d with
  | .ok _ => 0
  | .error c => c

/-- The bytes one pixel writes, from the C's `ni_tga_write_pixel`. -/
def tgaPixelOut (channels : Nat) (s0 s1 s2 s3 : UInt8) : List UInt8 :=
  if channels = 1 then [s0]
  else if channels = 3 then [s2, s1, s0]
  else if channels = 4 then [s2, s1, s0, s3]
  else []

/-- Destination byte offset of source pixel `pixelIndex`. -/
def tgaDstIndex (h : TgaInfo) (pixelIndex : Nat) : Nat :=
  let x := pixelIndex % h.width
  let y := pixelIndex / h.width
  let dstX := if h.rightOrigin ≠ 0 then h.width - 1 - x else x
  let dstY := if h.topOrigin ≠ 0 then y else h.height - 1 - y
  (dstY * h.width + dstX) * h.channels

/-- One output write: first byte position and bytes. -/
abbrev TgaWrite : Type := Nat × List UInt8

/-- The pixel stream: mirrors `ni_tga_decode_into`'s two loops, collecting
    the ordered writes (byte position, bytes). `fuel` is the pixel count (each
    packet consumes at least one pixel, so it never runs out). -/
def tgaWritesAux (d : List UInt8) (h : TgaInfo) :
    Nat → Nat → Nat → List TgaWrite → Except Nat (List TgaWrite)
  | 0, _left, _off, acc => pure acc
  | fuel + 1, left, off, acc =>
      if left = 0 then pure acc
      else do
        let (count, packetHeader, off1) ←
          if h.rle ≠ 0 then do
            if off ≥ d.length then throw 8
            let bh := byteAt d off
            pure ((bh &&& 0x7f) + 1, bh, off + 1)
          else pure (1, 0, off)
        if count > left then throw 9
        let (s0, s1, s2, s3, off2) ←
          if h.rle = 0 ∨ (packetHeader &&& 0x80) ≠ 0 then do
            if off1 + h.channels > d.length then throw 10
            pure (d.getD off1 0, d.getD (off1 + 1) 0, d.getD (off1 + 2) 0,
                  d.getD (off1 + 3) 0, off1 + h.channels)
          else pure (0, 0, 0, 255, off1)
        let start := h.width * h.height - left
        let isRaw := h.rle ≠ 0 ∧ (packetHeader &&& 0x80) = 0
        let res ← (List.range count).foldlM
          (fun (st : Nat × List TgaWrite) i =>
            let (offI, accI) := st
            if isRaw then do
              if offI + h.channels > d.length then throw 11
              pure (offI + h.channels,
                    accI ++ [(tgaDstIndex h (start + i),
                              tgaPixelOut h.channels (d.getD offI 0) (d.getD (offI + 1) 0)
                                (d.getD (offI + 2) 0) (d.getD (offI + 3) 0))])
            else
              pure (offI, accI ++ [(tgaDstIndex h (start + i),
                                    tgaPixelOut h.channels s0 s1 s2 s3)]))
          (off2, acc)
        tgaWritesAux d h fuel (left - count) res.1 res.2

/-- All the writes for the image. -/
def tgaWrites (d : List UInt8) (h : TgaInfo) : Except Nat (List TgaWrite) :=
  tgaWritesAux d h (h.width * h.height) (h.width * h.height) h.dataOffset []

/-- Write one ordered chunk into the buffer. -/
def tgaWriteAt (buf : List UInt8) (w : TgaWrite) : List UInt8 :=
  let (i, bs) := w
  (List.range bs.length).foldl (fun b k => b.set (i + k) (bs.getD k 0)) buf

/-- Materialise the writes into a zero-initialised buffer. -/
def tgaMaterialize (n : Nat) (ws : List TgaWrite) : List UInt8 :=
  ws.foldl tgaWriteAt (List.replicate n 0)

/-- The decoded image bytes. -/
def tgaPixels (d : List UInt8) (h : TgaInfo) : Except Nat (List UInt8) := do
  let ws ← tgaWrites d h
  pure (tgaMaterialize h.outputSize ws)

/-- Header and pixels, as `ni_load_tga_from_memory` computes them. -/
def tgaDecode (d : List UInt8) : Except Nat (List UInt8) := do
  let h ← tgaHeader d.length d
  tgaPixels d h

end NANO
