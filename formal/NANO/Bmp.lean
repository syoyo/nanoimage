/-
  Specification of the BMP loader core (src/nanoimage_bmp_core.c).

  `bmpHeader` mirrors `ni_bmp_header` check by check, in the same order, so
  that the error codes agree. `bmpPixels` mirrors `ni_bmp_decode_into` for
  headers accepted by `bmpHeader`. Error codes are the `NI_BMP_ERR_*` values
  of src/nanoimage_core.h.
-/
import NANO.Basic
import NANO.Spec

namespace NANO

/-- The fields of `ni_bmp_info`. -/
structure BmpInfo where
  rowStride : Nat
  outSize : Nat
  paletteOffset : Nat
  width : Nat
  height : Nat
  pixelOffset : Nat
  paletteEntries : Nat
  bitCount : Nat
  channels : Nat
  topDown : Nat
  deriving Repr, DecidableEq

/-- Two's-complement reading of a 32-bit word (`int32_t` cast). -/
def toInt32 (n : Nat) : Int := if n ≥ 2 ^ 31 then (n : Int) - 2 ^ 32 else (n : Int)

/-- The signature guard of `ni_bmp_sig_ok` (short-circuit order is irrelevant
    for the value). -/
def sigOk (size : Nat) (d : List UInt8) : Bool :=
  decide (54 ≤ size) && decide (byteAt d 0 = 66) && decide (byteAt d 1 = 77)

/-- The layout guard of `ni_bmp_layout_ok` (C: returns 0 when it fails). -/
def layoutOk (size : Nat) (d : List UInt8) : Bool :=
  !(decide (rd32le d 14 < 40) || decide (14 + rd32le d 14 > size) ||
    decide (rd32le d 10 < 14 + rd32le d 14) || decide (rd32le d 10 > size))

/-- `ni_bmp_geometry`: the geometry verdict. -/
def bmpGeometry (d : List UInt8) : Except Nat (Nat × Nat × Nat × Nat × Nat) := do
  let size := d.length
  let widthI := toInt32 (rd32le d 18)
  let heightI := toInt32 (rd32le d 22)
  let planes := rd16le d 26
  let bitCount := rd16le d 28
  let compression := rd32le d 30
  if widthI ≤ 0 ∨ heightI = 0 ∨ planes ≠ 1 then throw 3
  let t := heightI < 0
  if t then
    if heightI = -2147483648 then throw 4
    else
      if compression ≠ 0 then throw 5
      else if bitCount ≠ 8 ∧ bitCount ≠ 24 ∧ bitCount ≠ 32 then throw 6
      else
        let width : Nat := widthI.toNat
        let height : Nat := (-heightI).toNat
        let channels : Nat := if bitCount = 32 then 4 else 3
        return (width, height, bitCount, channels, 1)
  else
    if compression ≠ 0 then throw 5
    else if bitCount ≠ 8 ∧ bitCount ≠ 24 ∧ bitCount ≠ 32 then throw 6
    else
      let width : Nat := widthI.toNat
      let height : Nat := heightI.toNat
      let channels : Nat := if bitCount = 32 then 4 else 3
      return (width, height, bitCount, channels, 0)

/-- The error code `ni_bmp_geometry` returns (0 on success, else the NI_BMP_* code). -/
def bmpGeometryCode (d : List UInt8) : Nat :=
  let widthI := toInt32 (rd32le d 18)
  let heightI := toInt32 (rd32le d 22)
  let planes := rd16le d 26
  let bitCount := rd16le d 28
  let compression := rd32le d 30
  if widthI ≤ 0 ∨ heightI = 0 ∨ planes ≠ 1 then 3
  else if heightI < 0 then
    if heightI = -2147483648 then 4
    else if compression ≠ 0 then 5
    else if bitCount ≠ 8 ∧ bitCount ≠ 24 ∧ bitCount ≠ 32 then 6
    else 0
  else
    if compression ≠ 0 then 5
    else if bitCount ≠ 8 ∧ bitCount ≠ 24 ∧ bitCount ≠ 32 then 6
    else 0

/-- Stage 1 of `bmpHeader`: the signature check (`ni_bmp_sig_ok`). -/
def bmpSigGate (size : Nat) (d : List UInt8) : Except Nat Unit :=
  if size < 54 ∨ byteAt d 0 ≠ 66 ∨ byteAt d 1 ≠ 77 then throw 1 else pure ()

/-- Stage 2 of `bmpHeader`: the layout check (`ni_bmp_layout_ok`). -/
def bmpLayoutGate (size : Nat) (d : List UInt8) : Except Nat Unit :=
  let pixelOffset := rd32le d 10
  let dib := rd32le d 14
  if dib < 40 ∨ 14 + dib > size ∨ pixelOffset < 14 + dib ∨ pixelOffset > size then throw 2 else pure ()

/-- Stage 3 of `bmpHeader`: geometry validation (`ni_bmp_geometry`). -/
def bmpGeometryStage (size : Nat) (d : List UInt8) :
    Except Nat (Nat × Nat × Nat × Nat × Nat × Nat) := do
  let widthI := toInt32 (rd32le d 18)
  let heightI := toInt32 (rd32le d 22)
  let planes := rd16le d 26
  let bitCount := rd16le d 28
  let compression := rd32le d 30
  let colorsUsed := rd32le d 46
  if widthI ≤ 0 ∨ heightI = 0 ∨ planes ≠ 1 then throw 3
  if heightI < 0 then
    if heightI = -2147483648 then throw 4
    let height : Nat := heightI.natAbs
    let width : Nat := widthI.toNat
    if compression ≠ 0 then throw 5
    if bitCount ≠ 8 ∧ bitCount ≠ 24 ∧ bitCount ≠ 32 then throw 6
    let channels : Nat := if bitCount = 32 then 4 else 3
    pure (width, height, bitCount, channels, 1, colorsUsed)
  else
    let height : Nat := heightI.natAbs
    let width : Nat := widthI.toNat
    if compression ≠ 0 then throw 5
    if bitCount ≠ 8 ∧ bitCount ≠ 24 ∧ bitCount ≠ 32 then throw 6
    let channels : Nat := if bitCount = 32 then 4 else 3
    pure (width, height, bitCount, channels, 0, colorsUsed)

/-- Stage 4 of `bmpHeader`: arithmetic, truncation and palette checks. -/
def bmpOutputCompose (size : Nat) (d : List UInt8)
    (h : Nat × Nat × Nat × Nat × Nat × Nat) : Except Nat BmpInfo := do
  let (width, height, bitCount, channels, topDown, colorsUsed) := h
  if !sizeMulOK width bitCount then throw 7
  let rowStride : Nat := ((width * bitCount + 31) / 32) * 4
  if !sizeMulOK width channels then throw 8
  let outStride := width * channels
  if !sizeMulOK outStride height then throw 8
  let outSize := outStride * height
  if !sizeMulOK rowStride height then throw 9
  let rowsBytes := rowStride * height
  let pixelOffset := rd32le d 10
  if pixelOffset > sizeMax - rowsBytes ∨ pixelOffset + rowsBytes > size then throw 9
  if bitCount = 8 then
    let entries : Nat := if colorsUsed ≠ 0 then colorsUsed else 256
    let dib := rd32le d 14
    let paletteOffset := 14 + dib
    if entries = 0 ∨ entries > 256 ∨ paletteOffset + entries * 4 > pixelOffset then throw 10
    return { rowStride, outSize, paletteOffset, width, height, pixelOffset,
             paletteEntries := entries, bitCount, channels, topDown }
  else
    return { rowStride, outSize, paletteOffset := 0, width, height, pixelOffset,
             paletteEntries := 0, bitCount, channels, topDown }

/-- Row stride of a BMP row: 4-byte aligned. -/
def bmpRowStride (width bitCount : Nat) : Nat := ((width * bitCount + 31) / 32) * 4

/-- Total output size for a header accepted by `ni_bmp_header_arith`. -/
def bmpOutSize (width channels height : Nat) : Nat := width * channels * height

/-- Stage 4a verdict of `ni_bmp_header_arith`: the arithmetic, output-size and
    truncation checks of `bmpOutputCompose`, as a C error code. -/
def bmpOutputArithCode (width height bitCount channels pixelOffset size : Nat) : Nat :=
  if !sizeMulOK width bitCount then 7
  else
    let rowStride := bmpRowStride width bitCount
    if !sizeMulOK width channels then 8
    else
      let outStride := width * channels
      if !sizeMulOK outStride height then 8
      else
        let rowsBytes := rowStride * height
        if !sizeMulOK rowStride height then 9
        else if pixelOffset > sizeMax - rowsBytes ∨ pixelOffset + rowsBytes > size then 9
        else 0

/-- Stage 4b verdict of `ni_bmp_header_palette`: the 8-bit palette bounds
    check of `bmpOutputCompose`, as a C error code. -/
def bmpOutputPaletteCode (bitCount colorsUsed dibSize pixelOffset : Nat) : Nat :=
  if bitCount = 8 then
    let entries : Nat := if colorsUsed = 0 then 256 else colorsUsed
    let paletteOffset := 14 + dibSize
    if entries = 0 ∨ entries > 256 ∨ paletteOffset + entries * 4 > pixelOffset then 10 else 0
  else 0

/-- `ni_bmp_header`: signature, layout, geometry, arithmetic and palette
    checks in that order (the C does the same). -/
def bmpHeader (size : Nat) (d : List UInt8) : Except Nat BmpInfo := do
  bmpSigGate size d
  bmpLayoutGate size d
  let h ← bmpGeometryStage size d
  bmpOutputCompose size d h

/-- Output pixel `(y, x)` of a header accepted by `bmpHeader`:
    8-bit palette entries are expanded to BGR, 24/32-bit pixels are swapped
    from BGR(A) to RGB(A). Error 11 for an out-of-range palette index. -/
def bmpPixel (d : List UInt8) (h : BmpInfo) (y x : Nat) : Except Nat (List UInt8) := do
  let srcY := if h.topDown = 1 then y else h.height - 1 - y
  let base := h.pixelOffset + srcY * h.rowStride
  if h.bitCount = 8 then
    let idx := byteAt d (base + x)
    if idx ≥ h.paletteEntries then throw 11
    let p := h.paletteOffset + idx * 4
    return [d.getD (p + 2) 0, d.getD (p + 1) 0, d.getD p 0]
  else
    let srcCh := if h.bitCount = 32 then 4 else 3
    let s := base + x * srcCh
    if h.channels = 4 then
      return [d.getD (s + 2) 0, d.getD (s + 1) 0, d.getD s 0, d.getD (s + 3) 0]
    else
      return [d.getD (s + 2) 0, d.getD (s + 1) 0, d.getD s 0]

/-- The header verdict as a C error code (`NI_BMP_ERR_*`; 0 on success).
    Exactly `bmpHeader` with the info block discarded. -/
def bmpHeaderCode (size : Nat) (d : List UInt8) : Nat :=
  match bmpHeader size d with
  | .ok _ => 0
  | .error c => c

/-- All output pixels, row by row. -/
def bmpPixels (d : List UInt8) (h : BmpInfo) : Except Nat (List UInt8) := do
  let rows ← (List.range h.height).mapM fun y =>
    (List.range h.width).mapM fun x => bmpPixel d h y x
  return rows.flatten.flatten

/-- Header and pixels, as `ni_load_bmp_from_memory` computes them. -/
def bmpDecode (d : List UInt8) : Except Nat (List UInt8) := do
  let h ← bmpHeader d.length d
  bmpPixels d h

end NANO


