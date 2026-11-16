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

/-! ## Flattened output (used by the `ni_bmp_decode_into` refinement proof) -/

/-- Bytes one output pixel expands to. -/
def bmpPixelSize (h : BmpInfo) : Nat := if h.bitCount = 8 then 3 else h.channels

/-- Bytes per output row. -/
def bmpRowSize (h : BmpInfo) : Nat := h.width * bmpPixelSize h

/-- Flattened bytes of output row `y` (`[]` for pixels whose decode failed). -/
def bmpRowBytes (d : List UInt8) (h : BmpInfo) (y : Nat) : List UInt8 :=
  (List.range h.width).flatMap fun x =>
    match bmpPixel d h y x with
    | .ok bs => bs
    | .error _ => []

/-- Flattened bytes of the first `y` output rows. -/
def bmpRowsBytes (d : List UInt8) (h : BmpInfo) (y : Nat) : List UInt8 :=
  (List.range y).flatMap (bmpRowBytes d h)

/-- `bmpRowsBytes` peels one row off the back. -/
theorem bmpRowsBytes_succ (d : List UInt8) (h : BmpInfo) (y : Nat) :
    bmpRowsBytes d h (y + 1) = bmpRowsBytes d h y ++ bmpRowBytes d h y := by
  unfold bmpRowsBytes
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem bmpRowsBytes_zero (d : List UInt8) (h : BmpInfo) :
    bmpRowsBytes d h 0 = [] := rfl

/-- Length of a row: `h.width` pixels of `bmpPixelSize h` bytes each. -/
theorem bmpRowBytes_length (d : List UInt8) (h : BmpInfo) (y : Nat)
    (hok : ∀ x, x < h.width → ∃ bs, bmpPixel d h y x = .ok bs)
    (hlen : ∀ x bs, bmpPixel d h y x = .ok bs → bs.length = bmpPixelSize h) :
    (bmpRowBytes d h y).length = bmpRowSize h := by
  unfold bmpRowBytes bmpRowSize
  rw [List.length_flatMap]
  rw [List.map_congr_left (g := fun _ => bmpPixelSize h) (l := List.range h.width)]
  · rw [List.map_const', List.length_range, List.sum_replicate_nat]
  · intro x hx
    have hx' : x < h.width := by
      rw [List.mem_range] at hx; exact hx
    obtain ⟨bs, hbs⟩ := hok x hx'
    simp [hbs, hlen x bs hbs]

/-- Length of the first `y` rows. -/
theorem bmpRowsBytes_length (d : List UInt8) (h : BmpInfo) (y : Nat)
    (hy : y ≤ h.height)
    (hok : ∀ yy x, yy < y → x < h.width → ∃ bs, bmpPixel d h yy x = .ok bs)
    (hlen : ∀ yy x bs, bmpPixel d h yy x = .ok bs → bs.length = bmpPixelSize h) :
    (bmpRowsBytes d h y).length = y * bmpRowSize h := by
  induction y with
  | zero => simp [bmpRowsBytes]
  | succ k ih =>
    rw [bmpRowsBytes_succ, List.length_append, ih (by omega)
      (fun yy x hyy hx => hok yy x (by omega) hx)]
    rw [bmpRowBytes_length d h k (fun x hx => hok k x (by omega) hx)
      (fun x bs hbs => hlen k x bs hbs)]
    rw [Nat.add_mul, Nat.one_mul]

/-- Bytes one pixel expands to, bounded by the header's channel count. -/
theorem bmpPixelSize_le (h : BmpInfo) (hc : h.channels ≤ 4) : bmpPixelSize h ≤ 4 := by
  unfold bmpPixelSize
  split
  · omega
  · assumption


/-! ## Byte-level bridge lemmas (used by the `ni_bmp_decode_into` proof) -/

/-- `byteAt` round-trips to the byte in the list. -/
theorem byteAt_toUInt8 (d : List UInt8) (i : Nat) :
    (byteAt d i).toUInt8 = d.getD i 0 := by
  unfold byteAt
  simp

/-- The output expansion list of one 8-bit palette pixel. -/
theorem bmpPixel_palette (d : List UInt8) (h : BmpInfo) (y x : Nat)
    (hd8 : h.bitCount = 8)
    (hidx : byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) < h.paletteEntries) :
    bmpPixel d h y x =
      .ok [d.getD (h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4 + 2) 0,
           d.getD (h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4 + 1) 0,
           d.getD (h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4) 0] := by
  unfold bmpPixel
  rw [ite_eq_left hd8]
  dsimp only
  by_cases hge : byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) ≥ h.paletteEntries
  · exact absurd hge (by omega)
  · simp only [hge]
    rfl

/-- Prefix decomposition of `range`-`flatMap`. -/
theorem flatMap_range_prefix (f : Nat → List UInt8) (n : Nat) :
    ∀ m, m ≤ n → (List.range n).flatMap f =
      (List.range m).flatMap f ++ (List.range (n - m)).flatMap (fun i => f (m + i)) := by
  induction n with
  | zero =>
      intro m h
      have : m = 0 := by omega
      rw [this]
      simp
  | succ k ih =>
      intro m h
      by_cases hmk : m ≤ k
      · rw [List.range_succ, List.flatMap_append, ih m hmk]
        have e : k + 1 - m = (k - m) + 1 := by omega
        rw [e, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.flatMap_singleton]
        have e2 : m + (k - m) = k := by omega
        rw [e2, ← List.append_assoc]
      · have hmk' : m = k + 1 := by omega
        rw [hmk']
        simp [List.range_succ]


/-- `flatten` of `map f` is `flatMap f`. -/
theorem flatten_map' {α β : Type} (f : α → List β) (l : List α) :
    (l.map f).flatten = l.flatMap f := by
  rw [List.flatten_eq_flatMap, List.flatMap_map]
  rfl

/-- `flatten` of `flatMap f` is `flatMap (flatten ∘ f)`. -/
theorem flatten_flatMap' {α β : Type} (f : α → List (List β)) (l : List α) :
    (l.flatMap f).flatten = l.flatMap (fun a => (f a).flatten) := by
  rw [List.flatMap, List.flatten_flatten, List.map_map]
  rfl

/-- One output row decodes successfully iff every pixel does; in that case the
    row decodes to the list of pixel expansions. -/
theorem mapM_row_ok (d : List UInt8) (h : BmpInfo) (y : Nat) (n : Nat)
    (hok : ∀ x, x < n → ∃ bs, bmpPixel d h y x = .ok bs) :
    (List.range n).mapM (fun x => bmpPixel d h y x)
      = Except.ok ((List.range n).map fun x => match bmpPixel d h y x with | .ok bs => bs | .error _ => []) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.mapM_append, List.mapM_cons]
      rw [ih (fun x hx => hok x (by omega))]
      obtain ⟨bs, hbs⟩ := hok k (by omega)
      rw [List.map_append, List.map_cons, List.map_nil]
      rw [hbs]
      rfl

theorem mapM_row (d : List UInt8) (h : BmpInfo) (y : Nat)
    (hok : ∀ x, x < h.width → ∃ bs, bmpPixel d h y x = .ok bs) :
    (List.range h.width).mapM (fun x => bmpPixel d h y x)
      = Except.ok ((List.range h.width).map fun x => match bmpPixel d h y x with | .ok bs => bs | .error _ => []) :=
  mapM_row_ok d h y h.width hok

/-- All output rows decode successfully iff every pixel does. -/
theorem mapM_rows_ok (d : List UInt8) (h : BmpInfo) (n : Nat)
    (hok : ∀ y x, y < n → x < h.width → ∃ bs, bmpPixel d h y x = .ok bs) :
    (List.range n).mapM (fun y => (List.range h.width).mapM fun x => bmpPixel d h y x)
      = Except.ok ((List.range n).map fun y => (List.range h.width).map fun x => match bmpPixel d h y x with | .ok bs => bs | .error _ => []) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.mapM_append, List.mapM_cons]
      rw [ih (fun y x hy hx => hok y x (by omega) hx)]
      rw [mapM_row d h k (fun x hx => hok k x (by omega) hx)]
      rw [List.map_append, List.map_cons, List.map_nil]
      rfl

/-- The output expansion of one direct (BGR or BGRA) pixel. -/
theorem bmpPixel_direct (d : List UInt8) (h : BmpInfo) (y x : Nat)
    (hn8 : h.bitCount ≠ 8) :
    bmpPixel d h y x =
      (if h.channels = 4 then
         .ok ([d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 2) 0,
               d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 1) 0,
               d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 0) 0,
               d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 3) 0])
       else
         .ok ([d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 2) 0,
               d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 1) 0,
               d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 0) 0])) := by
  unfold bmpPixel
  rw [ite_eq_right hn8]
  dsimp only
  rfl

/-- `bmpPixels` flattens to the concatenated row bytes when every pixel decodes. -/
theorem bmpPixels_eq_rowsBytes (d : List UInt8) (h : BmpInfo)
    (hok : ∀ y x, y < h.height → x < h.width → ∃ bs, bmpPixel d h y x = .ok bs) :
    bmpPixels d h = .ok (bmpRowsBytes d h h.height) := by
  unfold bmpPixels bmpRowsBytes bmpRowBytes
  rw [mapM_rows_ok d h h.height hok]
  show ((Except.ok ((List.range h.height).map fun y => (List.range h.width).map fun x => match bmpPixel d h y x with | .ok bs => bs | .error _ => [])).bind (fun rows => Except.ok rows.flatten.flatten)) =
      Except.ok ((List.range h.height).flatMap fun y => (List.range h.width).flatMap fun x => match bmpPixel d h y x with | .ok bs => bs | .error _ => [])
  show Except.ok ((List.range h.height).map fun y => (List.range h.width).map fun x => match bmpPixel d h y x with | .ok bs => bs | .error _ => []).flatten.flatten =
      Except.ok ((List.range h.height).flatMap fun y => (List.range h.width).flatMap fun x => match bmpPixel d h y x with | .ok bs => bs | .error _ => [])
  congr 1
  simp only [flatten_map', flatten_flatMap']


/-- The flattened bytes of pixels `0..n-1` of row `y`. -/
def rowOut (d : List UInt8) (h : BmpInfo) (y n : Nat) : List UInt8 :=
  (List.range n).flatMap fun i => match bmpPixel d h y i with | .ok bs => bs | .error _ => []

/-- Length of a pixel-prefix of a row's bytes. -/
theorem rowOut_length (d : List UInt8) (h : BmpInfo) (y n : Nat)
    (hok : ∀ i, i < n → ∃ bs, bmpPixel d h y i = .ok bs)
    (hlen : ∀ i bs, bmpPixel d h y i = .ok bs → bs.length = bmpPixelSize h) :
    (rowOut d h y n).length = n * bmpPixelSize h := by
  unfold rowOut
  rw [List.length_flatMap]
  rw [List.map_congr_left (g := fun _ => bmpPixelSize h) (l := List.range n)]
  · rw [List.map_const', List.length_range, List.sum_replicate_nat]
  · intro x hx
    rw [List.mem_range] at hx
    obtain ⟨bs, hbs⟩ := hok x hx
    rw [hbs]
    exact hlen x bs hbs

/-- First `n` pixels of a row as bytes, appended to a prefix (`flatMap_range_prefix`
    specialized to `bmpPixel`). -/
theorem rowOut_prefix (d : List UInt8) (h : BmpInfo) (y n m : Nat)
    (hmn : m ≤ n) :
    (List.range n).flatMap (fun i => match bmpPixel d h y i with | .ok bs => bs | .error _ => [])
      = rowOut d h y m ++ (List.range (n - m)).flatMap (fun i => match bmpPixel d h y (m + i) with | .ok bs => bs | .error _ => []) := by
  apply flatMap_range_prefix
  exact hmn


/-- A row's full output bytes, as a pixel-prefix. -/
theorem rowOut_width (d : List UInt8) (h : BmpInfo) (y : Nat) :
    rowOut d h y h.width = bmpRowBytes d h y := rfl


/-- An 8-bit pixel that decoded successfully has an in-range palette index. -/
theorem bmpPixel_idx_lt_entries_of_ok (d : List UInt8) (h : BmpInfo) (y x : Nat)
    (hd8 : h.bitCount = 8) (bs : List UInt8)
    (hbs : bmpPixel d h y x = .ok bs) :
    byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) < h.paletteEntries := by
  by_cases hge : byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) ≥ h.paletteEntries
  · have herr : bmpPixel d h y x = .error 11 := by
      unfold bmpPixel
      rw [ite_eq_left hd8]
      dsimp only
      rw [ite_eq_left (by omega : byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) ≥ h.paletteEntries)]
      rfl
    rw [herr] at hbs
    exact absurd hbs (by simp)
  · omega

/-- A successful 8-bit pixel expands to exactly `bmpPixelSize h` bytes. -/
theorem bmpPixel_8bit_length (d : List UInt8) (h : BmpInfo) (y x : Nat)
    (hd8 : h.bitCount = 8) (bs : List UInt8)
    (hbs : bmpPixel d h y x = .ok bs) :
    bs.length = bmpPixelSize h := by
  have hidx := bmpPixel_idx_lt_entries_of_ok d h y x hd8 bs hbs
  have := bmpPixel_palette d h y x hd8 hidx
  rw [this] at hbs
  have h_eq : bs = [d.getD (h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4 + 2) 0,
               d.getD (h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4 + 1) 0,
               d.getD (h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4) 0] :=
    Except.ok.inj hbs.symm
  simp [h_eq, bmpPixelSize, hd8]

/-- An in-bounds 8-bit palette index forces the pixel to decode. -/
theorem bmpPixel_8bit_ok (d : List UInt8) (h : BmpInfo) (y x : Nat) (hd8 : h.bitCount = 8)
    (hidx : byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) < h.paletteEntries) :
    ∃ bs, bmpPixel d h y x = .ok bs := by
  unfold bmpPixel
  rw [ite_eq_left hd8]
  dsimp only
  by_cases hge : byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) ≥ h.paletteEntries
  · exact absurd hge (by omega)
  · rw [ite_eq_right hge]
    exact ⟨[d.getD _ 0, d.getD _ 0, d.getD _ 0], rfl⟩

/-- A successful direct (24/32-bit) pixel expands to exactly `bmpPixelSize h` bytes. -/
theorem bmpPixel_direct_length (d : List UInt8) (h : BmpInfo) (y x : Nat)
    (hn8 : h.bitCount ≠ 8) (hc : h.channels = 3 ∨ h.channels = 4) (bs : List UInt8)
    (hbs : bmpPixel d h y x = .ok bs) :
    bs.length = bmpPixelSize h := by
  unfold bmpPixel at hbs
  rw [ite_eq_right hn8] at hbs
  by_cases hc4 : h.channels = 4
  · simp only [hc4, ite_true] at hbs
    injection hbs with hlist
    rw [← hlist]
    simp [bmpPixelSize, hn8, hc4]
  · have hc3 : h.channels = 3 := by
      cases hc with
      | inl h3 => exact h3
      | inr h4 => exact absurd h4 hc4
    simp only [hc4, ite_false] at hbs
    injection hbs with hlist
    rw [← hlist]
    simp [bmpPixelSize, hn8, hc3]

end NANO
