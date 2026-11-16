/-
  BMP load composition: `ni_bmp_header` (fid 15) followed by
  `ni_bmp_decode_into` (fid 16), the verified part of
  `ni_load_bmp_from_memory`. The header's info-block contents are handed to
  the decode proof; on success the output block holds the flattened
  `bmpPixels` bytes.
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Lemmas
import NANO.Spec
import NANO.Bmp
import NANO.C.Proofs.Core
import NANO.C.Proofs.Bmp
import NANO.C.Proofs.NiGeometryTail
import NANO.C.Proofs.NiBmpHeaderLoads
import NANO.C.Proofs.NiBmpHeaderTail
import NANO.C.Proofs.NiBmpHeaderSpec
import NANO.C.Proofs.NiBmpHeaderSpecGeo
import NANO.C.Proofs.NiBmpHeaderSpecPalette
import NANO.C.Proofs.NiBmpHeaderSpecCompose
import NANO.C.Proofs.NiBmpHeaderArith
import NANO.C.Proofs.NiBmpHeaderPalette
import NANO.C.Proofs.NiBmpHeaderCompose
import NANO.C.Proofs.NiBmpHeader
import NANO.C.Proofs.NiBmpDecode
import NANO.C.Proofs.NiBmpLoop
import NANO.C.Proofs.NiBmpLoop4
import NANO.C.Proofs.NiBmpLoop5
import NANO.C.Proofs.NiBmpDecodeInto

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 800000

namespace NANO.C.Proofs
open NANO NANO.C

/-! ### Field slices of the store-chain blocks, one constructor per layer -/

/-- The arith stage's block: `row_stride@0`, `output_size@8`, `x` from 16. -/
theorem arithBlock_take8 (x : List UInt8) (rs os : Nat) :
    (bmpArithBlock x rs os).take 8 = encodeLE 8 rs := by
  simp [bmpArithBlock, encodeLE_length, List.take_append, List.take_of_length_le]

theorem arithBlock_drop8_take8 (x : List UInt8) (rs os : Nat) :
    ((bmpArithBlock x rs os).drop 8).take 8 = encodeLE 8 os := by
  simp [bmpArithBlock, encodeLE_length, List.take_append, List.drop_append,
    List.length_append, List.take_of_length_le, List.drop_of_length_le, List.take_zero,
    List.nil_append, List.append_nil]

theorem arithBlock_drop44 (x : List UInt8) (h48 : x.length = 48) (rs os : Nat) :
    (bmpArithBlock x rs os).drop 44 = x.drop 44 := by
  simp [bmpArithBlock, h48, encodeLE_length, List.drop_append, List.length_append,
    List.drop_of_length_le, List.nil_append, List.append_nil]

/-- The palette stage's block over the arith block: `palette_offset@16`,
    `palette_entries@36`. -/
theorem palBlock_take8 (y : List UInt8) (h48 : y.length = 48) (po pen : Nat) :
    (bmpPaletteBlock y po pen).take 8 = y.take 8 := by
  simp [bmpPaletteBlock, h48, encodeLE_length, List.take_append, List.drop_append,
    List.length_take, List.length_append, List.take_of_length_le, List.drop_of_length_le,
    List.take_zero, List.take_take, List.nil_append, List.append_nil]

theorem palBlock_drop8_take8 (y : List UInt8) (h48 : y.length = 48) (po pen : Nat) :
    ((bmpPaletteBlock y po pen).drop 8).take 8 = (y.drop 8).take 8 := by
  simp [bmpPaletteBlock, h48, encodeLE_length, List.take_append, List.drop_append,
    List.length_take, List.length_append, List.take_of_length_le, List.drop_of_length_le,
    List.take_zero, List.take_drop, List.take_take, List.nil_append, List.append_nil]

theorem palBlock_drop16_take8 (y : List UInt8) (h48 : y.length = 48) (po pen : Nat) :
    ((bmpPaletteBlock y po pen).drop 16).take 8 = encodeLE 8 po := by
  simp [bmpPaletteBlock, h48, encodeLE_length, List.take_append, List.drop_append,
    List.length_take, List.length_append, List.take_of_length_le, List.drop_of_length_le,
    List.take_zero, List.take_drop, List.nil_append, List.append_nil]

theorem palBlock_drop36_take4 (y : List UInt8) (h48 : y.length = 48) (po pen : Nat) :
    ((bmpPaletteBlock y po pen).drop 36).take 4 = encodeLE 4 pen := by
  simp [bmpPaletteBlock, h48, encodeLE_length, List.take_append, List.drop_append,
    List.length_take, List.length_append, List.take_of_length_le, List.drop_of_length_le,
    List.take_zero, List.take_drop, List.nil_append, List.append_nil]

theorem palBlock_drop44 (y : List UInt8) (h48 : y.length = 48) (po pen : Nat) :
    (bmpPaletteBlock y po pen).drop 44 = y.drop 44 := by
  simp [bmpPaletteBlock, h48, encodeLE_length, List.take_append, List.drop_append,
    List.length_take, List.length_append, List.drop_of_length_le, List.drop_drop,
    List.nil_append, List.append_nil]

/-- The tail stores' block: the six field slices are the splices; the
    preserved ranges pass through to `z`. -/
theorem headBlock_take8 (z : List UInt8) (h48 : z.length = 48) (w h po b c t : Nat) :
    (bmpHeadBlock z w h po b c t).take 8 = z.take 8 := by
  simp [bmpHeadBlock, h48, encodeLE_length, List.take_append, List.length_take,
    List.length_append, List.take_of_length_le, List.take_take, List.take_zero,
    List.nil_append, List.append_nil]

theorem headBlock_drop8_take8 (z : List UInt8) (h48 : z.length = 48) (w h po b c t : Nat) :
    ((bmpHeadBlock z w h po b c t).drop 8).take 8 = (z.drop 8).take 8 := by
  simp [bmpHeadBlock, h48, encodeLE_length, List.take_append, List.drop_append,
    List.length_take, List.length_append, List.take_of_length_le, List.drop_of_length_le,
    List.take_zero, List.take_drop, List.take_take, List.nil_append, List.append_nil]

theorem headBlock_drop16_take8 (z : List UInt8) (h48 : z.length = 48) (w h po b c t : Nat) :
    ((bmpHeadBlock z w h po b c t).drop 16).take 8 = (z.drop 16).take 8 := by
  simp [bmpHeadBlock, h48, encodeLE_length, List.take_append, List.drop_append,
    List.length_take, List.length_append, List.take_of_length_le, List.drop_of_length_le,
    List.take_zero, List.take_drop, List.take_take, List.nil_append, List.append_nil]

theorem headBlock_drop24 (z : List UInt8) (h48 : z.length = 48) (w h po b c t : Nat) :
    ((bmpHeadBlock z w h po b c t).drop 24).take 4 = encodeLE 4 w := by
  simp [bmpHeadBlock, h48, encodeLE_length, List.take_append, List.drop_append,
    List.length_take, List.length_append, List.take_of_length_le, List.drop_of_length_le,
    List.take_zero, List.take_drop, List.nil_append, List.append_nil]

theorem headBlock_drop28 (z : List UInt8) (h48 : z.length = 48) (w h po b c t : Nat) :
    ((bmpHeadBlock z w h po b c t).drop 28).take 4 = encodeLE 4 h := by
  simp [bmpHeadBlock, h48, encodeLE_length, List.take_append, List.drop_append,
    List.length_take, List.length_append, List.take_of_length_le, List.drop_of_length_le,
    List.take_zero, List.take_drop, List.nil_append, List.append_nil]

theorem headBlock_drop32 (z : List UInt8) (h48 : z.length = 48) (w h po b c t : Nat) :
    ((bmpHeadBlock z w h po b c t).drop 32).take 4 = encodeLE 4 po := by
  simp [bmpHeadBlock, h48, encodeLE_length, List.take_append, List.drop_append,
    List.length_take, List.length_append, List.take_of_length_le, List.drop_of_length_le,
    List.take_zero, List.take_drop, List.nil_append, List.append_nil]

theorem headBlock_drop36 (z : List UInt8) (h48 : z.length = 48) (w h po b c t : Nat) :
    ((bmpHeadBlock z w h po b c t).drop 36).take 4 = (z.drop 36).take 4 := by
  simp [bmpHeadBlock, h48, encodeLE_length, List.take_append, List.drop_append,
    List.length_take, List.length_append, List.take_of_length_le, List.drop_of_length_le,
    List.take_zero, List.take_drop, List.nil_append, List.append_nil]

theorem headBlock_drop40 (z : List UInt8) (h48 : z.length = 48) (w h po b c t : Nat) :
    ((bmpHeadBlock z w h po b c t).drop 40).take 2 = encodeLE 2 b := by
  simp [bmpHeadBlock, h48, encodeLE_length, List.take_append, List.drop_append,
    List.length_take, List.length_append, List.take_of_length_le, List.drop_of_length_le,
    List.take_zero, List.take_drop, List.nil_append, List.append_nil]

theorem headBlock_drop42 (z : List UInt8) (h48 : z.length = 48) (w h po b c t : Nat) :
    ((bmpHeadBlock z w h po b c t).drop 42).take 1 = encodeLE 1 c := by
  simp [bmpHeadBlock, h48, encodeLE_length, List.take_append, List.drop_append,
    List.length_take, List.length_append, List.take_of_length_le, List.drop_of_length_le,
    List.take_zero, List.take_drop, List.nil_append, List.append_nil]

theorem headBlock_drop43 (z : List UInt8) (h48 : z.length = 48) (w h po b c t : Nat) :
    ((bmpHeadBlock z w h po b c t).drop 43).take 1 = encodeLE 1 t := by
  simp [bmpHeadBlock, h48, encodeLE_length, List.take_append, List.drop_append,
    List.length_take, List.length_append, List.take_of_length_le, List.drop_of_length_le,
    List.take_zero, List.take_drop, List.nil_append, List.append_nil]

theorem headBlock_drop44 (z : List UInt8) (h48 : z.length = 48) (w h po b c t : Nat) :
    (bmpHeadBlock z w h po b c t).drop 44 = z.drop 44 := by
  simp [bmpHeadBlock, h48, encodeLE_length, List.drop_append, List.length_take,
    List.length_append, List.drop_of_length_le, List.nil_append, List.append_nil]

/-! ### Field slices of the final info block -/

theorem bmpHeaderFinalBlock_length (d gout : List UInt8) (hg : gout.length = 48) :
    (bmpHeaderFinalBlock d gout).length = 48 :=
  bmpHeadBlock_length _ (bmpPaletteBlock_length _ (bmpArithBlock_length gout hg _ _) _ _) _ _ _ _ _ _

theorem bmpHeaderFinalBlock_rows (d gout : List UInt8) (hg : gout.length = 48) :
    ((bmpHeaderFinalBlock d gout).drop 0).take 8 =
      encodeLE 8 (bmpRowStride (rd32le d 18) (rd16le d 28)) := by
  have hPal48 := bmpPaletteBlock_length (bmpArithBlock gout (bmpRowStride (rd32le d 18) (rd16le d 28))
    (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
      ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (bmpArithBlock_length gout hg _ _)
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0)
  show (bmpHeadBlock (bmpPaletteBlock (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28))
      (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
        ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0))
    (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd32le d 10)
    (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3)
    (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)).take 8 = _
  rw [headBlock_take8 _ hPal48]
  rw [palBlock_take8 _ (bmpArithBlock_length gout hg _ _) _ _]
  exact arithBlock_take8 gout _ _

theorem bmpHeaderFinalBlock_outSize (d gout : List UInt8) (hg : gout.length = 48) :
    ((bmpHeaderFinalBlock d gout).drop 8).take 8 =
      encodeLE 8 (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
        ((NANO.toInt32 (rd32le d 22)).natAbs)) := by
  have hA48 := bmpArithBlock_length gout hg (bmpRowStride (rd32le d 18) (rd16le d 28))
    (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
      ((NANO.toInt32 (rd32le d 22)).natAbs))
  have hPal48 := bmpPaletteBlock_length (bmpArithBlock gout (bmpRowStride (rd32le d 18) (rd16le d 28))
    (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
      ((NANO.toInt32 (rd32le d 22)).natAbs))) hA48
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0)
  show ((bmpHeadBlock (bmpPaletteBlock (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28))
      (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
        ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0))
    (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd32le d 10)
    (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3)
    (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)).drop 8).take 8 = _
  rw [headBlock_drop8_take8 _ hPal48]
  rw [palBlock_drop8_take8 _ hA48 _ _]
  exact arithBlock_drop8_take8 gout _ _

theorem bmpHeaderFinalBlock_paletteOffset (d gout : List UInt8) (hg : gout.length = 48) :
    ((bmpHeaderFinalBlock d gout).drop 16).take 8 =
      encodeLE 8 (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0) := by
  have hA48 := bmpArithBlock_length gout hg (bmpRowStride (rd32le d 18) (rd16le d 28))
    (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
      ((NANO.toInt32 (rd32le d 22)).natAbs))
  have hPal48 := bmpPaletteBlock_length (bmpArithBlock gout (bmpRowStride (rd32le d 18) (rd16le d 28))
    (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
      ((NANO.toInt32 (rd32le d 22)).natAbs))) hA48
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0)
  show ((bmpHeadBlock (bmpPaletteBlock (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28))
      (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
        ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0))
    (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd32le d 10)
    (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3)
    (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)).drop 16).take 8 = _
  rw [headBlock_drop16_take8 _ hPal48]
  exact palBlock_drop16_take8 _ hA48 _ _

theorem bmpHeaderFinalBlock_width (d gout : List UInt8) (hg : gout.length = 48) :
    ((bmpHeaderFinalBlock d gout).drop 24).take 4 = encodeLE 4 (rd32le d 18) := by
  have hPal48 := bmpPaletteBlock_length (bmpArithBlock gout (bmpRowStride (rd32le d 18) (rd16le d 28))
    (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
      ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (bmpArithBlock_length gout hg _ _)
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0)
  show ((bmpHeadBlock (bmpPaletteBlock (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28))
      (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
        ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0))
    (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd32le d 10)
    (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3)
    (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)).drop 24).take 4 = _
  exact headBlock_drop24 _ hPal48 _ _ _ _ _ _

theorem bmpHeaderFinalBlock_height (d gout : List UInt8) (hg : gout.length = 48) :
    ((bmpHeaderFinalBlock d gout).drop 28).take 4 =
      encodeLE 4 ((NANO.toInt32 (rd32le d 22)).natAbs) := by
  have hPal48 := bmpPaletteBlock_length (bmpArithBlock gout (bmpRowStride (rd32le d 18) (rd16le d 28))
    (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
      ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (bmpArithBlock_length gout hg _ _)
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0)
  show ((bmpHeadBlock (bmpPaletteBlock (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28))
      (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
        ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0))
    (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd32le d 10)
    (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3)
    (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)).drop 28).take 4 = _
  exact headBlock_drop28 _ hPal48 _ _ _ _ _ _

theorem bmpHeaderFinalBlock_pixelOffset (d gout : List UInt8) (hg : gout.length = 48) :
    ((bmpHeaderFinalBlock d gout).drop 32).take 4 = encodeLE 4 (rd32le d 10) := by
  have hPal48 := bmpPaletteBlock_length (bmpArithBlock gout (bmpRowStride (rd32le d 18) (rd16le d 28))
    (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
      ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (bmpArithBlock_length gout hg _ _)
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0)
  show ((bmpHeadBlock (bmpPaletteBlock (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28))
      (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
        ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0))
    (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd32le d 10)
    (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3)
    (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)).drop 32).take 4 = _
  exact headBlock_drop32 _ hPal48 _ _ _ _ _ _

theorem bmpHeaderFinalBlock_paletteEntries (d gout : List UInt8) (hg : gout.length = 48) :
    ((bmpHeaderFinalBlock d gout).drop 36).take 4 =
      encodeLE 4 (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0) := by
  have hA48 := bmpArithBlock_length gout hg (bmpRowStride (rd32le d 18) (rd16le d 28))
    (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
      ((NANO.toInt32 (rd32le d 22)).natAbs))
  have hPal48 := bmpPaletteBlock_length (bmpArithBlock gout (bmpRowStride (rd32le d 18) (rd16le d 28))
    (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
      ((NANO.toInt32 (rd32le d 22)).natAbs))) hA48
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0)
  show ((bmpHeadBlock (bmpPaletteBlock (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28))
      (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
        ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0))
    (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd32le d 10)
    (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3)
    (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)).drop 36).take 4 = _
  rw [headBlock_drop36 _ hPal48]
  exact palBlock_drop36_take4 _ hA48 _ _

theorem bmpHeaderFinalBlock_bitCount (d gout : List UInt8) (hg : gout.length = 48) :
    ((bmpHeaderFinalBlock d gout).drop 40).take 2 = encodeLE 2 (rd16le d 28) := by
  have hPal48 := bmpPaletteBlock_length (bmpArithBlock gout (bmpRowStride (rd32le d 18) (rd16le d 28))
    (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
      ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (bmpArithBlock_length gout hg _ _)
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0)
  show ((bmpHeadBlock (bmpPaletteBlock (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28))
      (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
        ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0))
    (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd32le d 10)
    (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3)
    (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)).drop 40).take 2 = _
  exact headBlock_drop40 _ hPal48 _ _ _ _ _ _

theorem bmpHeaderFinalBlock_channels (d gout : List UInt8) (hg : gout.length = 48) :
    ((bmpHeaderFinalBlock d gout).drop 42).take 1 =
      encodeLE 1 (if rd16le d 28 = 32 then 4 else 3) := by
  have hPal48 := bmpPaletteBlock_length (bmpArithBlock gout (bmpRowStride (rd32le d 18) (rd16le d 28))
    (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
      ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (bmpArithBlock_length gout hg _ _)
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0)
  show ((bmpHeadBlock (bmpPaletteBlock (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28))
      (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
        ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0))
    (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd32le d 10)
    (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3)
    (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)).drop 42).take 1 = _
  exact headBlock_drop42 _ hPal48 _ _ _ _ _ _

theorem bmpHeaderFinalBlock_topDown (d gout : List UInt8) (hg : gout.length = 48) :
    ((bmpHeaderFinalBlock d gout).drop 43).take 1 =
      encodeLE 1 (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0) := by
  have hPal48 := bmpPaletteBlock_length (bmpArithBlock gout (bmpRowStride (rd32le d 18) (rd16le d 28))
    (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
      ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (bmpArithBlock_length gout hg _ _)
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0)
  show ((bmpHeadBlock (bmpPaletteBlock (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28))
      (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
        ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
    (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0))
    (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd32le d 10)
    (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3)
    (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)).drop 43).take 1 = _
  exact headBlock_drop43 _ hPal48 _ _ _ _ _ _

/-! ### The spec-side info a successful header describes -/

/-- The `BmpInfo` a header accepted by all five stages describes. -/
def bmpHeaderInfoOf (d : List UInt8) : BmpInfo :=
  { rowStride := bmpRowStride (rd32le d 18) (rd16le d 28)
    outSize := bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
      ((NANO.toInt32 (rd32le d 22)).natAbs)
    paletteOffset := if rd16le d 28 = 8 then 14 + rd32le d 14 else 0
    width := rd32le d 18
    height := (NANO.toInt32 (rd32le d 22)).natAbs
    pixelOffset := rd32le d 10
    paletteEntries := if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0
    bitCount := rd16le d 28
    channels := if rd16le d 28 = 32 then 4 else 3
    topDown := if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0 }

/-- If geometry passes, the truncation check does not fire, and the palette
    check passes (or bit_count ≠ 8), `bmpHeader` accepts with the witness
    `bmpHeaderInfoOf d`. -/
theorem bmpHeader_ok_of_stages (size : Nat) (d : List UInt8)
    (hSig : sigOk size d = true) (hLay : layoutOk size d = true)
    (hG : bmpGeometryCode d = 0)
    (hAcr : bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size = 0)
    (hPcr : bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10) = 0) :
    bmpHeader size d = .ok (bmpHeaderInfoOf d) := by
  have h1 : ¬ (NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1) := by
    by_cases h1' : NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1
    · have he : bmpGeometryCode d = 3 := by unfold bmpGeometryCode; rw [if_pos h1']
      rw [he] at hG; contradiction
    · exact h1'
  have hsml : ¬ rd32le d 18 ≥ 2147483648 := by
    by_cases hge : rd32le d 18 ≥ 2147483648
    · have he : NANO.toInt32 (rd32le d 18) ≤ -1 := by
        simp [NANO.toInt32, hge]
        have hmax : rd32le d 18 ≤ 4294967295 := by have := rd32_lt d 18; omega
        omega
      omega
    · exact hge
  have hW : rd32le d 18 ≤ 2147483647 := by omega
  have hb32 : rd16le d 28 ≤ 32 := by
    have hbs := rd16le28_in_set_of_geomOk d hG
    cases hbs with
    | inl h8 => omega
    | inr h => cases h with
      | inl h24 => omega
      | inr h32 => omega
  have h3H : (NANO.toInt32 (rd32le d 22)).natAbs ≤ 2147483648 := height_bound_of_geomOk d hG
  have hwN : NANO.toInt32 (rd32le d 18) = (rd32le d 18 : Int) := by
    unfold NANO.toInt32; rw [if_neg (by omega)]
  have hWnat : (NANO.toInt32 (rd32le d 18)).toNat = rd32le d 18 := by
    rw [hwN]; rfl
  -- the truncation and palette verdicts hidden in `hAcr = 0` / `hPcr = 0`
  have hCh : (if rd16le d 28 = 32 then 4 else 3) ≤ 4 := channels_le_4 (rd16le d 28)
  have hTrunc := @arithCode_unfold (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
    (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size hW hb32 hCh h3H
  rw [hAcr] at hTrunc
  have hNotTrunc : ¬ (rd32le d 10 > sizeMax - bmpRowStride (rd32le d 18) (rd16le d 28) * (NANO.toInt32 (rd32le d 22)).natAbs
      ∨ rd32le d 10 + bmpRowStride (rd32le d 18) (rd16le d 28) * (NANO.toInt32 (rd32le d 22)).natAbs > size) := by
    intro hbad
    rw [if_pos hbad] at hTrunc
    exact absurd hTrunc (by decide)
  have hOK : rd16le d 28 ≠ 8 ∨ (rd16le d 28 = 8 ∧
      ¬ ((if rd32le d 46 = 0 then 256 else rd32le d 46) = 0 ∨
         (256 < if rd32le d 46 = 0 then 256 else rd32le d 46) ∨
         rd32le d 10 < 14 + rd32le d 14 + (if rd32le d 46 = 0 then 256 else rd32le d 46) * 4)) := by
    by_cases hB8 : rd16le d 28 = 8
    · right
      refine ⟨hB8, ?_⟩
      have hU := paletteCode_unfold (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10)
      rw [if_pos hB8, hPcr] at hU
      intro hbad
      rw [if_pos hbad] at hU
      exact absurd hU (by decide)
    · exact Or.inl hB8
  have hSigOk := bmpSigGate_ok_of_sigOk size d hSig
  have hLayOk := bmpLayoutGate_ok_of_layoutOk size d hLay
  unfold bmpHeader
  rw [hSigOk, bind_ok_of_ok]
  rw [hLayOk, bind_ok_of_ok]
  by_cases hLT : NANO.toInt32 (rd32le d 22) < 0
  · by_cases h2 : NANO.toInt32 (rd32le d 22) = -2147483648
    · have he : bmpGeometryCode d = 4 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_pos h2]
      rw [he] at hG; contradiction
    · by_cases h5 : rd32le d 30 ≠ 0
      · have he : bmpGeometryCode d = 5 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_neg h2, if_pos h5]
        rw [he] at hG; contradiction
      · by_cases h6 : rd16le d 28 ≠ 8 ∧ rd16le d 28 ≠ 24 ∧ rd16le d 28 ≠ 32
        · have he : bmpGeometryCode d = 6 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_neg h2, if_neg h5, if_pos h6]
          rw [he] at hG; contradiction
        · have hStage : bmpGeometryStage size d =
              .ok ((NANO.toInt32 (rd32le d 18)).toNat, (NANO.toInt32 (rd32le d 22)).natAbs, rd16le d 28,
                   if rd16le d 28 = 32 then 4 else 3, 1, rd32le d 46) := by
            unfold bmpGeometryStage; rw [if_neg h1, if_pos hLT, if_neg h2, if_neg h5, if_neg h6]; rfl
          rw [hStage, bind_ok_of_ok]
          have hW' : (NANO.toInt32 (rd32le d 18)).toNat ≤ 2147483647 := by
            rw [hwN]; exact hW
          have hNotTrunc' : ¬ (rd32le d 10 > sizeMax - (((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32) * 4 * (NANO.toInt32 (rd32le d 22)).natAbs ∨
              rd32le d 10 + (((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32) * 4 * (NANO.toInt32 (rd32le d 22)).natAbs > size) := by
            intro hOr
            apply hNotTrunc
            rw [hWnat] at hOr
            exact hOr
          by_cases hB8 : rd16le d 28 ≠ 8
          · have hOk := @bmpOutputCompose_ok_ne8 size d
              (W := (NANO.toInt32 (rd32le d 18)).toNat)
              (H := (NANO.toInt32 (rd32le d 22)).natAbs)
              (b := rd16le d 28)
              (c := if rd16le d 28 = 32 then 4 else 3)
              (t := 1) (cU := rd32le d 46)
              hb32
              (channels_le_4 (rd16le d 28))
              hW' h3H hNotTrunc' hB8
            rw [hOk, hWnat]
            simp [bmpHeaderInfoOf, bmpRowStride, bmpOutSize, hB8, hLT]
          · have hOK' := hOK.resolve_left hB8
            have hOk := @bmpOutputCompose_ok_8 size d
              (W := (NANO.toInt32 (rd32le d 18)).toNat)
              (H := (NANO.toInt32 (rd32le d 22)).natAbs)
              (b := rd16le d 28)
              (c := if rd16le d 28 = 32 then 4 else 3)
              (t := 1) (cU := rd32le d 46)
              hb32
              (channels_le_4 (rd16le d 28))
              hW' h3H hNotTrunc' hOK'.1 hOK'.2
            rw [hOk, hWnat]
            simp [bmpHeaderInfoOf, bmpRowStride, bmpOutSize, hB8, hLT,
              show (if rd32le d 46 ≠ 0 then rd32le d 46 else 256) = (if rd32le d 46 = 0 then 256 else rd32le d 46) from by
                by_cases hcu : rd32le d 46 = 0
                · rw [if_neg (by omega : ¬ (rd32le d 46 ≠ 0)), if_pos hcu]
                · rw [if_pos (by omega : rd32le d 46 ≠ 0), if_neg hcu]]
  · by_cases h5 : rd32le d 30 ≠ 0
    · have he : bmpGeometryCode d = 5 := by unfold bmpGeometryCode; rw [if_neg h1, if_neg hLT, if_pos h5]
      rw [he] at hG; contradiction
    · by_cases h6 : rd16le d 28 ≠ 8 ∧ rd16le d 28 ≠ 24 ∧ rd16le d 28 ≠ 32
      · have he : bmpGeometryCode d = 6 := by unfold bmpGeometryCode; rw [if_neg h1, if_neg hLT, if_neg h5, if_pos h6]
        rw [he] at hG; contradiction
      · have hStage : bmpGeometryStage size d =
            .ok ((NANO.toInt32 (rd32le d 18)).toNat, (NANO.toInt32 (rd32le d 22)).natAbs, rd16le d 28,
                 if rd16le d 28 = 32 then 4 else 3, 0, rd32le d 46) := by
          unfold bmpGeometryStage; rw [if_neg h1, if_neg hLT, if_neg h5, if_neg h6]; rfl
        rw [hStage, bind_ok_of_ok]
        have hW' : (NANO.toInt32 (rd32le d 18)).toNat ≤ 2147483647 := by
          rw [hwN]; exact hW
        have hNotTrunc' : ¬ (rd32le d 10 > sizeMax - (((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32) * 4 * (NANO.toInt32 (rd32le d 22)).natAbs ∨
            rd32le d 10 + (((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32) * 4 * (NANO.toInt32 (rd32le d 22)).natAbs > size) := by
          intro hOr
          apply hNotTrunc
          rw [hWnat] at hOr
          exact hOr
        by_cases hB8 : rd16le d 28 ≠ 8
        · have hOk := @bmpOutputCompose_ok_ne8 size d
            (W := (NANO.toInt32 (rd32le d 18)).toNat)
            (H := (NANO.toInt32 (rd32le d 22)).natAbs)
            (b := rd16le d 28)
            (c := if rd16le d 28 = 32 then 4 else 3)
            (t := 0) (cU := rd32le d 46)
            hb32
            (channels_le_4 (rd16le d 28))
            hW' h3H hNotTrunc' hB8
          rw [hOk, hWnat]
          simp [bmpHeaderInfoOf, bmpRowStride, bmpOutSize, hB8, hLT]
        · have hOK' := hOK.resolve_left hB8
          have hOk := @bmpOutputCompose_ok_8 size d
            (W := (NANO.toInt32 (rd32le d 18)).toNat)
            (H := (NANO.toInt32 (rd32le d 22)).natAbs)
            (b := rd16le d 28)
            (c := if rd16le d 28 = 32 then 4 else 3)
            (t := 0) (cU := rd32le d 46)
            hb32
            (channels_le_4 (rd16le d 28))
            hW' h3H hNotTrunc' hOK'.1 hOK'.2
          rw [hOk, hWnat]
          simp [bmpHeaderInfoOf, bmpRowStride, bmpOutSize, hB8, hLT,
            show (if rd32le d 46 ≠ 0 then rd32le d 46 else 256) = (if rd32le d 46 = 0 then 256 else rd32le d 46) from by
              by_cases hcu : rd32le d 46 = 0
              · rw [if_neg (by omega : ¬ (rd32le d 46 ≠ 0)), if_pos hcu]
              · rw [if_pos (by omega : rd32le d 46 ≠ 0), if_neg hcu]]


/-! ### Stage-fact bundle for the composed load -/

/-- All header-derived bounds on the witness `bmpHeaderInfoOf d`, from the
    geometry/arith/palette verdicts. -/
theorem bmpHeaderInfoOf_stage_facts (d : List UInt8) (hlen : d.length < 2 ^ 64)
    (hG0 : bmpGeometryCode d = 0)
    (hAcr : bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) d.length = 0)
    (hPcr : bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10) = 0) :
    ((bmpHeaderInfoOf d).pixelOffset + (bmpHeaderInfoOf d).rowStride * (bmpHeaderInfoOf d).height ≤ d.length) ∧
    ((bmpHeaderInfoOf d).pixelOffset + (bmpHeaderInfoOf d).rowStride * (bmpHeaderInfoOf d).height < 2 ^ 64) ∧
    ((bmpHeaderInfoOf d).rowStride < 2 ^ 64) ∧
    ((bmpHeaderInfoOf d).outSize < 2 ^ 64) ∧
    ((bmpHeaderInfoOf d).paletteOffset + (bmpHeaderInfoOf d).paletteEntries * 4 ≤ (bmpHeaderInfoOf d).pixelOffset) ∧
    ((bmpHeaderInfoOf d).paletteOffset < 2 ^ 64) ∧
    ((bmpHeaderInfoOf d).width < 4294967296) ∧
    ((bmpHeaderInfoOf d).height < 4294967296) ∧
    ((bmpHeaderInfoOf d).pixelOffset < 4294967296) ∧
    ((bmpHeaderInfoOf d).paletteEntries < 4294967296) ∧
    ((bmpHeaderInfoOf d).bitCount < 65536) ∧
    (1 ≤ (bmpHeaderInfoOf d).width) ∧
    ((bmpHeaderInfoOf d).topDown = 0 ∨ (bmpHeaderInfoOf d).topDown = 1) ∧
    ((bmpHeaderInfoOf d).channels = 3 ∨ (bmpHeaderInfoOf d).channels = 4) ∧
    ((bmpHeaderInfoOf d).bitCount = 8 ∨ (bmpHeaderInfoOf d).bitCount = 24 ∨ (bmpHeaderInfoOf d).bitCount = 32) ∧
    ((bmpHeaderInfoOf d).bitCount ≠ 8 → (bmpHeaderInfoOf d).width * (bmpHeaderInfoOf d).channels ≤ (bmpHeaderInfoOf d).rowStride) ∧
    ((bmpHeaderInfoOf d).width ≤ (bmpHeaderInfoOf d).rowStride) := by
  have hDisj : ¬ (NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1) := by
    intro hb
    have he : bmpGeometryCode d = 3 := by unfold bmpGeometryCode; rw [if_pos hb]
    rw [he] at hG0; exact absurd hG0 (by decide)
  have hWpos : 0 < NANO.toInt32 (rd32le d 18) := by omega
  have hsml : ¬ rd32le d 18 ≥ 2147483648 := by
    by_cases hge : rd32le d 18 ≥ 2147483648
    · have he : NANO.toInt32 (rd32le d 18) ≤ -1 := by
        simp [NANO.toInt32, hge]
        have hmax : rd32le d 18 ≤ 4294967295 := by have := rd32_lt d 18; omega
        omega
      omega
    · exact hge
  have hHne : NANO.toInt32 (rd32le d 22) ≠ 0 := by omega
  have hHpos : 0 < (NANO.toInt32 (rd32le d 22)).natAbs := by omega
  have hWle : rd32le d 18 ≤ 2147483647 := by omega
  have hBl : rd16le d 28 ≤ 32 := by
    have hbs := rd16le28_in_set_of_geomOk d hG0
    cases hbs with
    | inl h8 => omega
    | inr h => cases h with
      | inl h24 => omega
      | inr h32 => omega
  have hHb : (NANO.toInt32 (rd32le d 22)).natAbs ≤ 2147483648 := height_bound_of_geomOk d hG0
  have hCh : (if rd16le d 28 = 32 then 4 else 3) ≤ 4 := channels_le_4 (rd16le d 28)
  have hBset : rd16le d 28 = 8 ∨ rd16le d 28 = 24 ∨ rd16le d 28 = 32 := rd16le28_in_set_of_geomOk d hG0
  have hTrunc := @arithCode_unfold (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
    (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) d.length hWle hBl hCh hHb
  rw [hAcr] at hTrunc
  have hNotTrunc : ¬ (rd32le d 10 > sizeMax - bmpRowStride (rd32le d 18) (rd16le d 28) * ((NANO.toInt32 (rd32le d 22)).natAbs) ∨
      rd32le d 10 + bmpRowStride (rd32le d 18) (rd16le d 28) * ((NANO.toInt32 (rd32le d 22)).natAbs) > d.length) := by
    intro hbad
    rw [if_pos hbad] at hTrunc
    exact absurd hTrunc (by decide)
  have hpx : (bmpHeaderInfoOf d).pixelOffset + (bmpHeaderInfoOf d).rowStride * (bmpHeaderInfoOf d).height ≤ d.length := by
    show rd32le d 10 + bmpRowStride (rd32le d 18) (rd16le d 28) * ((NANO.toInt32 (rd32le d 22)).natAbs) ≤ d.length
    have := hNotTrunc; omega
  have hpx64 : (bmpHeaderInfoOf d).pixelOffset + (bmpHeaderInfoOf d).rowStride * (bmpHeaderInfoOf d).height < 2 ^ 64 := by
    have := hpx; omega
  have hrow64 : (bmpHeaderInfoOf d).rowStride < 2 ^ 64 := by
    have h1 : 1 ≤ (bmpHeaderInfoOf d).height := hHpos
    have hm : (bmpHeaderInfoOf d).rowStride * 1 ≤ (bmpHeaderInfoOf d).rowStride * (bmpHeaderInfoOf d).height :=
      Nat.mul_le_mul_left _ h1
    omega
  have hsm3 : sizeMulOK (rd32le d 18 * (if rd16le d 28 = 32 then 4 else 3))
      ((NANO.toInt32 (rd32le d 22)).natAbs) = true := by
    have h12 := sizeMulOK_w_b_gen (show rd32le d 18 ≤ 4294967295 by have := rd32_lt d 18; omega)
      (show rd16le d 28 ≤ 65535 by have := rd16le_lt d 28; omega)
    have h13 := sizeMulOK_w_c_gen (show rd32le d 18 ≤ 4294967295 by have := rd32_lt d 18; omega)
      (show (if rd16le d 28 = 32 then 4 else 3) ≤ 255 by omega)
    by_cases h : sizeMulOK (rd32le d 18 * (if rd16le d 28 = 32 then 4 else 3))
        ((NANO.toInt32 (rd32le d 22)).natAbs) = false
    · exfalso
      unfold bmpOutputArithCode at hAcr
      rw [if_neg (by simp [h12]), if_neg (by simp [h13]), if_pos (by simp [h])] at hAcr
      exact absurd hAcr (by decide)
    · cases hb : sizeMulOK (rd32le d 18 * (if rd16le d 28 = 32 then 4 else 3))
          ((NANO.toInt32 (rd32le d 22)).natAbs) with
      | true => rfl
      | false => exact absurd hb h
  have houtsz64 : (bmpHeaderInfoOf d).outSize < 2 ^ 64 := by
    show (rd32le d 18) * (if rd16le d 28 = 32 then 4 else 3) * ((NANO.toInt32 (rd32le d 22)).natAbs) < 2 ^ 64
    have hs := hsm3
    unfold sizeMulOK at hs
    by_cases h0 : rd32le d 18 * (if rd16le d 28 = 32 then 4 else 3) = 0
    · have hz : (rd32le d 18 * (if rd16le d 28 = 32 then 4 else 3)) * ((NANO.toInt32 (rd32le d 22)).natAbs) = 0 := by
        rw [h0, Nat.zero_mul]
      omega
    · have hge : ((NANO.toInt32 (rd32le d 22)).natAbs) ≤
          sizeMax / (rd32le d 18 * (if rd16le d 28 = 32 then 4 else 3)) := by
        simpa [h0] using hs
      have hle := Nat.le_div_iff_mul_le (by omega : 0 < rd32le d 18 * (if rd16le d 28 = 32 then 4 else 3)) |>.mp hge
      have e : ((NANO.toInt32 (rd32le d 22)).natAbs) * (rd32le d 18 * (if rd16le d 28 = 32 then 4 else 3)) =
          (rd32le d 18 * (if rd16le d 28 = 32 then 4 else 3)) * ((NANO.toInt32 (rd32le d 22)).natAbs) :=
        Nat.mul_comm _ _
      have hb : (rd32le d 18 * (if rd16le d 28 = 32 then 4 else 3)) * ((NANO.toInt32 (rd32le d 22)).natAbs) ≤
          18446744073709551615 := by
        rw [← e]
        simpa [sizeMax] using hle
      omega
  have hPal8 : rd16le d 28 = 8 → ¬ ((if rd32le d 46 = 0 then 256 else rd32le d 46) = 0 ∨
                 (256 < if rd32le d 46 = 0 then 256 else rd32le d 46) ∨
                 14 + rd32le d 14 + (if rd32le d 46 = 0 then 256 else rd32le d 46) * 4 > rd32le d 10) := by
    intro h8 hbad
    have hU := paletteCode_unfold (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10)
    rw [if_pos h8, hPcr] at hU
    rw [if_pos hbad] at hU
    exact absurd hU (by decide)
  have hpalok : (bmpHeaderInfoOf d).paletteOffset + (bmpHeaderInfoOf d).paletteEntries * 4 ≤
      (bmpHeaderInfoOf d).pixelOffset := by
    show (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0) +
      (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0) * 4 ≤ rd32le d 10
    by_cases h8 : rd16le d 28 = 8
    · rw [if_pos h8, if_pos h8]
      have := hPal8 h8; omega
    · rw [if_neg h8, if_neg h8]; omega
  have hpentrv : (bmpHeaderInfoOf d).paletteEntries < 4294967296 := by
    show (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0) < 4294967296
    by_cases h8 : rd16le d 28 = 8
    · rw [if_pos h8]
      have hP := hPal8 h8
      by_cases h : (if rd32le d 46 = 0 then 256 else rd32le d 46) = 0
      · rw [h]; omega
      · have hle : ¬ (256 < if rd32le d 46 = 0 then 256 else rd32le d 46) := by
          intro hc; exact hP (Or.inr (Or.inl hc))
        omega
    · rw [if_neg h8]; omega
  have hpal64 : (bmpHeaderInfoOf d).paletteOffset < 2 ^ 64 := by
    show (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0) < 2 ^ 64
    by_cases h8 : rd16le d 28 = 8
    · rw [if_pos h8]; have := rd32_lt d 14; omega
    · rw [if_neg h8]; omega
  have hwv : (bmpHeaderInfoOf d).width < 4294967296 := by
    show rd32le d 18 < 4294967296; exact rd32_lt d 18
  have hhtwv : (bmpHeaderInfoOf d).height < 4294967296 := by
    show (NANO.toInt32 (rd32le d 22)).natAbs < 4294967296; omega
  have hpicv : (bmpHeaderInfoOf d).pixelOffset < 4294967296 := by
    show rd32le d 10 < 4294967296; exact rd32_lt d 10
  have hbcv : (bmpHeaderInfoOf d).bitCount < 65536 := by
    show rd16le d 28 < 65536; exact rd16le_lt d 28
  have hwN : NANO.toInt32 (rd32le d 18) = (rd32le d 18 : Int) := by
    unfold NANO.toInt32; rw [if_neg hsml]
  have hwidth : 1 ≤ (bmpHeaderInfoOf d).width := by
    show 1 ≤ rd32le d 18
    have := hWpos
    rw [hwN] at this
    omega
  have htopd : (bmpHeaderInfoOf d).topDown = 0 ∨ (bmpHeaderInfoOf d).topDown = 1 := by
    show (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0) = 0 ∨
      (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0) = 1
    by_cases h : NANO.toInt32 (rd32le d 22) < 0
    · rw [if_pos h]; exact Or.inr rfl
    · rw [if_neg h]; exact Or.inl rfl
  have hchc : (bmpHeaderInfoOf d).channels = 3 ∨ (bmpHeaderInfoOf d).channels = 4 := by
    show (if rd16le d 28 = 32 then 4 else 3) = 3 ∨ (if rd16le d 28 = 32 then 4 else 3) = 4
    by_cases h : rd16le d 28 = 32
    · rw [if_pos h]; exact Or.inr rfl
    · rw [if_neg h]; exact Or.inl rfl
  have hrsd : (bmpHeaderInfoOf d).bitCount ≠ 8 → (bmpHeaderInfoOf d).width * (bmpHeaderInfoOf d).channels ≤
      (bmpHeaderInfoOf d).rowStride := by
    intro hn8
    show rd32le d 18 * (if rd16le d 28 = 32 then 4 else 3) ≤ ((rd32le d 18 * rd16le d 28 + 31) / 32) * 4
    rcases hBset with h8 | h24 | h32
    · exact absurd h8 hn8
    · rw [h24]
      rw [show (if (24 : Nat) = 32 then 4 else 3) = 3 from by decide]
      omega
    · rw [h32]
      rw [show (if (32 : Nat) = 32 then 4 else 3) = 4 from by decide]
      omega
  have hrs_ge_w : (bmpHeaderInfoOf d).width ≤ (bmpHeaderInfoOf d).rowStride := by
    show rd32le d 18 ≤ ((rd32le d 18 * rd16le d 28 + 31) / 32) * 4
    rcases hBset with h8 | h24 | h32
    · rw [h8]; omega
    · rw [h24]; omega
    · rw [h32]; omega
  exact ⟨hpx, hpx64, hrow64, houtsz64, hpalok, hpal64, hwv, hhtwv, hpicv, hpentrv, hbcv,
    hwidth, htopd, hchc, hBset, hrsd, hrs_ge_w⟩

/-! ### Pixel-access bounds for the composed load -/

theorem bmpHeaderInfoOf_px8 (d : List UInt8) (hlen : d.length < 2 ^ 64)
    (hG0 : bmpGeometryCode d = 0)
    (hAcr : bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) d.length = 0)
    (hPcr : bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10) = 0) :
    ∀ y i, y < (bmpHeaderInfoOf d).height → i < (bmpHeaderInfoOf d).width →
      (bmpHeaderInfoOf d).pixelOffset +
        (if (bmpHeaderInfoOf d).topDown = 1 then y else (bmpHeaderInfoOf d).height - 1 - y) *
          (bmpHeaderInfoOf d).rowStride + i < d.length := by
  obtain ⟨hpx, _hpx64, _hrow64, _houtsz64, _hpalok, _hpal64, _hwv, _hhtwv, _hpicv, _hpentrv,
    _hbcv, _hwidth, _htopd, _hchc, _hbcdisc, _hrsd, hrs_ge_w⟩ :=
    bmpHeaderInfoOf_stage_facts d hlen hG0 hAcr hPcr
  have hHne : NANO.toInt32 (rd32le d 22) ≠ 0 := by
    intro hb
    have he : bmpGeometryCode d = 3 := by
      unfold bmpGeometryCode
      rw [if_pos (Or.inr (Or.inl hb))]
    rw [he] at hG0; exact absurd hG0 (by decide)
  have hHpos : 0 < (bmpHeaderInfoOf d).height := by
    show 0 < (NANO.toInt32 (rd32le d 22)).natAbs
    exact Int.natAbs_pos.mpr hHne
  have hrowh : (bmpHeaderInfoOf d).rowStride * (bmpHeaderInfoOf d).height =
      ((bmpHeaderInfoOf d).height - 1) * (bmpHeaderInfoOf d).rowStride + (bmpHeaderInfoOf d).rowStride := by
    have h1 : 1 ≤ (bmpHeaderInfoOf d).height := hHpos
    have hh : (bmpHeaderInfoOf d).height - 1 + 1 = (bmpHeaderInfoOf d).height := Nat.sub_add_cancel h1
    calc (bmpHeaderInfoOf d).rowStride * (bmpHeaderInfoOf d).height
        = (bmpHeaderInfoOf d).rowStride * ((bmpHeaderInfoOf d).height - 1 + 1) := by rw [hh]
      _ = (bmpHeaderInfoOf d).rowStride * ((bmpHeaderInfoOf d).height - 1) + (bmpHeaderInfoOf d).rowStride := by
            rw [Nat.mul_add, Nat.mul_one]
      _ = ((bmpHeaderInfoOf d).height - 1) * (bmpHeaderInfoOf d).rowStride + (bmpHeaderInfoOf d).rowStride := by
            rw [Nat.mul_comm (bmpHeaderInfoOf d).rowStride ((bmpHeaderInfoOf d).height - 1)]
  intro y i hy hi
  have hsy : (if (bmpHeaderInfoOf d).topDown = 1 then y else (bmpHeaderInfoOf d).height - 1 - y) ≤
      (bmpHeaderInfoOf d).height - 1 := by
    by_cases htd : (bmpHeaderInfoOf d).topDown = 1
    · rw [if_pos htd]; omega
    · rw [if_neg htd]; omega
  have hmul : (if (bmpHeaderInfoOf d).topDown = 1 then y else (bmpHeaderInfoOf d).height - 1 - y) *
      (bmpHeaderInfoOf d).rowStride ≤ ((bmpHeaderInfoOf d).height - 1) * (bmpHeaderInfoOf d).rowStride :=
    Nat.mul_le_mul_right _ hsy
  have hir : i < (bmpHeaderInfoOf d).rowStride := by omega
  omega

theorem bmpHeaderInfoOf_idx8 (d : List UInt8)
    (hG0 : bmpGeometryCode d = 0)
    (hokPix : ∀ y x, y < (bmpHeaderInfoOf d).height → x < (bmpHeaderInfoOf d).width →
      ∃ bs, bmpPixel d (bmpHeaderInfoOf d) y x = .ok bs) :
    (bmpHeaderInfoOf d).bitCount = 8 → ∀ y i, y < (bmpHeaderInfoOf d).height →
      i < (bmpHeaderInfoOf d).width →
      byteAt d ((bmpHeaderInfoOf d).pixelOffset +
        (if (bmpHeaderInfoOf d).topDown = 1 then y else (bmpHeaderInfoOf d).height - 1 - y) *
          (bmpHeaderInfoOf d).rowStride + i) < (bmpHeaderInfoOf d).paletteEntries := by
  intro hbc8 y i hy hi
  obtain ⟨bs, hbs⟩ := hokPix y i hy hi
  exact bmpPixel_idx_lt_entries_of_ok d (bmpHeaderInfoOf d) y i hbc8 bs hbs

theorem bmpHeaderInfoOf_pos8 (d : List UInt8) (hlen : d.length < 2 ^ 64)
    (hG0 : bmpGeometryCode d = 0)
    (hAcr : bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) d.length = 0)
    (hPcr : bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10) = 0)
    (hokPix : ∀ y x, y < (bmpHeaderInfoOf d).height → x < (bmpHeaderInfoOf d).width →
      ∃ bs, bmpPixel d (bmpHeaderInfoOf d) y x = .ok bs) :
    (bmpHeaderInfoOf d).bitCount = 8 → ∀ y i, y < (bmpHeaderInfoOf d).height →
      i < (bmpHeaderInfoOf d).width →
      (bmpHeaderInfoOf d).paletteOffset + byteAt d ((bmpHeaderInfoOf d).pixelOffset +
        (if (bmpHeaderInfoOf d).topDown = 1 then y else (bmpHeaderInfoOf d).height - 1 - y) *
          (bmpHeaderInfoOf d).rowStride + i) * 4 + 3 ≤ d.length := by
  obtain ⟨_hpx, _hpx64, _hrow64, _houtsz64, hpalok, _hpal64, _hwv, _hhtwv, _hpicv, _hpentrv,
    _hbcv, _hwidth, _htopd, _hchc, _hbcdisc, _hrsd, _hrs_ge_w⟩ :=
    bmpHeaderInfoOf_stage_facts d hlen hG0 hAcr hPcr
  intro hbc8 y i hy hi
  have hidx := bmpHeaderInfoOf_idx8 d hG0 hokPix hbc8 y i hy hi
  have hpxi := bmpHeaderInfoOf_px8 d hlen hG0 hAcr hPcr y i hy hi
  have hle : byteAt d ((bmpHeaderInfoOf d).pixelOffset +
      (if (bmpHeaderInfoOf d).topDown = 1 then y else (bmpHeaderInfoOf d).height - 1 - y) *
        (bmpHeaderInfoOf d).rowStride + i) * 4 + 3 ≤ (bmpHeaderInfoOf d).paletteEntries * 4 := by
    omega
  have := hpalok
  omega


/-! ### The composed load: header then decode -/

/-- The verified load path — `ni_bmp_header` (fid 15), then, when it accepts,
    `ni_bmp_decode_into` (fid 16): the core of `ni_load_bmp_from_memory`.
    The info object is block 3, the output buffer block `bo`. Under the five
    stage verdicts the header accepts; the composite returns 0 and the output
    block holds the flattened `bmpPixels` bytes. -/
theorem ni_bmp_load_exs (m : Mem) (d : List UInt8) (bd : Nat) (hm : m bd = some d)
    (hd : 54 ≤ d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : m 3 = some obl) (h48 : obl.length = 48)
    (out : List UInt8) (bo : Nat) (hoo : m bo = some out) (hcap64 : out.length < 2 ^ 64)
    (hbdo : bd ≠ bo) (h3o : 3 ≠ bo) (hb3 : 3 ≠ bd)
    (ro : Bool) (hro : ro = false)
    (hSig : sigOk d.length d = true) (hLay : layoutOk d.length d = true)
    (hG0 : bmpGeometryCode d = 0)
    (hAcr : bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) d.length = 0)
    (hPcr : bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10) = 0)
    (hokPix : ∀ y x, y < (bmpHeaderInfoOf d).height → x < (bmpHeaderInfoOf d).width →
      ∃ bs, bmpPixel d (bmpHeaderInfoOf d) y x = .ok bs)
    (hcap : (bmpHeaderInfoOf d).outSize ≤ out.length) :
    ∃ s', ExS Gen.prog
        ⟨frameLocals [0, 1, 2, 3, 4, 17]
          [.ptr bd 0, .int ⟨64, false⟩ d.length, .ptr 3 0, .ptr bo 0, .int ⟨64, false⟩ out.length,
           .int ⟨32, true⟩ 0], m, ro⟩
        (.seq (.call (some 17) 15 [(.var 0), (.var 1), (.var 2)])
          (.seq (.ite (.bin .ne (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0)))
                  (.ret (some (.var 17))) .skip)
            (.seq (.call none 16 [(.var 0), (.var 1), (.var 2), (.var 3), (.var 4)])
              (.ret (some (.const (.int ⟨32, true⟩ 0)))))))
        (.ret (some (.int ⟨32, true⟩ (bmpHeaderCode d.length d)))) s' ∧
      s'.mem bo = some (bmpRowsBytes d (bmpHeaderInfoOf d) (bmpHeaderInfoOf d).height ++
        out.drop ((bmpHeaderInfoOf d).height * bmpRowSize (bmpHeaderInfoOf d))) ∧
      bmpHeader d.length d = .ok (bmpHeaderInfoOf d) := by
  have hSpec : bmpHeader d.length d = .ok (bmpHeaderInfoOf d) :=
    bmpHeader_ok_of_stages d.length d hSig hLay hG0 hAcr hPcr
  have hCode0 : bmpHeaderCode d.length d = 0 := by unfold bmpHeaderCode; rw [hSpec]
  let s : State :=
    ⟨frameLocals [0, 1, 2, 3, 4, 17]
      ([.ptr bd 0, .int ⟨64, false⟩ d.length, .ptr 3 0, .ptr bo 0, .int ⟨64, false⟩ out.length,
        .int ⟨32, true⟩ 0] : List Val), m, ro⟩
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  have h0 : s.locals 0 = some (.ptr bd 0) := rfl
  have h1 : s.locals 1 = some (.int ⟨64, false⟩ d.length) := rfl
  have h2 : s.locals 2 = some (.ptr 3 0) := rfl
  have h3 : s.locals 3 = some (.ptr bo 0) := rfl
  have h4 : s.locals 4 = some (.int ⟨64, false⟩ out.length) := rfl
  -- the header call
  obtain ⟨sH, hHdrBody, hHdrExp⟩ :=
    ni_bmp_header_exs m bd d hm d.length (Nat.le_refl _) hd hlen obl hob h48 ro hro
  have hHdrArgs : EvArgs Gen.prog s [(.var 0), (.var 1), (.var 2)]
      [.ptr bd 0, .int ⟨64, false⟩ d.length, .ptr 3 0] :=
    EvArgs.cons (EvE.var h0) (EvArgs.cons (EvE.var h1) (EvArgs.cons (EvE.var h2) EvArgs.nil))
  have hHdrCall : ExS Gen.prog s (.call (some 17) 15 [(.var 0), (.var 1), (.var 2)]) .normal
      { s with mem := sH.mem, locals := s.locals.upd 17 (.int ⟨32, true⟩ (bmpHeaderCode d.length d)) } :=
    ExS.call_dst hHdrArgs (show Gen.prog 15 = some Gen.ni_bmp_header from rfl)
      (show Gen.ni_bmp_header.params.length = 3 from rfl) hHdrBody
  let s1 : State :=
    { s with mem := sH.mem, locals := s.locals.upd 17 (.int ⟨32, true⟩ (bmpHeaderCode d.length d)) }
  have h17_1 : s1.locals 17 = some (.int ⟨32, true⟩ 0) := by
    rw [show s1.locals = s.locals.upd 17 (.int ⟨32, true⟩ (bmpHeaderCode d.length d)) from rfl,
      Locals.upd_same, hCode0]
  have h0_1 : s1.locals 0 = some (.ptr bd 0) :=
    locals_upd_extract 17 (.int ⟨32, true⟩ (bmpHeaderCode d.length d)) 0 (by decide : ¬ (0 : Nat) = 17) h0
  have h1_1 : s1.locals 1 = some (.int ⟨64, false⟩ d.length) :=
    locals_upd_extract 17 (.int ⟨32, true⟩ (bmpHeaderCode d.length d)) 1 (by decide : ¬ (1 : Nat) = 17) h1
  have h2_1 : s1.locals 2 = some (.ptr 3 0) :=
    locals_upd_extract 17 (.int ⟨32, true⟩ (bmpHeaderCode d.length d)) 2 (by decide : ¬ (2 : Nat) = 17) h2
  have h3_1 : s1.locals 3 = some (.ptr bo 0) :=
    locals_upd_extract 17 (.int ⟨32, true⟩ (bmpHeaderCode d.length d)) 3 (by decide : ¬ (3 : Nat) = 17) h3
  have h4_1 : s1.locals 4 = some (.int ⟨64, false⟩ out.length) :=
    locals_upd_extract 17 (.int ⟨32, true⟩ (bmpHeaderCode d.length d)) 4 (by decide : ¬ (4 : Nat) = 17) h4
  have hCond : EvE Gen.prog s1
      (.bin .ne (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0))) (boolVal false) := by
    have e : EvE Gen.prog s1
        (.bin .ne (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0)))
        (boolVal (decide (IntTy.toInt ⟨32, true⟩ 0 ≠ IntTy.toInt ⟨32, true⟩ 0))) :=
      EvE.bin (EvE.var h17_1) (EvE.const _) (bin_i32_ne _ _)
    rw [show (decide (IntTy.toInt ⟨32, true⟩ 0 ≠ IntTy.toInt ⟨32, true⟩ 0)) = false from by decide] at e
    exact e
  have hIte : ExS Gen.prog s1
      (.ite (.bin .ne (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0)))
        (.ret (some (.var 17))) .skip) .normal s1 :=
    ExS.ite hCond truthy_false ExS.skip
  -- the decode call
  obtain ⟨gout, hInfo3, hg_len⟩ := hHdrExp.1 hSig hLay hG0 hAcr hPcr
  have hUntH : ∀ j, j ≠ 3 → sH.mem j = m j := hHdrExp.2 hSig hLay hG0 hAcr hPcr
  obtain ⟨hpx, hpx64, hrow64, houtsz64, hpalok, hpal64, hwv, hhtwv, hpicv, hpentrv, hbcv,
    hwidth, htopd, hchc, hbcdisc, hrsd, _hrs_ge_w⟩ :=
    bmpHeaderInfoOf_stage_facts d hlen hG0 hAcr hPcr
  have hmD : s1.mem bd = some d := by
    rw [show s1.mem = sH.mem from rfl, hUntH bd (Ne.symm hb3)]; exact hm
  have hobD : s1.mem bo = some out := by
    rw [show s1.mem = sH.mem from rfl, hUntH bo (Ne.symm h3o)]; exact hoo
  have hinfoD : s1.mem 3 = some (bmpHeaderFinalBlock d gout) := by
    rw [show s1.mem = sH.mem from rfl]; exact hInfo3
  have hDArgs : EvArgs Gen.prog s1 [(.var 0), (.var 1), (.var 2), (.var 3), (.var 4)]
      [.ptr bd 0, .int ⟨64, false⟩ d.length, .ptr 3 0, .ptr bo 0, .int ⟨64, false⟩ out.length] :=
    EvArgs.cons (EvE.var h0_1) (EvArgs.cons (EvE.var h1_1) (EvArgs.cons (EvE.var h2_1)
      (EvArgs.cons (EvE.var h3_1) (EvArgs.cons (EvE.var h4_1) EvArgs.nil))))
  obtain ⟨sD, hDecBody, hDecMem⟩ :=
    ni_bmp_decode_into_ok_exs s1.mem d out bd bo hmD hlen hobD hbdo h3o hb3
      (bmpHeaderFinalBlock d gout) hinfoD (bmpHeaderFinalBlock_length d gout hg_len) (bmpHeaderInfoOf d)
      (bmpHeaderFinalBlock_rows d gout hg_len) hrow64
      (bmpHeaderFinalBlock_outSize d gout hg_len) rfl houtsz64
      (bmpHeaderFinalBlock_paletteOffset d gout hg_len) hpal64
      (bmpHeaderFinalBlock_width d gout hg_len) hwv
      (bmpHeaderFinalBlock_height d gout hg_len) hhtwv
      (bmpHeaderFinalBlock_pixelOffset d gout hg_len) hpicv
      (bmpHeaderFinalBlock_paletteEntries d gout hg_len) hpentrv
      (bmpHeaderFinalBlock_bitCount d gout hg_len) hbcv
      hbcdisc
      (bmpHeaderFinalBlock_channels d gout hg_len) hchc rfl
      hrsd
      (bmpHeaderFinalBlock_topDown d gout hg_len) htopd
      hcap hcap64 hpx hpx64 hpalok
      (bmpHeaderInfoOf_px8 d hlen hG0 hAcr hPcr)
      (bmpHeaderInfoOf_pos8 d hlen hG0 hAcr hPcr hokPix)
      (bmpHeaderInfoOf_idx8 d hG0 hokPix)
      hokPix hwidth ro hro
  have hDecCall : ExS Gen.prog s1
      (.call none 16 [(.var 0), (.var 1), (.var 2), (.var 3), (.var 4)]) .normal
      { s1 with mem := sD.mem } :=
    ExS.call_ret hDArgs (show Gen.prog 16 = some Gen.ni_bmp_decode_into from rfl)
      (show Gen.ni_bmp_decode_into.params.length = 5 from rfl) hDecBody
  let s2 : State := { s1 with mem := sD.mem }
  have hRet : ExS Gen.prog s2 (.ret (some (.const (.int ⟨32, true⟩ 0))))
      (.ret (some (.int ⟨32, true⟩ 0))) s2 :=
    ExS.ret (EvE.const _)
  refine ⟨s2, ?_, ?_, hSpec⟩
  · rw [hCode0]
    exact ExS.seq hHdrCall (ExS.seq hIte (ExS.seq hDecCall hRet))
  · exact hDecMem


end NANO.C.Proofs
