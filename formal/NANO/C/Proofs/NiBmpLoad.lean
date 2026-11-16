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

end NANO.C.Proofs
