/-
  Spec-side facts for the final composition of `ni_bmp_header`:
  the stage-4 verdicts under in-range geometry bounds, and clean unfoldings
  used by the composed refinement proof.
-/
import NANO.Bmp
import NANO.Spec
import NANO.C.Lemmas
import NANO.C.Proofs.NiGeometryTail
import NANO.C.Proofs.NiBmpHeaderSpecGeo
import NANO.C.Proofs.NiBmpHeaderSpecPalette
import NANO.C.Proofs.NiBmpHeaderArith

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000

open NANO NANO.C NANO.C.Proofs

namespace NANO

/-- Unfolding `bmpOutputArithCode` under in-range bounds: stages 1–4 always
    pass, leaving the truncation decision. -/
theorem arithCode_unfold {width height bitCount channels pixelOffset size : Nat}
    (hW : width ≤ 2147483647) (hB32 : bitCount ≤ 32) (hC : channels ≤ 4)
    (hH : height ≤ 2147483648) :
    bmpOutputArithCode width height bitCount channels pixelOffset size =
      (if pixelOffset > sizeMax - bmpRowStride width bitCount * height ∨
          pixelOffset + bmpRowStride width bitCount * height > size
       then 9 else 0) := by
  have hsMulR : sizeMulOK (bmpRowStride width bitCount) height = true := by
    unfold bmpRowStride; exact sizeMulOK_row_h hW hB32 hH
  unfold bmpOutputArithCode
  simp [sizeMulOK_w_b_gen (show width ≤ 4294967295 by omega) (show bitCount ≤ 65535 by omega),
        sizeMulOK_w_c_gen (show width ≤ 4294967295 by omega) (show channels ≤ 255 by omega),
        sizeMulOK_wc_h hW hC hH, hsMulR]

/-- Under in-range bounds, the arith stage returns `0` or `9`. -/
theorem arithCode_zero_or_nine {width height bitCount channels pixelOffset size : Nat}
    (hW : width ≤ 2147483647) (hB32 : bitCount ≤ 32) (hC : channels ≤ 4)
    (hH : height ≤ 2147483648) :
    bmpOutputArithCode width height bitCount channels pixelOffset size = 0 ∨
    bmpOutputArithCode width height bitCount channels pixelOffset size = 9 := by
  have hsMulR : sizeMulOK (bmpRowStride width bitCount) height = true := by
    unfold bmpRowStride; exact sizeMulOK_row_h hW hB32 hH
  unfold bmpOutputArithCode
  simp only [sizeMulOK_w_b_gen (show width ≤ 4294967295 by omega) (show bitCount ≤ 65535 by omega),
             sizeMulOK_w_c_gen (show width ≤ 4294967295 by omega) (show channels ≤ 255 by omega),
             sizeMulOK_wc_h hW hC hH, hsMulR]
  by_cases h : pixelOffset > sizeMax - bmpRowStride width bitCount * height ∨
               pixelOffset + bmpRowStride width bitCount * height > size
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl rfl

/-- Unfolding `bmpOutputPaletteCode`: an explicit nested `if`. -/
theorem paletteCode_unfold (bitCount colorsUsed dibSize pixelOffset : Nat) :
    bmpOutputPaletteCode bitCount colorsUsed dibSize pixelOffset =
      (if bitCount = 8 then
         (if (if colorsUsed = 0 then 256 else colorsUsed) = 0 ∨
             (if colorsUsed = 0 then 256 else colorsUsed) > 256 ∨
             14 + dibSize + (if colorsUsed = 0 then 256 else colorsUsed) * 4 > pixelOffset
          then 10 else 0)
        else 0) := by
  unfold bmpOutputPaletteCode
  rfl

/-- `bmpOutputPaletteCode` is `0` or `10`. -/
theorem paletteCode_zero_or_ten (bitCount colorsUsed dibSize pixelOffset : Nat) :
    bmpOutputPaletteCode bitCount colorsUsed dibSize pixelOffset = 0 ∨
    bmpOutputPaletteCode bitCount colorsUsed dibSize pixelOffset = 10 := by
  unfold bmpOutputPaletteCode
  by_cases h8 : bitCount = 8
  · simp only [if_pos h8]
    by_cases h : (if colorsUsed = 0 then 256 else colorsUsed) = 0 ∨
                (if colorsUsed = 0 then 256 else colorsUsed) > 256 ∨
                14 + dibSize + (if colorsUsed = 0 then 256 else colorsUsed) * 4 > pixelOffset
    · rw [if_pos h]; exact Or.inr rfl
    · rw [if_neg h]; exact Or.inl rfl
  · rw [if_neg h8]; exact Or.inl rfl

end NANO
