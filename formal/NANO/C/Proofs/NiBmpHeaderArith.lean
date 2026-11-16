/-
  `ni_bmp_header_arith` — the arithmetic / output-size / truncation stage of
  the BMP header, proved against `bmpOutputArithCode` (the same decision tree).
  On success the two u64 fields of `ni_bmp_info` (row_stride@0, output_size@8)
  are spliced into the block; on failure the block is untouched.
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Lemmas
import NANO.Spec
import NANO.Bmp
import NANO.C.Proofs.Core
import NANO.C.Proofs.NiGeometryTail
import NANO.C.Proofs.Bmp
import NANO.C.Proofs.NiBmpHeaderSpecGeo

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 800000

namespace NANO.C.Proofs
open NANO NANO.C

/-- Stage 4a of `ni_bmp_info`: row_stride@0 and output_size@8 (u64 each). -/
def bmpArithBlock (obl : List UInt8) (rs os : Nat) : List UInt8 :=
  encodeLE 8 rs ++ encodeLE 8 os ++ obl.drop 16

theorem bmpArithBlock_length (obl : List UInt8) (h48 : obl.length = 48) (rs os : Nat) :
    (bmpArithBlock obl rs os).length = 48 := by
  simp [bmpArithBlock, h48, encodeLE_length, List.length_drop, List.length_append]

/-- Two u64 stores into a 48-byte `ni_bmp_info` block (row_stride@0, output_size@8). -/
theorem bmp_arith_stores_exs (m : Mem) (obl : List UInt8) (hob : m 3 = some obl) (h48 : obl.length = 48)
    (ro : Bool) (hro : ro = false)
    (l : Locals) (hl6 : l 6 = some (.ptr 3 0))
    (rs os : Nat) (hrs : rs < 18446744073709551616) (hos : os < 18446744073709551616)
    (hl7 : l 7 = some (Val.int ⟨64, false⟩ rs)) (hl8 : l 8 = some (Val.int ⟨64, false⟩ os)) :
    ∃ s', ExS Gen.prog ⟨l, m, ro⟩
      (.seq (.store (.int ⟨64, false⟩) (.field (.var 6) 0) (.var 7))
            (.seq (.store (.int ⟨64, false⟩) (.field (.var 6) 8) (.var 8))
                  (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 0))))))
      (Outcome.ret (some (.int ⟨32, true⟩ 0))) s' ∧
    s'.mem 3 = some (bmpArithBlock obl rs os) ∧
    (∀ j, j ≠ 3 → s'.mem j = m j) := by
  have h2 : EvE Gen.prog ⟨l, m, ro⟩ (.var 6) (.ptr 3 0) := EvE.var hl6
  have h7 : EvE Gen.prog ⟨l, m, ro⟩ (.var 7) (.int ⟨64, false⟩ rs) := EvE.var hl7
  have h8 : EvE Gen.prog ⟨l, m, ro⟩ (.var 8) (.int ⟨64, false⟩ os) := EvE.var hl8
  have hr0 : EvE Gen.prog ⟨l, m, ro⟩ (.field (.var 6) 0) (.ptr 3 0) :=
    EvE.field h2 (ptrAddN_ok hob (by omega))
  have hS1 : ExS Gen.prog ⟨l, m, ro⟩ (.store (.int ⟨64, false⟩) (.field (.var 6) 0) (.var 7)) .normal
      { locals := l, mem := m.upd 3 (obl.take 0 ++ encodeLE 8 rs ++ obl.drop 8), ro := ro } :=
    ExS.store hr0 h7 hro (store_field_u64 m 3 obl hob h48 0 (by omega) rs hrs)
  let b1 : List UInt8 := obl.take 0 ++ encodeLE 8 rs ++ obl.drop 8
  have hb1 : b1.length = 48 := by
    simp [b1, h48, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have h2m1 : (m.upd 3 b1) 3 = some b1 := rfl
  let s1 : State := { locals := l, mem := m.upd 3 b1, ro := ro }
  have h2s : EvE Gen.prog s1 (.var 6) (.ptr 3 0) := EvE.var hl6
  have h8s : EvE Gen.prog s1 (.var 8) (.int ⟨64, false⟩ os) := EvE.var hl8
  have hr8 : EvE Gen.prog s1 (.field (.var 6) 8) (.ptr 3 8) :=
    EvE.field h2s (ptrAddN_ok h2m1 (by omega))
  have hS2 : ExS Gen.prog s1 (.store (.int ⟨64, false⟩) (.field (.var 6) 8) (.var 8)) .normal
      { s1 with mem := (m.upd 3 b1).upd 3 (b1.take 8 ++ encodeLE 8 os ++ b1.drop 16) } :=
    ExS.store hr8 h8s hro (store_field_u64 (m.upd 3 b1) 3 b1 h2m1 hb1 8 (by omega) os hos)
  let b2 : List UInt8 := b1.take 8 ++ encodeLE 8 os ++ b1.drop 16
  have hb2 : b2.length = 48 := by
    simp [b2, hb1, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have h2m2 : ((m.upd 3 b1).upd 3 b2) 3 = some b2 := rfl
  let s2 : State := { s1 with mem := (m.upd 3 b1).upd 3 b2 }
  have hret : ExS Gen.prog s2 (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 0))))
      (Outcome.ret (some (.int ⟨32, true⟩ 0))) s2 :=
    ExS.ret (EvE.const (v := (.int ⟨32, true⟩ 0)))
  have hb1' : b1 = obl.take 0 ++ encodeLE 8 rs ++ obl.drop 8 := rfl
  have hb2' : b2 = b1.take 8 ++ encodeLE 8 os ++ b1.drop 16 := rfl
  have hblk : (b2) = bmpArithBlock obl rs os := by
    have e8 : (encodeLE 8 rs).length = 8 := encodeLE_length 8 rs
    simp [bmpArithBlock, b1, b2, hb1', hb2', h48, e8, encodeLE_length,
          List.take_append, List.drop_append, List.take_left', List.drop_left',
          List.take_take, List.drop_drop, List.nil_append, List.append_nil, List.drop_zero]
  have hfin : ((m.upd 3 b1).upd 3 b2) = m.upd 3 (bmpArithBlock obl rs os) := by
    rw [mem_upd_same, hblk]
  refine ⟨s2, ExS.seq hS1 (ExS.seq hS2 hret), ?_, ?_⟩
  · show s2.mem 3 = some (bmpArithBlock obl rs os)
    rw [show s2.mem = ((m.upd 3 b1).upd 3 b2) from rfl, hfin]
    rfl
  · intro j hj
    show (((m.upd 3 b1).upd 3 b2)) j = m j
    rw [mem_upd_same]
    exact mem_upd_other_blk m 3 j _ hj

/-- Row stride, matching `bmpOutputArithCode`'s internal expression. -/
theorem bmpRowStride_def (W b : Nat) : bmpRowStride W b = ((W * b + 31) / 32) * 4 := rfl

/-- The bound used throughout: widths survive a u32 cast, bit counts a u16. -/
theorem mulFits_w_b_general {width bitCount : Nat}
    (hW : width ≤ 4294967295) (hB : bitCount ≤ 65535) :
    (width = 0 ∨ bitCount ≤ 18446744073709551615 / width) := by
  by_cases h0 : width = 0
  · exact Or.inl h0
  · right
    rw [Nat.le_div_iff_mul_le (by omega)]
    have hle := Nat.mul_le_mul hB hW
    have hlit : 65535 * 4294967295 = 281470681677825 := by decide
    rw [hlit] at hle
    omega

theorem mulFits_w_c_general {width channels : Nat}
    (hW : width ≤ 4294967295) (hC : channels ≤ 255) :
    (width = 0 ∨ channels ≤ 18446744073709551615 / width) := by
  by_cases h0 : width = 0
  · exact Or.inl h0
  · right
    rw [Nat.le_div_iff_mul_le (by omega)]
    have hle := Nat.mul_le_mul hC hW
    have hlit : 255 * 4294967295 = 1095216660225 := by decide
    rw [hlit] at hle
    omega

theorem sizeMulOK_w_b_gen {width bitCount : Nat}
    (hW : width ≤ 4294967295) (hB : bitCount ≤ 65535) :
    sizeMulOK width bitCount = true := by
  unfold sizeMulOK
  by_cases h0 : width = 0
  · rw [h0]; rfl
  · have h1 : (width == 0) = false := decide_eq_false (by omega)
    have h2 : decide (bitCount ≤ sizeMax / width) = true :=
      decide_eq_true_eq.mpr ((mulFits_w_b_general hW hB).resolve_left h0)
    simp [h1, h2]

theorem sizeMulOK_w_c_gen {width channels : Nat}
    (hW : width ≤ 4294967295) (hC : channels ≤ 255) :
    sizeMulOK width channels = true := by
  unfold sizeMulOK
  by_cases h0 : width = 0
  · rw [h0]; rfl
  · have h1 : (width == 0) = false := decide_eq_false (by omega)
    have h2 : decide (channels ≤ sizeMax / width) = true :=
      decide_eq_true_eq.mpr ((mulFits_w_c_general hW hC).resolve_left h0)
    simp [h1, h2]


theorem sizeMulOK_wc_h_gen {width channels height : Nat}
    (hStage3 : (width * channels = 0 ∨ height ≤ sizeMax / (width * channels))) :
    sizeMulOK (width * channels) height = true := by
  unfold sizeMulOK
  by_cases hz : width * channels = 0
  · rw [show (width * channels == 0) = true from decide_eq_true_eq.mpr hz]; rfl
  · have h1 : (width * channels == 0) = false := decide_eq_false hz
    have hfit : height ≤ sizeMax / (width * channels) := by
      rcases hStage3 with h0 | hfit
      · exact absurd h0 hz
      · exact hfit
    have h2 : decide (height ≤ sizeMax / (width * channels)) = true := decide_eq_true_eq.mpr hfit
    simp [h1, h2]

theorem sizeMulOK_row_h_gen {rowStride height : Nat}
    (hStage4 : (rowStride = 0 ∨ height ≤ sizeMax / rowStride)) :
    sizeMulOK rowStride height = true := by
  unfold sizeMulOK
  by_cases hz : rowStride = 0
  · rw [show (rowStride == 0) = true from decide_eq_true_eq.mpr hz]; rfl
  · have h1 : (rowStride == 0) = false := decide_eq_false hz
    have hfit : height ≤ sizeMax / rowStride := by
      rcases hStage4 with h0 | hfit
      · exact absurd h0 hz
      · exact hfit
    have h2 : decide (height ≤ sizeMax / rowStride) = true := decide_eq_true_eq.mpr hfit
    simp [h1, h2]

theorem sizeMulOK_wc_h_false_gen {width channels height : Nat} (hz : 0 < width * channels)
    (hBad : ¬ height ≤ sizeMax / (width * channels)) :
    sizeMulOK (width * channels) height = false := by
  unfold sizeMulOK
  have h1 : (width * channels == 0) = false := decide_eq_false (by omega)
  have h2 : decide (height ≤ sizeMax / (width * channels)) = false := decide_eq_false_iff_not.mpr hBad
  simp [h1, h2]

theorem sizeMulOK_row_h_false_gen {rowStride height : Nat} (hz : 0 < rowStride)
    (hBad : ¬ height ≤ sizeMax / rowStride) :
    sizeMulOK rowStride height = false := by
  unfold sizeMulOK
  have h1 : (rowStride == 0) = false := decide_eq_false (by omega)
  have h2 : decide (height ≤ sizeMax / rowStride) = false := decide_eq_false_iff_not.mpr hBad
  simp [h1, h2]

/-- `ni_bmp_header_arith` returns `bmpOutputArithCode`. -/
theorem ni_bmp_header_arith_exs (m : Mem)
    (width height bitCount channels pixelOffset size : Nat)
    (hW : width < 4294967296) (hH : height < 4294967296) (hB : bitCount < 65536)
    (hC : channels < 256) (hP : pixelOffset < 4294967296) (hS : size < 2 ^ 64)
    (obl : List UInt8) (hob : m 3 = some obl) (h48 : obl.length = 48) (ro : Bool)
    (hro : ro = false) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals [0, 1, 2, 3, 4, 5, 6]
        [.int ⟨32, false⟩ width, .int ⟨32, false⟩ height, .int ⟨16, false⟩ bitCount,
         .int ⟨8, false⟩ channels, .int ⟨32, false⟩ pixelOffset, .int ⟨64, false⟩ size, .ptr 3 0], m, ro⟩
      Gen.ni_bmp_header_arith.body
      (.ret (some (.int ⟨32, true⟩ (bmpOutputArithCode width height bitCount channels pixelOffset size)))) s' ∧
    (bmpOutputArithCode width height bitCount channels pixelOffset size = 0 →
      s'.mem 3 = some (bmpArithBlock obl (bmpRowStride width bitCount) (bmpOutSize width channels height))) ∧
    (bmpOutputArithCode width height bitCount channels pixelOffset size = 0 →
      ∀ j, j ≠ 3 → s'.mem j = m j) := by
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  let s0 : State :=
    ⟨frameLocals [0, 1, 2, 3, 4, 5, 6]
      [.int ⟨32, false⟩ width, .int ⟨32, false⟩ height, .int ⟨16, false⟩ bitCount,
       .int ⟨8, false⟩ channels, .int ⟨32, false⟩ pixelOffset, .int ⟨64, false⟩ size, .ptr 3 0], m, ro⟩
  have hl0 : frameLocals [0, 1, 2, 3, 4, 5, 6]
      [.int ⟨32, false⟩ width, .int ⟨32, false⟩ height, .int ⟨16, false⟩ bitCount,
       .int ⟨8, false⟩ channels, .int ⟨32, false⟩ pixelOffset, .int ⟨64, false⟩ size, .ptr 3 0]
      0 = some (.int ⟨32, false⟩ width) := rfl
  have hl1 : frameLocals [0, 1, 2, 3, 4, 5, 6]
      [.int ⟨32, false⟩ width, .int ⟨32, false⟩ height, .int ⟨16, false⟩ bitCount,
       .int ⟨8, false⟩ channels, .int ⟨32, false⟩ pixelOffset, .int ⟨64, false⟩ size, .ptr 3 0]
      1 = some (.int ⟨32, false⟩ height) := rfl
  have hl2 : frameLocals [0, 1, 2, 3, 4, 5, 6]
      [.int ⟨32, false⟩ width, .int ⟨32, false⟩ height, .int ⟨16, false⟩ bitCount,
       .int ⟨8, false⟩ channels, .int ⟨32, false⟩ pixelOffset, .int ⟨64, false⟩ size, .ptr 3 0]
      2 = some (.int ⟨16, false⟩ bitCount) := rfl
  have hl3 : frameLocals [0, 1, 2, 3, 4, 5, 6]
      [.int ⟨32, false⟩ width, .int ⟨32, false⟩ height, .int ⟨16, false⟩ bitCount,
       .int ⟨8, false⟩ channels, .int ⟨32, false⟩ pixelOffset, .int ⟨64, false⟩ size, .ptr 3 0]
      3 = some (.int ⟨8, false⟩ channels) := rfl
  have hl4 : frameLocals [0, 1, 2, 3, 4, 5, 6]
      [.int ⟨32, false⟩ width, .int ⟨32, false⟩ height, .int ⟨16, false⟩ bitCount,
       .int ⟨8, false⟩ channels, .int ⟨32, false⟩ pixelOffset, .int ⟨64, false⟩ size, .ptr 3 0]
      4 = some (.int ⟨32, false⟩ pixelOffset) := rfl
  have hl5 : frameLocals [0, 1, 2, 3, 4, 5, 6]
      [.int ⟨32, false⟩ width, .int ⟨32, false⟩ height, .int ⟨16, false⟩ bitCount,
       .int ⟨8, false⟩ channels, .int ⟨32, false⟩ pixelOffset, .int ⟨64, false⟩ size, .ptr 3 0]
      5 = some (.int ⟨64, false⟩ size) := rfl
  have hl6 : frameLocals [0, 1, 2, 3, 4, 5, 6]
      [.int ⟨32, false⟩ width, .int ⟨32, false⟩ height, .int ⟨16, false⟩ bitCount,
       .int ⟨8, false⟩ channels, .int ⟨32, false⟩ pixelOffset, .int ⟨64, false⟩ size, .ptr 3 0]
      6 = some (.ptr 3 0) := rfl
  have hW64 : width < 2 ^ 64 := by omega
  have hH64 : height < 2 ^ 64 := by omega
  have hB64 : bitCount < 2 ^ 64 := by omega
  have hC64 : channels < 2 ^ 64 := by omega
  have hP64 : pixelOffset < 2 ^ 64 := by omega
  have hWB : width * bitCount ≤ 281470681677825 := by
    have hle := Nat.mul_le_mul (show width ≤ 4294967295 from by omega) (show bitCount ≤ 65535 from by omega)
    have hlit : 4294967295 * 65535 = 281470681677825 := by decide
    rwa [hlit] at hle
  have hWB31 : width * bitCount + 31 < 2 ^ 64 := by omega
  have hWC : width * channels ≤ 1095216660225 := by
    have hle := Nat.mul_le_mul (show width ≤ 4294967295 from by omega) (show channels ≤ 255 from by omega)
    have hlit : 4294967295 * 255 = 1095216660225 := by decide
    rwa [hlit] at hle
  -- ========== Stage 1: mul_fits(width, bitCount) — always succeeds ==========
  have vc0 : EvE Gen.prog s0 (.cast ⟨64, false⟩ (.var 0)) (.int ⟨64, false⟩ width) :=
    EvE.cast (EvE.var hl0) (u32_u64_cast width (by omega))
  have vc2 : EvE Gen.prog s0 (.cast ⟨64, false⟩ (.var 2)) (.int ⟨64, false⟩ bitCount) :=
    EvE.cast (EvE.var hl2) (u16_u64_cast bitCount (by omega))
  obtain ⟨sMF1, exMF1⟩ := ni_bmp_mul_fits_exs s0.mem width bitCount hW64 hB64 true
  have hFits1 : width = 0 ∨ bitCount ≤ 18446744073709551615 / width :=
    mulFits_w_b_general (by omega) (by omega)
  have hCall1 : EvE Gen.prog s0
      (.call 11 [(.cast ⟨64, false⟩ (.var 0)), (.cast ⟨64, false⟩ (.var 2))])
      (.int ⟨32, true⟩ 1) := by
    have hex : EvE Gen.prog s0
        (.call 11 [(.cast ⟨64, false⟩ (.var 0)), (.cast ⟨64, false⟩ (.var 2))])
        (.int ⟨32, true⟩ (if width = 0 ∨ bitCount ≤ 18446744073709551615 / width then 1 else 0)) :=
      EvE.call (EvArgs.cons vc0 (EvArgs.cons vc2 EvArgs.nil))
        (show Gen.prog 11 = some Gen.ni_bmp_mul_fits from rfl)
        (show Gen.ni_bmp_mul_fits.params.length = 2 from rfl)
        exMF1
    rwa [if_pos hFits1] at hex
  have hNot1 : EvE Gen.prog s0
      (.un .lnot ⟨32, true⟩ (.call 11 [(.cast ⟨64, false⟩ (.var 0)), (.cast ⟨64, false⟩ (.var 2))]))
      (boolVal false) := by
    have he : evalUn .lnot ⟨32, true⟩ (.int ⟨32, true⟩ 1) = .ok (boolVal false) := by
      simp [evalUn, truthy]
    exact EvE.un hCall1 he
  have hSkip1 : ExS Gen.prog s0
      (.ite (.un .lnot ⟨32, true⟩ (.call 11 [(.cast ⟨64, false⟩ (.var 0)), (.cast ⟨64, false⟩ (.var 2))]))
        (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 7)))) .skip)
      .normal s0 :=
    ExS.ite hNot1 truthy_false ExS.skip
  -- ========== row_stride computation ==========
  have hSet7 : ExS Gen.prog s0
      (.set 7 (.bin .shl (some ⟨64, false⟩)
        (.bin .shr (some ⟨64, false⟩)
          (.bin .add (some ⟨64, false⟩)
            (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 0)) (.cast ⟨64, false⟩ (.var 2)))
            (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 31))))
          (.const (.int ⟨32, false⟩ 5)))
        (.const (.int ⟨32, false⟩ 2))))
      .normal { s0 with locals := s0.locals.upd 7 (.int ⟨64, false⟩ (bmpRowStride width bitCount)) } := by
    have hWBlt : width * bitCount < 2 ^ 64 := by omega
    have h1 : EvE Gen.prog s0 (.cast ⟨64, false⟩ (.var 0)) (.int ⟨64, false⟩ width) := vc0
    have h2 : EvE Gen.prog s0 (.cast ⟨64, false⟩ (.var 2)) (.int ⟨64, false⟩ bitCount) := vc2
    have hMul : EvE Gen.prog s0
        (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 0)) (.cast ⟨64, false⟩ (.var 2)))
        (.int ⟨64, false⟩ (width * bitCount)) :=
      EvE.bin h1 h2 (bin_u64_mul width bitCount hWBlt)
    have hcast31 : EvE Gen.prog s0 (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 31))) (.int ⟨64, false⟩ 31) :=
      EvE.cast (EvE.const _) (u32_u64_cast 31 (by omega))
    have hAdd : EvE Gen.prog s0
        (.bin .add (some ⟨64, false⟩)
          (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 0)) (.cast ⟨64, false⟩ (.var 2)))
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 31))))
        (.int ⟨64, false⟩ (width * bitCount + 31)) :=
      EvE.bin hMul hcast31 (bin_u64_add (width * bitCount) 31 hWB31)
    have hShr : EvE Gen.prog s0
        (.bin .shr (some ⟨64, false⟩)
          (.bin .add (some ⟨64, false⟩)
            (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 0)) (.cast ⟨64, false⟩ (.var 2)))
            (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 31))))
          (.const (.int ⟨32, false⟩ 5)))
        (.int ⟨64, false⟩ ((width * bitCount + 31) / 2 ^ 5)) :=
      EvE.bin hAdd (EvE.const _) (bin_u64_shr_5_c32 (width * bitCount + 31))
    have hShl : EvE Gen.prog s0
        (.bin .shl (some ⟨64, false⟩)
          (.bin .shr (some ⟨64, false⟩)
            (.bin .add (some ⟨64, false⟩)
              (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 0)) (.cast ⟨64, false⟩ (.var 2)))
              (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 31))))
            (.const (.int ⟨32, false⟩ 5)))
          (.const (.int ⟨32, false⟩ 2)))
        (.int ⟨64, false⟩ (((width * bitCount + 31) / 2 ^ 5) * 4)) :=
      EvE.bin hShr (EvE.const _) (bin_u64_shl_2_c32 ((width * bitCount + 31) / 2 ^ 5) (by omega))
    have eqn : ((width * bitCount + 31) / 2 ^ 5) * 4 = bmpRowStride width bitCount := by
      have e52 : (2 : Nat) ^ 5 = 32 := by decide
      rw [e52]
      rfl
    rw [eqn] at hShl
    exact ExS.set hShl
  let s1 : State := { s0 with locals := s0.locals.upd 7 (.int ⟨64, false⟩ (bmpRowStride width bitCount)) }
  have hl6_1 : s1.locals 6 = some (.ptr 3 0) := rfl
  have hl7_1 : s1.locals 7 = some (.int ⟨64, false⟩ (bmpRowStride width bitCount)) := rfl
  -- ========== Stage 2: mul_fits(width, channels) — always succeeds ==========
  have vc0_1 : EvE Gen.prog s1 (.cast ⟨64, false⟩ (.var 0)) (.int ⟨64, false⟩ width) :=
    EvE.cast (EvE.var (show s1.locals 0 = some (.int ⟨32, false⟩ width) from rfl))
      (u32_u64_cast width (by omega))
  have vc3_1 : EvE Gen.prog s1 (.cast ⟨64, false⟩ (.var 3)) (.int ⟨64, false⟩ channels) :=
    EvE.cast (EvE.var (show s1.locals 3 = some (.int ⟨8, false⟩ channels) from rfl))
      (by simp [evalCast, IntTy.modulus, IntTy.wrap, Int.ofNat_lt,
                show (channels : Nat) < 18446744073709551616 from by omega])
  obtain ⟨sMF2, exMF2⟩ := ni_bmp_mul_fits_exs s1.mem width channels hW64 hC64 true
  have hFits2 : width = 0 ∨ channels ≤ 18446744073709551615 / width :=
    mulFits_w_c_general (by omega) (by omega)
  have hCall2 : EvE Gen.prog s1
      (.call 11 [(.cast ⟨64, false⟩ (.var 0)), (.cast ⟨64, false⟩ (.var 3))])
      (.int ⟨32, true⟩ 1) := by
    have hex : EvE Gen.prog s1
        (.call 11 [(.cast ⟨64, false⟩ (.var 0)), (.cast ⟨64, false⟩ (.var 3))])
        (.int ⟨32, true⟩ (if width = 0 ∨ channels ≤ 18446744073709551615 / width then 1 else 0)) :=
      EvE.call (EvArgs.cons vc0_1 (EvArgs.cons vc3_1 EvArgs.nil))
        (show Gen.prog 11 = some Gen.ni_bmp_mul_fits from rfl)
        (show Gen.ni_bmp_mul_fits.params.length = 2 from rfl)
        exMF2
    rwa [if_pos hFits2] at hex
  have hNot2 : EvE Gen.prog s1
      (.un .lnot ⟨32, true⟩ (.call 11 [(.cast ⟨64, false⟩ (.var 0)), (.cast ⟨64, false⟩ (.var 3))]))
      (boolVal false) := by
    have he : evalUn .lnot ⟨32, true⟩ (.int ⟨32, true⟩ 1) = .ok (boolVal false) := by
      simp [evalUn, truthy]
    exact EvE.un hCall2 he
  have hSkip2 : ExS Gen.prog s1
      (.ite (.un .lnot ⟨32, true⟩ (.call 11 [(.cast ⟨64, false⟩ (.var 0)), (.cast ⟨64, false⟩ (.var 3))]))
        (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 8)))) .skip)
      .normal s1 :=
    ExS.ite hNot2 truthy_false ExS.skip
  -- ========== Stage 3: output_size = width * channels; mul_fits(output_size, height) ==========
  have hSet8a : ExS Gen.prog s1
      (.set 8 (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 0)) (.cast ⟨64, false⟩ (.var 3))))
      .normal { s1 with locals := s1.locals.upd 8 (.int ⟨64, false⟩ (width * channels)) } := by
    have hWClt : width * channels < 2 ^ 64 := by omega
    exact ExS.set (EvE.bin vc0_1 vc3_1 (bin_u64_mul width channels hWClt))
  let s2 : State := { s1 with locals := s1.locals.upd 8 (.int ⟨64, false⟩ (width * channels)) }
  have hl6_2 : s2.locals 6 = some (.ptr 3 0) := rfl
  have hl7_2 : s2.locals 7 = some (.int ⟨64, false⟩ (bmpRowStride width bitCount)) := rfl
  have hl8_2 : s2.locals 8 = some (.int ⟨64, false⟩ (width * channels)) := rfl
  have vc1_2 : EvE Gen.prog s2 (.cast ⟨64, false⟩ (.var 1)) (.int ⟨64, false⟩ height) :=
    EvE.cast (EvE.var (show s2.locals 1 = some (.int ⟨32, false⟩ height) from rfl))
      (u32_u64_cast height (by omega))
  have v8_2 : EvE Gen.prog s2 (.var 8) (.int ⟨64, false⟩ (width * channels)) := EvE.var hl8_2
  have hWClt2 : width * channels < 2 ^ 64 := by omega
  classical
  by_cases hStage3 : (width * channels = 0 ∨ height ≤ 18446744073709551615 / (width * channels))
  · -- stage 3 passes
    obtain ⟨sMF3, exMF3⟩ := ni_bmp_mul_fits_exs s2.mem (width * channels) height hWClt2 hH64 true
    have hCall3 : EvE Gen.prog s2
        (.call 11 [(.var 8), (.cast ⟨64, false⟩ (.var 1))])
        (.int ⟨32, true⟩ 1) := by
      have hex : EvE Gen.prog s2
          (.call 11 [(.var 8), (.cast ⟨64, false⟩ (.var 1))])
          (.int ⟨32, true⟩ (if width * channels = 0 ∨ height ≤ 18446744073709551615 / (width * channels) then 1 else 0)) :=
        EvE.call (EvArgs.cons v8_2 (EvArgs.cons vc1_2 EvArgs.nil))
          (show Gen.prog 11 = some Gen.ni_bmp_mul_fits from rfl)
          (show Gen.ni_bmp_mul_fits.params.length = 2 from rfl)
          exMF3
      rwa [if_pos hStage3] at hex
    have hNot3 : EvE Gen.prog s2
        (.un .lnot ⟨32, true⟩ (.call 11 [(.var 8), (.cast ⟨64, false⟩ (.var 1))]))
        (boolVal false) := by
      have he : evalUn .lnot ⟨32, true⟩ (.int ⟨32, true⟩ 1) = .ok (boolVal false) := by
        simp [evalUn, truthy]
      exact EvE.un hCall3 he
    have hSkip3 : ExS Gen.prog s2
        (.ite (.un .lnot ⟨32, true⟩ (.call 11 [(.var 8), (.cast ⟨64, false⟩ (.var 1))]))
          (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 8)))) .skip)
        .normal s2 :=
      ExS.ite hNot3 truthy_false ExS.skip
    -- ========== output_size = output_size * height ==========
    have hWCH : (width * channels) * height ≤ 18446744073709551615 := by
      rcases hStage3 with h0 | hfit
      · rw [h0]; simp
      · calc (width * channels) * height ≤ width * channels * (18446744073709551615 / (width * channels)) := Nat.mul_le_mul_left _ hfit
          _ ≤ 18446744073709551615 := Nat.mul_div_le _ _
    have hSet8b : ExS Gen.prog s2
        (.set 8 (.bin .mul (some ⟨64, false⟩) (.var 8) (.cast ⟨64, false⟩ (.var 1))))
        .normal { s2 with locals := s2.locals.upd 8 (.int ⟨64, false⟩ (width * channels * height)) } := by
      have hmul : EvE Gen.prog s2
          (.bin .mul (some ⟨64, false⟩) (.var 8) (.cast ⟨64, false⟩ (.var 1)))
          (.int ⟨64, false⟩ (width * channels * height)) :=
        EvE.bin v8_2 vc1_2 (bin_u64_mul (width * channels) height (Nat.lt_of_le_of_lt hWCH (by decide)))
      exact ExS.set hmul
    let s3 : State := { s2 with locals := s2.locals.upd 8 (.int ⟨64, false⟩ (width * channels * height)) }
    have hl6_3 : s3.locals 6 = some (.ptr 3 0) := rfl
    have hl7_3 : s3.locals 7 = some (.int ⟨64, false⟩ (bmpRowStride width bitCount)) := rfl
    have hl8_3 : s3.locals 8 = some (.int ⟨64, false⟩ (width * channels * height)) := rfl
    have hl9_3 := hl8_3
    -- ========== Stage 4: mul_fits(row_stride, height) ==========
    have v7_3 : EvE Gen.prog s3 (.var 7) (.int ⟨64, false⟩ (bmpRowStride width bitCount)) := EvE.var hl7_3
    have vc1_3 : EvE Gen.prog s3 (.cast ⟨64, false⟩ (.var 1)) (.int ⟨64, false⟩ height) :=
      EvE.cast (EvE.var (show s3.locals 1 = some (.int ⟨32, false⟩ height) from rfl))
        (u32_u64_cast height (by omega))
    have hRowStrideBound : bmpRowStride width bitCount ≤ 35183835209732 := by
      have hWB2 : width * bitCount + 31 ≤ 281470681677856 := by omega
      have h2 : (width * bitCount + 31) / 32 ≤ 8795958802433 := by
        rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)]
        have hlit : 8795958802433 * 32 = 281470681677856 := by decide
        omega
      have h3 : bmpRowStride width bitCount = ((width * bitCount + 31) / 32) * 4 := rfl
      omega
    have hRowStride64 : bmpRowStride width bitCount < 2 ^ 64 := by omega
    classical
    by_cases hStage4 : (bmpRowStride width bitCount = 0 ∨ height ≤ 18446744073709551615 / bmpRowStride width bitCount)
    · obtain ⟨sMF4, exMF4⟩ := ni_bmp_mul_fits_exs s3.mem (bmpRowStride width bitCount) height hRowStride64 hH64 true
      have hCall4 : EvE Gen.prog s3
          (.call 11 [(.var 7), (.cast ⟨64, false⟩ (.var 1))])
          (.int ⟨32, true⟩ 1) := by
        have hex : EvE Gen.prog s3
            (.call 11 [(.var 7), (.cast ⟨64, false⟩ (.var 1))])
            (.int ⟨32, true⟩ (if bmpRowStride width bitCount = 0 ∨
              height ≤ 18446744073709551615 / bmpRowStride width bitCount then 1 else 0)) :=
          EvE.call (EvArgs.cons v7_3 (EvArgs.cons vc1_3 EvArgs.nil))
            (show Gen.prog 11 = some Gen.ni_bmp_mul_fits from rfl)
            (show Gen.ni_bmp_mul_fits.params.length = 2 from rfl)
            exMF4
        rwa [if_pos hStage4] at hex
      have hNot4 : EvE Gen.prog s3
          (.un .lnot ⟨32, true⟩ (.call 11 [(.var 7), (.cast ⟨64, false⟩ (.var 1))]))
          (boolVal false) := by
        have he : evalUn .lnot ⟨32, true⟩ (.int ⟨32, true⟩ 1) = .ok (boolVal false) := by
          simp [evalUn, truthy]
        exact EvE.un hCall4 he
      have hSkip4 : ExS Gen.prog s3
          (.ite (.un .lnot ⟨32, true⟩ (.call 11 [(.var 7), (.cast ⟨64, false⟩ (.var 1))]))
            (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 9)))) .skip)
          .normal s3 :=
        ExS.ite hNot4 truthy_false ExS.skip
      -- ========== rows_bytes = row_stride * height ==========
      have hRowsBytesBound : (bmpRowStride width bitCount * height) ≤ 18446744073709551615 := by
        rcases hStage4 with h0 | hfit
        · rw [h0]; simp
        · calc (bmpRowStride width bitCount * height)
              ≤ bmpRowStride width bitCount * (18446744073709551615 / bmpRowStride width bitCount) :=
                Nat.mul_le_mul_left _ hfit
            _ ≤ 18446744073709551615 := Nat.mul_div_le _ _
      have hSet9 : ExS Gen.prog s3
          (.set 9 (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.var 1))))
          .normal { s3 with locals := s3.locals.upd 9 (.int ⟨64, false⟩ (bmpRowStride width bitCount * height)) } := by
        have hmul : EvE Gen.prog s3
            (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.var 1)))
            (.int ⟨64, false⟩ (bmpRowStride width bitCount * height)) :=
          EvE.bin v7_3 vc1_3 (bin_u64_mul (bmpRowStride width bitCount) height (Nat.lt_of_le_of_lt hRowsBytesBound (by decide)))
        exact ExS.set hmul
      let s4 : State := { s3 with locals := s3.locals.upd 9 (.int ⟨64, false⟩ (bmpRowStride width bitCount * height)) }
      have hl6_4 : s4.locals 6 = some (.ptr 3 0) := rfl
      have hl7_4 : s4.locals 7 = some (.int ⟨64, false⟩ (bmpRowStride width bitCount)) := rfl
      have hl8_4 : s4.locals 8 = some (.int ⟨64, false⟩ (width * channels * height)) := rfl
      have hl9_4 : s4.locals 9 = some (.int ⟨64, false⟩ (bmpRowStride width bitCount * height)) := rfl
      have hl4_4 : s4.locals 4 = some (.int ⟨32, false⟩ pixelOffset) := rfl
      have hl5_4 : s4.locals 5 = some (.int ⟨64, false⟩ size) := rfl
      have hRows64 : (bmpRowStride width bitCount * height) ≤ 18446744073709551615 := hRowsBytesBound
      classical
      by_cases hTruncA : pixelOffset > 18446744073709551615 - (bmpRowStride width bitCount * height)
      · -- truncation check fires via condA → return 9
        have hSpec : bmpOutputArithCode width height bitCount channels pixelOffset size = 9 := by
          have hsMul1 := sizeMulOK_w_b_gen (show width ≤ 4294967295 by omega) (show bitCount ≤ 65535 by omega)
          have hsMul2 := sizeMulOK_w_c_gen (show width ≤ 4294967295 by omega) (show channels ≤ 255 by omega)
          have hsMul3 : sizeMulOK (width * channels) height = true := sizeMulOK_wc_h_gen hStage3
          have hsMul4 : sizeMulOK (bmpRowStride width bitCount) height = true := sizeMulOK_row_h_gen hStage4
          have hTruncA' : pixelOffset > sizeMax - (bmpRowStride width bitCount * height) := hTruncA
          unfold bmpOutputArithCode
          simp [hsMul1, hsMul2, hsMul3, hsMul4, Or.inl hTruncA']
        have hRet9 : ExS Gen.prog s4
            (.ite (.lor
              (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
                (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 9)))
              (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4)) (.var 9)) (.var 5)))
              (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 9)))) .skip)
            (Outcome.ret (some (.int ⟨32, true⟩ 9))) s4 := by
          have hscast : EvE Gen.prog s4 (.cast ⟨64, false⟩ (.var 4)) (.int ⟨64, false⟩ pixelOffset) :=
            EvE.cast (EvE.var hl4_4) (u32_u64_cast pixelOffset (by omega))
          have hscast9 : EvE Gen.prog s4 (.var 9) (.int ⟨64, false⟩ (bmpRowStride width bitCount * height)) := EvE.var hl9_4
          have hscast5 : EvE Gen.prog s4 (.var 5) (.int ⟨64, false⟩ size) := EvE.var hl5_4
          have hsub : EvE Gen.prog s4
              (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 9))
              (.int ⟨64, false⟩ (18446744073709551615 - (bmpRowStride width bitCount * height))) := by
            have he : evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ 18446744073709551615) (.int ⟨64, false⟩ (bmpRowStride width bitCount * height)) =
                .ok (.int ⟨64, false⟩ (18446744073709551615 - (bmpRowStride width bitCount * height))) :=
              NANO.C.bin_u64_sub 18446744073709551615 (bmpRowStride width bitCount * height) (by omega)
            exact EvE.bin (EvE.const _) hscast9 he
          have hlt1 : EvE Gen.prog s4
              (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
                (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 9)))
              (boolVal true) := by
            have eCmp : EvE Gen.prog s4
                (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
                  (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 9)))
                (boolVal (decide (pixelOffset > 18446744073709551615 - (bmpRowStride width bitCount * height)))) :=
              EvE.bin hscast hsub (bin_u64_gt _ _)
            rwa [decide_eq_true_eq.mpr hTruncA] at eCmp
          have he : EvE Gen.prog s4
              (.lor
                (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
                  (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 9)))
                (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4)) (.var 9)) (.var 5)))
              (boolVal true) :=
            EvE.lor_true hlt1 truthy_true
          exact ExS.ite he truthy_true (ExS.ret (EvE.const _))
        refine ⟨s4, ?_, ?_, fun _ _ _ => rfl⟩
        · show ExS Gen.prog s0 Gen.ni_bmp_header_arith.body
              (.ret (some (.int ⟨32, true⟩ (bmpOutputArithCode width height bitCount channels pixelOffset size)))) s4
          rw [hSpec]
          exact ExS.seq hSkip1 (ExS.seq hSet7 (ExS.seq hSkip2
            (ExS.seq hSet8a (ExS.seq hSkip3
              (ExS.seq hSet8b (ExS.seq hSkip4
                (ExS.seq hSet9 (ExS.seq_ret hRet9))))))))
        · intro habs
          rw [hSpec] at habs
          exact absurd habs (by decide)
      · by_cases hTruncB : pixelOffset + (bmpRowStride width bitCount * height) > size
        · -- truncation check fires via condB → return 9
          have hSpec : bmpOutputArithCode width height bitCount channels pixelOffset size = 9 := by
            have hsMul1 := sizeMulOK_w_b_gen (show width ≤ 4294967295 by omega) (show bitCount ≤ 65535 by omega)
            have hsMul2 := sizeMulOK_w_c_gen (show width ≤ 4294967295 by omega) (show channels ≤ 255 by omega)
            have hsMul3 : sizeMulOK (width * channels) height = true := sizeMulOK_wc_h_gen hStage3
            have hsMul4 : sizeMulOK (bmpRowStride width bitCount) height = true := sizeMulOK_row_h_gen hStage4
            have hTruncB' : pixelOffset + (bmpRowStride width bitCount * height) > size := hTruncB
            unfold bmpOutputArithCode
            simp [hsMul1, hsMul2, hsMul3, hsMul4, Or.inr hTruncB']
          have hRet9 : ExS Gen.prog s4
              (.ite (.lor
                (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
                  (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 9)))
                (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4)) (.var 9)) (.var 5)))
                (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 9)))) .skip)
              (Outcome.ret (some (.int ⟨32, true⟩ 9))) s4 := by
            have hscast : EvE Gen.prog s4 (.cast ⟨64, false⟩ (.var 4)) (.int ⟨64, false⟩ pixelOffset) :=
              EvE.cast (EvE.var hl4_4) (u32_u64_cast pixelOffset (by omega))
            have hscast9 : EvE Gen.prog s4 (.var 9) (.int ⟨64, false⟩ (bmpRowStride width bitCount * height)) := EvE.var hl9_4
            have hscast5 : EvE Gen.prog s4 (.var 5) (.int ⟨64, false⟩ size) := EvE.var hl5_4
            have hAddLt : pixelOffset + (bmpRowStride width bitCount * height) < 2 ^ 64 := by
              have h2 : (bmpRowStride width bitCount * height) ≤ 18446744073709551615 := hRows64
              have h1 : pixelOffset ≤ 4294967295 := by omega
              omega
            have hsub : EvE Gen.prog s4
                (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 9))
                (.int ⟨64, false⟩ (18446744073709551615 - (bmpRowStride width bitCount * height))) := by
              have he : evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ 18446744073709551615) (.int ⟨64, false⟩ (bmpRowStride width bitCount * height)) =
                  .ok (.int ⟨64, false⟩ (18446744073709551615 - (bmpRowStride width bitCount * height))) :=
                NANO.C.bin_u64_sub 18446744073709551615 (bmpRowStride width bitCount * height) (by omega)
              exact EvE.bin (EvE.const _) hscast9 he
            have hlt1 : EvE Gen.prog s4
                (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
                  (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 9)))
                (boolVal false) := by
              have eCmp : EvE Gen.prog s4
                  (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
                    (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 9)))
                  (boolVal (decide (pixelOffset > 18446744073709551615 - (bmpRowStride width bitCount * height)))) :=
                EvE.bin hscast hsub (bin_u64_gt _ _)
              rwa [decide_eq_false_iff_not.mpr hTruncA] at eCmp
            have eAdd : EvE Gen.prog s4
                (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4)) (.var 9))
                (.int ⟨64, false⟩ (pixelOffset + (bmpRowStride width bitCount * height))) :=
              EvE.bin hscast hscast9 (bin_u64_add pixelOffset (bmpRowStride width bitCount * height) hAddLt)
            have hlt2 : EvE Gen.prog s4
                (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4)) (.var 9)) (.var 5))
                (boolVal true) := by
              have eCmp : EvE Gen.prog s4
                  (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4)) (.var 9)) (.var 5))
                  (boolVal (decide (pixelOffset + (bmpRowStride width bitCount * height) > size))) :=
                EvE.bin eAdd hscast5 (bin_u64_gt _ _)
              rwa [decide_eq_true_eq.mpr hTruncB] at eCmp
            have he : EvE Gen.prog s4
                (.lor
                  (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
                    (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 9)))
                  (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4)) (.var 9)) (.var 5)))
                (boolVal true) :=
              EvE.lor_false hlt1 truthy_false hlt2 truthy_true
            exact ExS.ite he truthy_true (ExS.ret (EvE.const _))
          refine ⟨s4, ?_, ?_, fun _ _ _ => rfl⟩
          · show ExS Gen.prog s0 Gen.ni_bmp_header_arith.body
                (.ret (some (.int ⟨32, true⟩ (bmpOutputArithCode width height bitCount channels pixelOffset size)))) s4
            rw [hSpec]
            exact ExS.seq hSkip1 (ExS.seq hSet7 (ExS.seq hSkip2
              (ExS.seq hSet8a (ExS.seq hSkip3
                (ExS.seq hSet8b (ExS.seq hSkip4
                  (ExS.seq hSet9 (ExS.seq_ret hRet9))))))))
          · intro habs
            rw [hSpec] at habs
            exact absurd habs (by decide)
        · -- no truncation: stores succeed
          have hTruncFalse : ¬ (pixelOffset > 18446744073709551615 - (bmpRowStride width bitCount * height) ∨ pixelOffset + (bmpRowStride width bitCount * height) > size) :=
            fun h => h.elim hTruncA hTruncB
          have hSpec : bmpOutputArithCode width height bitCount channels pixelOffset size = 0 := by
            have hsMul1 := sizeMulOK_w_b_gen (show width ≤ 4294967295 by omega) (show bitCount ≤ 65535 by omega)
            have hsMul2 := sizeMulOK_w_c_gen (show width ≤ 4294967295 by omega) (show channels ≤ 255 by omega)
            have hsMul3 : sizeMulOK (width * channels) height = true := sizeMulOK_wc_h_gen hStage3
            have hsMul4 : sizeMulOK (bmpRowStride width bitCount) height = true := sizeMulOK_row_h_gen hStage4
            have hTruncFalse' : ¬ (pixelOffset > sizeMax - (bmpRowStride width bitCount * height) ∨ pixelOffset + (bmpRowStride width bitCount * height) > size) := hTruncFalse
            unfold bmpOutputArithCode
            simp [hsMul1, hsMul2, hsMul3, hsMul4, hTruncFalse']
          have hStoresSkip : ExS Gen.prog s4
              (.ite (.lor
                (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
                  (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 9)))
                (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4)) (.var 9)) (.var 5)))
                (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 9)))) .skip)
              .normal s4 := by
            have hscast : EvE Gen.prog s4 (.cast ⟨64, false⟩ (.var 4)) (.int ⟨64, false⟩ pixelOffset) :=
              EvE.cast (EvE.var hl4_4) (u32_u64_cast pixelOffset (by omega))
            have hscast9 : EvE Gen.prog s4 (.var 9) (.int ⟨64, false⟩ (bmpRowStride width bitCount * height)) := EvE.var hl9_4
            have hscast5 : EvE Gen.prog s4 (.var 5) (.int ⟨64, false⟩ size) := EvE.var hl5_4
            have hAddLt : pixelOffset + (bmpRowStride width bitCount * height) < 2 ^ 64 := by
              have h2 : (bmpRowStride width bitCount * height) ≤ 18446744073709551615 := hRows64
              have h1 : pixelOffset ≤ 4294967295 := by omega
              have h3 : pixelOffset ≤ 18446744073709551615 - (bmpRowStride width bitCount * height) := by omega
              omega
            have hsub : EvE Gen.prog s4
                (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 9))
                (.int ⟨64, false⟩ (18446744073709551615 - (bmpRowStride width bitCount * height))) := by
              have he : evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ 18446744073709551615) (.int ⟨64, false⟩ (bmpRowStride width bitCount * height)) =
                  .ok (.int ⟨64, false⟩ (18446744073709551615 - (bmpRowStride width bitCount * height))) :=
                NANO.C.bin_u64_sub 18446744073709551615 (bmpRowStride width bitCount * height) (by omega)
              exact EvE.bin (EvE.const _) hscast9 he
            have hlt1 : EvE Gen.prog s4
                (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
                  (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 9)))
                (boolVal false) := by
              have eCmp : EvE Gen.prog s4
                  (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
                    (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 9)))
                  (boolVal (decide (pixelOffset > 18446744073709551615 - (bmpRowStride width bitCount * height)))) :=
                EvE.bin hscast hsub (bin_u64_gt _ _)
              rwa [decide_eq_false_iff_not.mpr (by omega)] at eCmp
            have eAdd : EvE Gen.prog s4
                (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4)) (.var 9))
                (.int ⟨64, false⟩ (pixelOffset + (bmpRowStride width bitCount * height))) :=
              EvE.bin hscast hscast9 (bin_u64_add pixelOffset (bmpRowStride width bitCount * height) hAddLt)
            have hlt2 : EvE Gen.prog s4
                (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4)) (.var 9)) (.var 5))
                (boolVal false) := by
              have eCmp : EvE Gen.prog s4
                  (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4)) (.var 9)) (.var 5))
                  (boolVal (decide (pixelOffset + (bmpRowStride width bitCount * height) > size))) :=
                EvE.bin eAdd hscast5 (bin_u64_gt _ _)
              rwa [decide_eq_false_iff_not.mpr (by omega)] at eCmp
            have he : EvE Gen.prog s4
                (.lor
                  (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4))
                    (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 9)))
                  (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 4)) (.var 9)) (.var 5)))
                (boolVal false) :=
              EvE.lor_false hlt1 truthy_false hlt2 truthy_false
            exact ExS.ite he truthy_false ExS.skip
          obtain ⟨s5, hStores, hblk, hUnt⟩ := bmp_arith_stores_exs s4.mem obl hob h48 ro hro s4.locals hl6_4
            (bmpRowStride width bitCount) (width * channels * height)
            (by omega) (by omega) hl7_4 hl8_4
          refine ⟨s5, ?_, ?_, fun _ j hj => hUnt j hj⟩
          · show ExS Gen.prog s0 Gen.ni_bmp_header_arith.body
                (.ret (some (.int ⟨32, true⟩ (bmpOutputArithCode width height bitCount channels pixelOffset size)))) s5
            rw [hSpec]
            exact ExS.seq hSkip1 (ExS.seq hSet7 (ExS.seq hSkip2
              (ExS.seq hSet8a (ExS.seq hSkip3
                (ExS.seq hSet8b (ExS.seq hSkip4
                  (ExS.seq hSet9 (ExS.seq hStoresSkip hStores))))))))
          · intro _
            exact hblk
    · -- stage 4 fails: ret 9
      have hBad4 : ¬ (bmpRowStride width bitCount = 0 ∨ height ≤ 18446744073709551615 / bmpRowStride width bitCount) := hStage4
      obtain ⟨sMF4, exMF4⟩ := ni_bmp_mul_fits_exs s3.mem (bmpRowStride width bitCount) height hRowStride64 hH64 true
      have hCall4 : EvE Gen.prog s3
          (.call 11 [(.var 7), (.cast ⟨64, false⟩ (.var 1))])
          (.int ⟨32, true⟩ 0) := by
        have hex : EvE Gen.prog s3
            (.call 11 [(.var 7), (.cast ⟨64, false⟩ (.var 1))])
            (.int ⟨32, true⟩ (if bmpRowStride width bitCount = 0 ∨
              height ≤ 18446744073709551615 / bmpRowStride width bitCount then 1 else 0)) :=
          EvE.call (EvArgs.cons v7_3 (EvArgs.cons vc1_3 EvArgs.nil))
            (show Gen.prog 11 = some Gen.ni_bmp_mul_fits from rfl)
            (show Gen.ni_bmp_mul_fits.params.length = 2 from rfl)
            exMF4
        rwa [if_neg hBad4] at hex
      have hNot4 : EvE Gen.prog s3
          (.un .lnot ⟨32, true⟩ (.call 11 [(.var 7), (.cast ⟨64, false⟩ (.var 1))]))
          (boolVal true) := by
        have he : evalUn .lnot ⟨32, true⟩ (.int ⟨32, true⟩ 0) = .ok (boolVal true) := by
          simp [evalUn, truthy]
        exact EvE.un hCall4 he
      have hSpec : bmpOutputArithCode width height bitCount channels pixelOffset size = 9 := by
        have hsMul1 := sizeMulOK_w_b_gen (show width ≤ 4294967295 by omega) (show bitCount ≤ 65535 by omega)
        have hsMul2 := sizeMulOK_w_c_gen (show width ≤ 4294967295 by omega) (show channels ≤ 255 by omega)
        have hsMul3 : sizeMulOK (width * channels) height = true := sizeMulOK_wc_h_gen hStage3
        have hsMul4 : sizeMulOK (bmpRowStride width bitCount) height = false :=
          sizeMulOK_row_h_false_gen (Nat.pos_iff_ne_zero.mpr (fun h0 => hBad4 (Or.inl h0)))
            (fun h => hBad4 (Or.inr h))
        unfold bmpOutputArithCode
        simp [hsMul1, hsMul2, hsMul3, hsMul4]
      have hRet9 : ExS Gen.prog s3
          (.ite (.un .lnot ⟨32, true⟩ (.call 11 [(.var 7), (.cast ⟨64, false⟩ (.var 1))]))
            (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 9)))) .skip)
          (Outcome.ret (some (.int ⟨32, true⟩ 9))) s3 :=
        ExS.ite hNot4 truthy_true (ExS.ret (EvE.const _))
      refine ⟨s3, ?_, ?_, fun _ _ _ => rfl⟩
      · show ExS Gen.prog s0 Gen.ni_bmp_header_arith.body
            (.ret (some (.int ⟨32, true⟩ (bmpOutputArithCode width height bitCount channels pixelOffset size)))) s3
        rw [hSpec]
        exact ExS.seq hSkip1 (ExS.seq hSet7 (ExS.seq hSkip2
          (ExS.seq hSet8a (ExS.seq hSkip3
            (ExS.seq hSet8b (ExS.seq_ret hRet9))))))
      · intro habs
        rw [hSpec] at habs
        exact absurd habs (by decide)
  · -- stage 3 fails: ret 8
    have hBad3 : ¬ (width * channels = 0 ∨ height ≤ 18446744073709551615 / (width * channels)) := hStage3
    have hWCne0 : width * channels ≠ 0 := by
      intro h0; exact hBad3 (Or.inl h0)
    have hWCpos : 0 < width * channels := Nat.pos_iff_ne_zero.mpr hWCne0
    obtain ⟨sMF3, exMF3⟩ := ni_bmp_mul_fits_exs s2.mem (width * channels) height hWClt2 hH64 true
    have hCall3 : EvE Gen.prog s2
        (.call 11 [(.var 8), (.cast ⟨64, false⟩ (.var 1))])
        (.int ⟨32, true⟩ 0) := by
      have hex : EvE Gen.prog s2
          (.call 11 [(.var 8), (.cast ⟨64, false⟩ (.var 1))])
          (.int ⟨32, true⟩ (if width * channels = 0 ∨ height ≤ 18446744073709551615 / (width * channels) then 1 else 0)) :=
        EvE.call (EvArgs.cons v8_2 (EvArgs.cons vc1_2 EvArgs.nil))
          (show Gen.prog 11 = some Gen.ni_bmp_mul_fits from rfl)
          (show Gen.ni_bmp_mul_fits.params.length = 2 from rfl)
          exMF3
      rwa [if_neg hBad3] at hex
    have hNot3 : EvE Gen.prog s2
        (.un .lnot ⟨32, true⟩ (.call 11 [(.var 8), (.cast ⟨64, false⟩ (.var 1))]))
        (boolVal true) := by
      have he : evalUn .lnot ⟨32, true⟩ (.int ⟨32, true⟩ 0) = .ok (boolVal true) := by
        simp [evalUn, truthy]
      exact EvE.un hCall3 he
    have hSpec : bmpOutputArithCode width height bitCount channels pixelOffset size = 8 := by
      have hsMul1 := sizeMulOK_w_b_gen (show width ≤ 4294967295 by omega) (show bitCount ≤ 65535 by omega)
      have hsMul2 := sizeMulOK_w_c_gen (show width ≤ 4294967295 by omega) (show channels ≤ 255 by omega)
      have hsMul3 : sizeMulOK (width * channels) height = false :=
        sizeMulOK_wc_h_false_gen (Nat.pos_iff_ne_zero.mpr hWCne0)
          (fun h => hBad3 (Or.inr h))
      unfold bmpOutputArithCode
      simp [hsMul1, hsMul2, hsMul3]
    have hRet8 : ExS Gen.prog s2
        (.ite (.un .lnot ⟨32, true⟩ (.call 11 [(.var 8), (.cast ⟨64, false⟩ (.var 1))]))
          (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 8)))) .skip)
        (Outcome.ret (some (.int ⟨32, true⟩ 8))) s2 :=
      ExS.ite hNot3 truthy_true (ExS.ret (EvE.const _))
    refine ⟨s2, ?_, ?_, fun _ _ _ => rfl⟩
    · show ExS Gen.prog s0 Gen.ni_bmp_header_arith.body
          (.ret (some (.int ⟨32, true⟩ (bmpOutputArithCode width height bitCount channels pixelOffset size)))) s2
      rw [hSpec]
      exact ExS.seq hSkip1 (ExS.seq hSet7 (ExS.seq hSkip2
        (ExS.seq hSet8a (ExS.seq_ret hRet8))))
    · intro habs
      rw [hSpec] at habs
      exact absurd habs (by decide)

end NANO.C.Proofs
