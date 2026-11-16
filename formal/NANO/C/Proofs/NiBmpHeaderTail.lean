/-
  Development scratch for the arithmetical tail of `ni_bmp_header`:
  casts, multiplication, .set 11/12/15, mul_fits calls, and the truncated
  check. Proves structure independently; will be moved to the final file.
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

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 400000

namespace NANO.C.Proofs
open NANO NANO.C

theorem const_u64_proof {s : State} (ro : Bool) :
    EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 31)))
      (.int ⟨64, false⟩ 31) := by
  have he : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ 31) = Res.ok (.int ⟨64, false⟩ 31) := by
    rw [u32_u64_cast 31 (by decide)]
  exact EvE.cast (EvE.const _) he

theorem cast_n_proof {s : State} (n : Nat) {v : Nat} (hl : s.locals n = some (Val.int ⟨32, false⟩ v))
    (hv : v < 2 ^ 32) :
    EvE Gen.prog s (.cast ⟨64, false⟩ (.var n)) (.int ⟨64, false⟩ v) := by
  have he : evalCast ⟨64, false⟩ (Val.int ⟨32, false⟩ v) = Res.ok (Val.int ⟨64, false⟩ v) := by
    rw [u32_u64_cast v hv]
  exact EvE.cast (EvE.var hl) he

theorem cast_seven_proof {s : State} {W : Nat} (hl7 : s.locals 7 = some (Val.int ⟨32, false⟩ W))
    (hW64 : W < 2 ^ 32) :
    EvE Gen.prog s (.cast ⟨64, false⟩ (.var 7)) (.int ⟨64, false⟩ W) :=
  cast_n_proof 7 hl7 hW64

theorem cast_four_proof_n {s : State} {v : Nat} (hl4 : s.locals 4 = some (Val.int ⟨32, false⟩ v))
    (h : v < 2 ^ 32) :
    EvE Gen.prog s (.cast ⟨64, false⟩ (.var 4)) (.int ⟨64, false⟩ v) :=
  cast_n_proof 4 hl4 h

theorem cast_three_proof_n {s : State} {v : Nat} (hl3 : s.locals 3 = some (Val.int ⟨32, false⟩ v))
    (h : v < 2 ^ 32) :
    EvE Gen.prog s (.cast ⟨64, false⟩ (.var 3)) (.int ⟨64, false⟩ v) :=
  cast_n_proof 3 hl3 h

theorem cast_five_proof {s : State} {b : Nat} (hl5 : s.locals 5 = some (Val.int ⟨16, false⟩ b))
    (hB64 : b < 65536) :
    EvE Gen.prog s (.cast ⟨64, false⟩ (.var 5)) (.int ⟨64, false⟩ b) := by
  have he : evalCast ⟨64, false⟩ (Val.int ⟨16, false⟩ b) = Res.ok (Val.int ⟨64, false⟩ b) := by
    rw [u16_u64_cast b hB64]
  exact EvE.cast (EvE.var hl5) he

theorem cast_nine_proof {s : State} {c : Nat} (hl9 : s.locals 9 = some (Val.int ⟨8, false⟩ c))
    (hc : c < 256) :
    EvE Gen.prog s (.cast ⟨64, false⟩ (.var 9)) (.int ⟨64, false⟩ c) := by
  have he : evalCast ⟨64, false⟩ (Val.int ⟨8, false⟩ c) = Res.ok (Val.int ⟨64, false⟩ c) := by
    simp [evalCast, IntTy.modulus, IntTy.wrap, Int.ofNat_lt, show (c : Nat) < 18446744073709551616 from by omega]
  exact EvE.cast (EvE.var hl9) he

theorem cast_four_proof {s : State} {v : Nat} (hl4 : s.locals 4 = some (Val.int ⟨32, false⟩ v))
    (h : v < 2 ^ 32) :
    EvE Gen.prog s (.cast ⟨64, false⟩ (.var 4)) (.int ⟨64, false⟩ v) := by
  have he : evalCast ⟨64, false⟩ (Val.int ⟨32, false⟩ v) = Res.ok (Val.int ⟨64, false⟩ v) := by
    rw [u32_u64_cast v h]
  exact EvE.cast (EvE.var hl4) he

theorem cast_three_proof {s : State} {v : Nat} (hl3 : s.locals 3 = some (Val.int ⟨32, false⟩ v))
    (h : v < 2 ^ 32) :
    EvE Gen.prog s (.cast ⟨64, false⟩ (.var 3)) (.int ⟨64, false⟩ v) := by
  have he : evalCast ⟨64, false⟩ (Val.int ⟨32, false⟩ v) = Res.ok (Val.int ⟨64, false⟩ v) := by
    rw [u32_u64_cast v h]
  exact EvE.cast (EvE.var hl3) he

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem cast_thirty_one {s : State} :
    EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 31)))
      (.int ⟨64, false⟩ 31) := by
  have he : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ 31) = Res.ok (.int ⟨64, false⟩ 31) :=
    u32_u64_cast 31 (by omega)
  exact EvE.cast (EvE.const _) he

theorem cast_five_const {s : State} :
    EvE Gen.prog s (.const (.int ⟨32, false⟩ 5)) (.int ⟨32, false⟩ 5) := EvE.const _

theorem cast_two_const {s : State} :
    EvE Gen.prog s (.const (.int ⟨32, false⟩ 2)) (.int ⟨32, false⟩ 2) := EvE.const _

theorem bin_mul_casts {s : State} {W b : Nat} (hW : W ≤ 2147483647) (hb : b ≤ 65535)
    (hl7 : s.locals 7 = some (Val.int ⟨32, false⟩ W)) (hl5 : s.locals 5 = some (Val.int ⟨16, false⟩ b))
    (hW32 : W < 4294967296) (hb65536 : b < 65536) :
    EvE Gen.prog s (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 7)) (.cast ⟨64, false⟩ (.var 5)))
      (.int ⟨64, false⟩ (W * b)) := by
  have h1 : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 7)) (.int ⟨64, false⟩ W) :=
    cast_seven_proof hl7 hW32
  have h2 : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 5)) (.int ⟨64, false⟩ b) :=
    cast_five_proof hl5 hb65536
  have h3 : W * b < 2 ^ 64 := by
    have hWB : W * b ≤ 2147483647 * 65535 := Nat.mul_le_mul hW hb
    omega
  exact EvE.bin h1 h2 (bin_u64_mul W b h3)

theorem bin_add_const31 {s : State} {W b : Nat} (hW : W ≤ 2147483647) (hb : b ≤ 65535) {m : Mem}
    (hl7 : s.locals 7 = some (Val.int ⟨32, false⟩ W)) (hl5 : s.locals 5 = some (Val.int ⟨16, false⟩ b))
    (hW32 : W < 4294967296) :
    EvE Gen.prog s
      (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 7)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 31))))
      (.int ⟨64, false⟩ (W + 31)) := by
  have h1 : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 7)) (.int ⟨64, false⟩ W) :=
    cast_seven_proof hl7 hW32
  have h2 : EvE Gen.prog s (.const (.int ⟨32, false⟩ 31)) (.int ⟨32, false⟩ 31) := EvE.const _
  have h3 : W + 31 < 2 ^ 64 := by
    have hWB : W ≤ 2147483647 := hW
    omega
  exact EvE.bin h1 (EvE.cast h2 (u32_u64_cast 31 (by omega))) (bin_u64_add W 31 h3)

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- Row stride expression, as a Nat: `((W*b+31)/32)*4`. -/
def rowStride (W b : Nat) : Nat := ((W * b + 31) / 32) * 4

theorem eval_row_stride {s : State} {W b : Nat} (hW : W ≤ 2147483647) (hb : b ≤ 65535)
    (hl7 : s.locals 7 = some (Val.int ⟨32, false⟩ W)) (hl5 : s.locals 5 = some (Val.int ⟨16, false⟩ b)) :
    EvE Gen.prog s
      (.bin .shl (some ⟨64, false⟩)
        (.bin .shr (some ⟨64, false⟩)
          (.bin .add (some ⟨64, false⟩)
            (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 7)) (.cast ⟨64, false⟩ (.var 5)))
            (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 31))))
          (.const (.int ⟨32, false⟩ 5)))
        (.const (.int ⟨32, false⟩ 2)))
      (.int ⟨64, false⟩ (rowStride W b)) := by
  have hWB : W * b ≤ 2147483647 * 65535 := Nat.mul_le_mul (by omega) hb
  have hWB2 : W * b + 31 < 2 ^ 64 := by omega
  have h1 : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 7)) (.int ⟨64, false⟩ W) :=
    cast_seven_proof hl7 (by omega)
  have h2 : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 5)) (.int ⟨64, false⟩ b) :=
    cast_five_proof hl5 (by omega)
  have h3 : W * b < 2 ^ 64 := by omega
  have hMul : EvE Gen.prog s (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 7)) (.cast ⟨64, false⟩ (.var 5)))
      (.int ⟨64, false⟩ (W * b)) :=
    EvE.bin h1 h2 (bin_u64_mul W b h3)
  have hcast31 : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 31))) (.int ⟨64, false⟩ 31) :=
    cast_thirty_one
  have hAdd : EvE Gen.prog s
      (.bin .add (some ⟨64, false⟩) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 7)) (.cast ⟨64, false⟩ (.var 5)))
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 31))))
      (.int ⟨64, false⟩ (W * b + 31)) :=
    EvE.bin hMul hcast31 (bin_u64_add (W * b) 31 hWB2)
  have hShr : EvE Gen.prog s
      (.bin .shr (some ⟨64, false⟩)
        (.bin .add (some ⟨64, false⟩) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 7)) (.cast ⟨64, false⟩ (.var 5)))
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 31))))
        (.const (.int ⟨32, false⟩ 5)))
      (.int ⟨64, false⟩ ((W * b + 31) / 2 ^ 5)) :=
    EvE.bin hAdd (EvE.const _) (bin_u64_shr_5_c32 (W * b + 31))
  have hShr2 : EvE Gen.prog s
      (.bin .shl (some ⟨64, false⟩)
        (.bin .shr (some ⟨64, false⟩)
          (.bin .add (some ⟨64, false⟩) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 7)) (.cast ⟨64, false⟩ (.var 5)))
            (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 31))))
          (.const (.int ⟨32, false⟩ 5)))
        (.const (.int ⟨32, false⟩ 2)))
      (.int ⟨64, false⟩ (((W * b + 31) / 2 ^ 5) * 4)) :=
    EvE.bin hShr (EvE.const _) (bin_u64_shl_2_c32 ((W * b + 31) / 2 ^ 5) (by omega))
  have eqn : ((W * b + 31) / 2 ^ 5) * 4 = ((W * b + 31) / 32) * 4 := by
    have e52 : (2 : Nat) ^ 5 = 32 := by decide
    rw [e52]
  rw [eqn] at hShr2
  have eqn2 : ((W * b + 31) / 32) * 4 = rowStride W b := rfl
  rw [eqn2] at hShr2
  exact hShr2

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem fits2_proof {W c : Nat} (hW : W ≤ 2147483647) (hc : c ≤ 4) (hW1 : 1 ≤ W) :
    (W = 0 ∨ c ≤ 18446744073709551615 / W) := by
  right
  rw [Nat.le_div_iff_mul_le (by omega)]
  have hwc : c * W ≤ 4 * 2147483647 := Nat.mul_le_mul hc hW
  omega

theorem fits3_proof {W c h : Nat} (hW : W ≤ 2147483647) (hc : c ≤ 4) (hh : h ≤ 2147483647)
    (h_wc : W * c > 0) :
    (W * c = 0 ∨ h ≤ 18446744073709551615 / (W * c)) := by
  right
  rw [Nat.le_div_iff_mul_le (by omega)]
  have hwc : W * c ≤ 8589934588 := by
    have := Nat.mul_le_mul hW hc
    have hwc2 : W * c ≤ 2147483647 * 4 := this
    omega
  have hOSH : (W * c) * h ≤ 8589934588 * 2147483647 := Nat.mul_le_mul hwc hh
  have hLit : 8589934588 * 2147483647 = 18446744056529682436 := by decide
  rw [Nat.mul_comm, hLit] at hOSH
  omega

theorem fits4_proof {rowStride h : Nat} (hr : rowStride ≤ 8589934592) (hh : h ≤ 2147483647) :
    (rowStride = 0 ∨ h ≤ 18446744073709551615 / rowStride) := by
  by_cases h0 : rowStride = 0
  · exact Or.inl h0
  · right
    rw [Nat.le_div_iff_mul_le (by omega)]
    have he : rowStride * h ≤ 8589934592 * 2147483647 := Nat.mul_le_mul hr hh
    have hLit : 8589934592 * 2147483647 = 18446744065119617024 := by decide
    rw [Nat.mul_comm, hLit] at he
    omega

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem fits_bin_u64_add {W b : Nat} (h : W + b < 2 ^ 64) :
    evalBin .add (some ⟨64, false⟩) (.int ⟨64, false⟩ W) (.int ⟨64, false⟩ b)
      = .ok (.int ⟨64, false⟩ (W + b)) :=
  bin_u64_add W b h

theorem hMulFits2 {s : State} {W c : Nat} (hW : W ≤ 2147483647) (hc : c ≤ 4)
    (hW1 : 1 ≤ W) (hc65 : c < 256)
    (hW64 : W < 2 ^ 64) (hc64 : c < 2 ^ 64)
    (hl7 : s.locals 7 = some (Val.int ⟨32, false⟩ W))
    (hl9 : s.locals 9 = some (Val.int ⟨8, false⟩ c)) :
    EvE Gen.prog s
      (.call 11 [(.cast ⟨64, false⟩ (.var 7)), (.cast ⟨64, false⟩ (.var 9))])
      (.int ⟨32, true⟩ 1) := by
  have wcast : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 7)) (.int ⟨64, false⟩ W) :=
    cast_seven_proof hl7 (by omega)
  have ccast : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 9)) (.int ⟨64, false⟩ c) :=
    cast_nine_proof hl9 hc65
  obtain ⟨sMF, exMF⟩ := ni_bmp_mul_fits_exs s.mem W c hW64 hc64 true
  have exCall : EvE Gen.prog s
      (.call 11 [(.cast ⟨64, false⟩ (.var 7)), (.cast ⟨64, false⟩ (.var 9))])
      (.int ⟨32, true⟩ (if W = 0 ∨ c ≤ 18446744073709551615 / W then 1 else 0)) :=
    EvE.call (EvArgs.cons wcast (EvArgs.cons ccast EvArgs.nil))
      (show Gen.prog 11 = some Gen.ni_bmp_mul_fits from rfl)
      (show Gen.ni_bmp_mul_fits.params.length = 2 from rfl)
      exMF
  have hfits : W = 0 ∨ c ≤ 18446744073709551615 / W :=
    fits2_proof hW hc hW1
  rw [if_pos hfits] at exCall
  exact exCall

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem mulfits2_ite_skip {s : State} {W c : Nat} (hW : W ≤ 2147483647) (hc : c ≤ 4)
    (hW1 : 1 ≤ W) (hc65 : c < 256)
    (hW64 : W < 2 ^ 64) (hc64 : c < 2 ^ 64)
    (hl7 : s.locals 7 = some (Val.int ⟨32, false⟩ W))
    (hl9 : s.locals 9 = some (Val.int ⟨8, false⟩ c)) :
    ExS Gen.prog s
      (.ite (.un .lnot ⟨32, true⟩ (.call 11 [(.cast ⟨64, false⟩ (.var 7)), (.cast ⟨64, false⟩ (.var 9))]))
        (.ret (some (.const (.int ⟨32, true⟩ 8)))) .skip)
      .normal s := by
  have hfitscall : EvE Gen.prog s
      (.call 11 [(.cast ⟨64, false⟩ (.var 7)), (.cast ⟨64, false⟩ (.var 9))])
      (.int ⟨32, true⟩ 1) :=
    hMulFits2 hW hc hW1 hc65 hW64 hc64 hl7 hl9
  have he : evalUn .lnot ⟨32, true⟩ (.int ⟨32, true⟩ 1) = .ok (boolVal false) := by
    simp [evalUn, truthy]
  have hfalse : EvE Gen.prog s
      (.un .lnot ⟨32, true⟩ (.call 11 [(.cast ⟨64, false⟩ (.var 7)), (.cast ⟨64, false⟩ (.var 9))]))
      (boolVal false) :=
    EvE.un hfitscall he
  exact ExS.ite hfalse (truthy_boolVal false) ExS.skip

theorem set_twelve_mul {s : State} {W c : Nat} (hW : W ≤ 2147483647) (hc : c ≤ 4)
    (hW64 : W < 2 ^ 64) (hc64 : c < 2 ^ 64)
    (hl7 : s.locals 7 = some (Val.int ⟨32, false⟩ W))
    (hl9 : s.locals 9 = some (Val.int ⟨8, false⟩ c)) :
    ExS Gen.prog s
      (.set 12 (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 7)) (.cast ⟨64, false⟩ (.var 9))))
      .normal { s with locals := s.locals.upd 12 (.int ⟨64, false⟩ (W * c)) } := by
  have wcast : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 7)) (.int ⟨64, false⟩ W) :=
    cast_seven_proof hl7 (by omega)
  have ccast : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 9)) (.int ⟨64, false⟩ c) :=
    cast_nine_proof hl9 (by omega)
  have h3 : W * c < 2 ^ 64 := by
    have hwc : W * c ≤ 2147483647 * 4 := Nat.mul_le_mul hW hc
    omega
  have hmul : EvE Gen.prog s
      (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 7)) (.cast ⟨64, false⟩ (.var 9)))
      (.int ⟨64, false⟩ (W * c)) :=
    EvE.bin wcast ccast (bin_u64_mul W c h3)
  exact ExS.set hmul

theorem hMulFits3 {s : State} {W c h : Nat} (hW : W ≤ 2147483647) (hc : c ≤ 4) (hh : h ≤ 2147483647)
    (hWo : W * c > 0)
    (hW64 : W < 2 ^ 64) (hc64 : c < 2 ^ 64) (hh64 : h < 2 ^ 64) (hOS64 : (W * c) < 2 ^ 64)
    (hl12 : s.locals 12 = some (.int ⟨64, false⟩ (W * c)))
    (hl8 : s.locals 8 = some (Val.int ⟨32, false⟩ h)) :
    EvE Gen.prog s
      (.call 11 [(.var 12), (.cast ⟨64, false⟩ (.var 8))])
      (.int ⟨32, true⟩ 1) := by
  have hcast : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 8)) (.int ⟨64, false⟩ h) :=
    cast_n_proof 8 hl8 (by omega)
  have wcast : EvE Gen.prog s (.var 12) (.int ⟨64, false⟩ (W * c)) := EvE.var hl12
  obtain ⟨sMF, exMF⟩ := ni_bmp_mul_fits_exs s.mem (W * c) h hOS64 hh64 true
  have exCall : EvE Gen.prog s
      (.call 11 [(.var 12), (.cast ⟨64, false⟩ (.var 8))])
      (.int ⟨32, true⟩ (if W * c = 0 ∨ h ≤ 18446744073709551615 / (W * c) then 1 else 0)) :=
    EvE.call (EvArgs.cons wcast (EvArgs.cons hcast EvArgs.nil))
      (show Gen.prog 11 = some Gen.ni_bmp_mul_fits from rfl)
      (show Gen.ni_bmp_mul_fits.params.length = 2 from rfl)
      exMF
  have hwc : W * c ≤ 8589934588 := by
    have := Nat.mul_le_mul hW hc
    omega
  have hfits : W * c = 0 ∨ h ≤ 18446744073709551615 / (W * c) :=
    fits3_proof hW hc hh hWo
  rw [if_pos hfits] at exCall
  exact exCall

theorem mulfits3_ite_skip {s : State} {W c h : Nat} (hW : W ≤ 2147483647) (hc : c ≤ 4) (hh : h ≤ 2147483647)
    (hWo : W * c > 0)
    (hW64 : W < 2 ^ 64) (hc64 : c < 2 ^ 64) (hh64 : h < 2 ^ 64) (hOS64 : W * c < 2 ^ 64)
    (hl12 : s.locals 12 = some (.int ⟨64, false⟩ (W * c)))
    (hl8 : s.locals 8 = some (Val.int ⟨32, false⟩ h)) :
    ExS Gen.prog s
      (.ite (.un .lnot ⟨32, true⟩ (.call 11 [(.var 12), (.cast ⟨64, false⟩ (.var 8))]))
        (.ret (some (.const (.int ⟨32, true⟩ 8)))) .skip)
      .normal s := by
  have hfitscall : EvE Gen.prog s
      (.call 11 [(.var 12), (.cast ⟨64, false⟩ (.var 8))])
      (.int ⟨32, true⟩ 1) :=
    hMulFits3 hW hc hh hWo hW64 hc64 hh64 hOS64 hl12 hl8
  have he : evalUn .lnot ⟨32, true⟩ (.int ⟨32, true⟩ 1) = .ok (boolVal false) := by
    simp [evalUn, truthy]
  have hfalse : EvE Gen.prog s
      (.un .lnot ⟨32, true⟩ (.call 11 [(.var 12), (.cast ⟨64, false⟩ (.var 8))]))
      (boolVal false) :=
    EvE.un hfitscall he
  exact ExS.ite hfalse (truthy_boolVal false) ExS.skip

theorem set_twelve_mul2 {s : State} {W c h : Nat} (hW : W ≤ 2147483647) (hc : c ≤ 4) (hh : h ≤ 2147483647)
    (hWo : W * c > 0)
    (hW64 : W < 2 ^ 64) (hc64 : c < 2 ^ 64) (hh64 : h < 2 ^ 64) (hOS64 : W * c < 2 ^ 64) (hOSH64 : W * c * h < 2 ^ 64)
    (hl12 : s.locals 12 = some (.int ⟨64, false⟩ (W * c)))
    (hl8 : s.locals 8 = some (Val.int ⟨32, false⟩ h)) :
    ExS Gen.prog s
      (.set 12 (.bin .mul (some ⟨64, false⟩) (.var 12) (.cast ⟨64, false⟩ (.var 8))))
      .normal { s with locals := s.locals.upd 12 (.int ⟨64, false⟩ (W * c * h)) } := by
  have hcast : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 8)) (.int ⟨64, false⟩ h) :=
    cast_n_proof 8 hl8 (by omega)
  have wcast : EvE Gen.prog s (.var 12) (.int ⟨64, false⟩ (W * c)) := EvE.var hl12
  have hOS : W * c < 2 ^ 64 := hOS64
  have hmul : EvE Gen.prog s
      (.bin .mul (some ⟨64, false⟩) (.var 12) (.cast ⟨64, false⟩ (.var 8)))
      (.int ⟨64, false⟩ (W * c * h)) :=
    EvE.bin wcast hcast (bin_u64_mul (W * c) h hOSH64)
  exact ExS.set hmul

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem set_eleven_rowstride {s : State} {W b : Nat} (hW : W ≤ 2147483647) (hb : b ≤ 65535)
    (hb32 : b < 65536)
    (hl7 : s.locals 7 = some (Val.int ⟨32, false⟩ W)) (hl5 : s.locals 5 = some (Val.int ⟨16, false⟩ b)) :
    ExS Gen.prog s
      (.set 11 (.bin .shl (some ⟨64, false⟩)
        (.bin .shr (some ⟨64, false⟩)
          (.bin .add (some ⟨64, false⟩)
            (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 7)) (.cast ⟨64, false⟩ (.var 5)))
            (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 31))))
          (.const (.int ⟨32, false⟩ 5)))
        (.const (.int ⟨32, false⟩ 2))))
      .normal { s with locals := s.locals.upd 11 (.int ⟨64, false⟩ (rowStride W b)) } := by
  have hEv : EvE Gen.prog s
      (.bin .shl (some ⟨64, false⟩)
        (.bin .shr (some ⟨64, false⟩)
          (.bin .add (some ⟨64, false⟩)
            (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 7)) (.cast ⟨64, false⟩ (.var 5)))
            (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 31))))
          (.const (.int ⟨32, false⟩ 5)))
        (.const (.int ⟨32, false⟩ 2)))
      (.int ⟨64, false⟩ (rowStride W b)) :=
    eval_row_stride hW hb hl7 hl5
  exact ExS.set hEv

theorem cast_eight_for_var_eight {s : State} {h : Nat}
    (hl8 : s.locals 8 = some (Val.int ⟨32, false⟩ h)) (hh : h < 4294967296) :
    EvE Gen.prog s (.cast ⟨64, false⟩ (.var 8)) (.int ⟨64, false⟩ h) :=
  cast_n_proof 8 hl8 (by omega)

theorem hMulFits4 {s : State} {RB h : Nat} (RB4 : RB ≤ 8589934592) (hh : h ≤ 2147483647)
    (hRB : RB > 0) (hRB64 : RB < 2 ^ 64) (hh64 : h < 2 ^ 64)
    (hl11 : s.locals 11 = some (.int ⟨64, false⟩ RB))
    (hl8 : s.locals 8 = some (Val.int ⟨32, false⟩ h)) :
    EvE Gen.prog s
      (.call 11 [(.var 11), (.cast ⟨64, false⟩ (.var 8))])
      (.int ⟨32, true⟩ 1) := by
  have hcast : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 8)) (.int ⟨64, false⟩ h) :=
    cast_n_proof 8 hl8 (by omega)
  have RBcast : EvE Gen.prog s (.var 11) (.int ⟨64, false⟩ RB) := EvE.var hl11
  obtain ⟨sMF, exMF⟩ := ni_bmp_mul_fits_exs s.mem RB h hRB64 hh64 true
  have exCall : EvE Gen.prog s
      (.call 11 [(.var 11), (.cast ⟨64, false⟩ (.var 8))])
      (.int ⟨32, true⟩ (if RB = 0 ∨ h ≤ 18446744073709551615 / RB then 1 else 0)) :=
    EvE.call (EvArgs.cons RBcast (EvArgs.cons hcast EvArgs.nil))
      (show Gen.prog 11 = some Gen.ni_bmp_mul_fits from rfl)
      (show Gen.ni_bmp_mul_fits.params.length = 2 from rfl)
      exMF
  by_cases hRBeq0 : RB = 0
  · rw [if_pos (Or.inl hRBeq0)] at exCall
    exact exCall
  · have hf : RB = 0 ∨ h ≤ 18446744073709551615 / RB := fits4_proof RB4 hh
    rw [if_pos hf] at exCall
    exact exCall

theorem mulfits4_ite_skip {s : State} {RB h : Nat} (RB4 : RB ≤ 8589934592) (hh : h ≤ 2147483647)
    (hRB : RB > 0) (hRB64 : RB < 2 ^ 64) (hh64 : h < 2 ^ 64)
    (hl11 : s.locals 11 = some (.int ⟨64, false⟩ RB))
    (hl8 : s.locals 8 = some (Val.int ⟨32, false⟩ h)) :
    ExS Gen.prog s
      (.ite (.un .lnot ⟨32, true⟩ (.call 11 [(.var 11), (.cast ⟨64, false⟩ (.var 8))]))
        (.ret (some (.const (.int ⟨32, true⟩ 9)))) .skip)
      .normal s := by
  have hfitscall : EvE Gen.prog s
      (.call 11 [(.var 11), (.cast ⟨64, false⟩ (.var 8))])
      (.int ⟨32, true⟩ 1) :=
    hMulFits4 RB4 hh hRB hRB64 hh64 hl11 hl8
  have he : evalUn .lnot ⟨32, true⟩ (.int ⟨32, true⟩ 1) = .ok (boolVal false) := by
    simp [evalUn, truthy]
  have hfalse : EvE Gen.prog s
      (.un .lnot ⟨32, true⟩ (.call 11 [(.var 11), (.cast ⟨64, false⟩ (.var 8))]))
      (boolVal false) :=
    EvE.un hfitscall he
  exact ExS.ite hfalse (truthy_boolVal false) ExS.skip

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem sub_sizeMax_rowsBytes {rowsBytes : Nat} (h : rowsBytes ≤ 18446744073709551615) :
    18446744073709551615 - rowsBytes ≤ 18446744073709551615 :=
  Nat.sub_le _ _

theorem trunc_check_skip {s : State} {pixelOffset rowsBytes size : Nat}
    (hhLE1 : pixelOffset ≤ 18446744073709551615 - rowsBytes)  -- decide: .gt gives false
    (hhLE2 : pixelOffset + rowsBytes ≤ size)
    (hPo32 : pixelOffset < 4294967296)
    (hr64B : rowsBytes ≤ 18446744065119617024)
    (hl3 : s.locals 3 = some (Val.int ⟨32, false⟩ pixelOffset))
    (hl15 : s.locals 15 = some (.int ⟨64, false⟩ rowsBytes))
    (hl1 : s.locals 1 = some (.int ⟨64, false⟩ size)) :
    ExS Gen.prog s
      (.ite (.lor
        (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
          (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15)))
        (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3)) (.var 15)) (.var 1)))
        (.ret (some (.const (.int ⟨32, true⟩ 9)))) .skip)
      .normal s := by
  have hscast : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 3)) (.int ⟨64, false⟩ pixelOffset) :=
    cast_n_proof 3 hl3 (by omega)
  have hscast15 : EvE Gen.prog s (.var 15) (.int ⟨64, false⟩ rowsBytes) := EvE.var hl15
  have hcst1 : EvE Gen.prog s (.var 1) (.int ⟨64, false⟩ size) := EvE.var hl1
  have hsub : EvE Gen.prog s
      (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15))
      (.int ⟨64, false⟩ (18446744073709551615 - rowsBytes)) := by
    have he : evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ 18446744073709551615) (.int ⟨64, false⟩ rowsBytes) =
        .ok (.int ⟨64, false⟩ (18446744073709551615 - rowsBytes)) :=
      NANO.C.bin_u64_sub 18446744073709551615 rowsBytes (by omega)
    exact EvE.bin (EvE.const _) hscast15 he
  have hlt1 : EvE Gen.prog s
      (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
        (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15)))
      (boolVal false) := by
    have eCmp : EvE Gen.prog s
        (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
          (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15)))
        (boolVal (decide (pixelOffset > 18446744073709551615 - rowsBytes))) :=
      EvE.bin hscast hsub (bin_u64_gt _ _)
    rwa [decide_eq_false_iff_not.mpr (by omega)] at eCmp
  have hscast1 : EvE Gen.prog s (.var 1) (.int ⟨64, false⟩ size) := EvE.var hl1
  have eAdd : EvE Gen.prog s
      (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3)) (.var 15))
      (.int ⟨64, false⟩ (pixelOffset + rowsBytes)) := by
    exact EvE.bin hscast hscast15 (bin_u64_add pixelOffset rowsBytes (by omega))

  have hlt2 : EvE Gen.prog s
      (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3)) (.var 15)) (.var 1))
      (boolVal false) := by
    have eCmp : EvE Gen.prog s
        (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3)) (.var 15)) (.var 1))
        (boolVal (decide (pixelOffset + rowsBytes > size))) :=
      EvE.bin eAdd hscast1 (bin_u64_gt _ _)
    rwa [decide_eq_false_iff_not.mpr (by omega)] at eCmp
  have he : EvE Gen.prog s
      (.lor
        (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
          (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15)))
        (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3)) (.var 15)) (.var 1)))
      (boolVal false) := by
    exact EvE.lor_false hlt1 (truthy_boolVal false) hlt2 (truthy_boolVal false)
  exact ExS.ite he (truthy_boolVal false) ExS.skip

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem trunc_check_fire_condA {s : State} {pixelOffset rowsBytes size : Nat}
    (hBad : pixelOffset > 18446744073709551615 - rowsBytes)
    (hPo32 : pixelOffset < 4294967296)
    (hr64B : rowsBytes ≤ 18446744065119617024)
    (hl3 : s.locals 3 = some (Val.int ⟨32, false⟩ pixelOffset))
    (hl15 : s.locals 15 = some (.int ⟨64, false⟩ rowsBytes))
    (hl1 : s.locals 1 = some (.int ⟨64, false⟩ size)) :
    ExS Gen.prog s
      (.ite (.lor
        (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
          (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15)))
        (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3)) (.var 15)) (.var 1)))
        (.ret (some (.const (.int ⟨32, true⟩ 9)))) .skip)
      (Outcome.ret (some (.int ⟨32, true⟩ 9))) s := by
  have hscast : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 3)) (.int ⟨64, false⟩ pixelOffset) :=
    cast_n_proof 3 hl3 (by omega)
  have hscast15 : EvE Gen.prog s (.var 15) (.int ⟨64, false⟩ rowsBytes) := EvE.var hl15
  have hscast1 : EvE Gen.prog s (.var 1) (.int ⟨64, false⟩ size) := EvE.var hl1
  have heVal : rowsBytes < 2 ^ 64 := by
    have hMax : 18446744065119617024 < 18446744073709551616 := by decide
    omega
  have hsub : EvE Gen.prog s
      (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15))
      (.int ⟨64, false⟩ (18446744073709551615 - rowsBytes)) := by
    have he : evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ 18446744073709551615) (.int ⟨64, false⟩ rowsBytes) =
        .ok (.int ⟨64, false⟩ (18446744073709551615 - rowsBytes)) :=
      NANO.C.bin_u64_sub 18446744073709551615 rowsBytes (by omega)
    exact EvE.bin (EvE.const _) hscast15 he
  have hlt1 : EvE Gen.prog s
      (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
        (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15)))
      (boolVal true) := by
    have eCmp : EvE Gen.prog s
        (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
          (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15)))
        (boolVal (decide (pixelOffset > 18446744073709551615 - rowsBytes))) :=
      EvE.bin hscast hsub (bin_u64_gt _ _)
    rwa [decide_eq_true_eq.mpr hBad] at eCmp
  have he : EvE Gen.prog s
      (.lor
        (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
          (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15)))
        (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3)) (.var 15)) (.var 1)))
      (boolVal true) :=
    EvE.lor_true hlt1 (truthy_boolVal true)
  exact ExS.ite he (truthy_boolVal true) (ExS.ret (EvE.const _))

theorem trunc_check_fire_condB (hBad : pixelOffset + rowsBytes > size)
    (hPo32 : pixelOffset < 4294967296)
    (hr64B : rowsBytes ≤ 18446744065119617024)
    (hl3 : s.locals 3 = some (Val.int ⟨32, false⟩ pixelOffset))
    (hl15 : s.locals 15 = some (.int ⟨64, false⟩ rowsBytes))
    (hl1 : s.locals 1 = some (.int ⟨64, false⟩ size)) :
    ExS Gen.prog s
      (.ite (.lor
        (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
          (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15)))
        (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3)) (.var 15)) (.var 1)))
        (.ret (some (.const (.int ⟨32, true⟩ 9)))) .skip)
      (Outcome.ret (some (.int ⟨32, true⟩ 9))) s := by
  have hscast : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 3)) (.int ⟨64, false⟩ pixelOffset) :=
    cast_n_proof 3 hl3 (by omega)
  have hscast15 : EvE Gen.prog s (.var 15) (.int ⟨64, false⟩ rowsBytes) := EvE.var hl15
  have hscast1 : EvE Gen.prog s (.var 1) (.int ⟨64, false⟩ size) := EvE.var hl1
  have heAdd : pixelOffset + rowsBytes ≤ 18446744069414584319 := by
    omega
  have hAddLt : pixelOffset + rowsBytes < 2 ^ 64 := by omega
  have heVAL : rowsBytes < 2 ^ 64 := by omega
  by_cases hA : pixelOffset > 18446744073709551615 - rowsBytes
  · -- condition A fires; lor short-circuits to true here
    have subVal : evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ 18446744073709551615) (.int ⟨64, false⟩ rowsBytes) =
        .ok (.int ⟨64, false⟩ (18446744073709551615 - rowsBytes)) :=
      NANO.C.bin_u64_sub 18446744073709551615 rowsBytes (by omega)
    have hsub : EvE Gen.prog s
        (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15))
        (.int ⟨64, false⟩ (18446744073709551615 - rowsBytes)) :=
      EvE.bin (EvE.const _) hscast15 subVal
    have hlt1 : EvE Gen.prog s
        (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
          (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15)))
        (boolVal true) := by
      have eCmp : EvE Gen.prog s
          (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
            (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15)))
          (boolVal (decide (pixelOffset > 18446744073709551615 - rowsBytes))) :=
        EvE.bin hscast hsub (bin_u64_gt _ _)
      rwa [decide_eq_true_eq.mpr hA] at eCmp
    have he : EvE Gen.prog s
        (.lor
          (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
            (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15)))
          (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3)) (.var 15)) (.var 1)))
        (boolVal true) :=
      EvE.lor_true hlt1 (truthy_boolVal true)
    exact ExS.ite he (truthy_boolVal true) (ExS.ret (EvE.const _))
  · -- condition A false; condition B fires (hBad implies pixelOffset + rowsBytes > size)
    have subVal : evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ 18446744073709551615) (.int ⟨64, false⟩ rowsBytes) =
        .ok (.int ⟨64, false⟩ (18446744073709551615 - rowsBytes)) :=
      NANO.C.bin_u64_sub 18446744073709551615 rowsBytes (by omega)
    have hsub : EvE Gen.prog s
        (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15))
        (.int ⟨64, false⟩ (18446744073709551615 - rowsBytes)) :=
      EvE.bin (EvE.const _) hscast15 subVal
    have hlt1 : EvE Gen.prog s
        (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
          (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15)))
        (boolVal false) := by
      have eCmp : EvE Gen.prog s
          (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
            (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15)))
          (boolVal (decide (pixelOffset > 18446744073709551615 - rowsBytes))) :=
        EvE.bin hscast hsub (bin_u64_gt _ _)
      rwa [decide_eq_false_iff_not.mpr hA] at eCmp
    have eAdd : EvE Gen.prog s
        (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3)) (.var 15))
        (.int ⟨64, false⟩ (pixelOffset + rowsBytes)) :=
      EvE.bin hscast hscast15 (bin_u64_add pixelOffset rowsBytes hAddLt)
    have hlt2 : EvE Gen.prog s
        (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3)) (.var 15)) (.var 1))
        (boolVal true) := by
      have eCmp : EvE Gen.prog s
          (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3)) (.var 15)) (.var 1))
          (boolVal (decide (pixelOffset + rowsBytes > size))) :=
        EvE.bin eAdd hscast1 (bin_u64_gt _ _)
      rwa [decide_eq_true_eq.mpr hBad] at eCmp
    have he : EvE Gen.prog s
        (.lor
          (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3))
            (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 15)))
          (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 3)) (.var 15)) (.var 1)))
        (boolVal true) :=
      EvE.lor_false hlt1 (truthy_boolVal false) hlt2 (truthy_boolVal true)
    exact ExS.ite he (truthy_boolVal true) (ExS.ret (EvE.const _))

end NANO.C.Proofs


namespace NANO.C.Proofs
open NANO NANO.C

/-- The 10-store epilogue of `ni_bmp_header`: the `ni_bmp_info` fields are storeed
    into the caller-provided `%3`-pointed struct, then the function returns 0. -/
theorem ni_tail_stores {s : State} (obl0 : Block) (h48_0 : obl0.length = 48)
    (hMem : s.mem 3 = some obl0) (hl2 : s.locals 2 = some (.ptr 3 0))
    {rowStride outSize paletteOffset width height pixelOffset paletteEntries bitCount channels topDown : Nat}
    (hl3 : s.locals 3 = some (.int ⟨32, false⟩ pixelOffset))
    (hl5 : s.locals 5 = some (.int ⟨16, false⟩ bitCount))
    (hl7 : s.locals 7 = some (.int ⟨32, false⟩ width))
    (hl8 : s.locals 8 = some (.int ⟨32, false⟩ height))
    (hl9 : s.locals 9 = some (.int ⟨8, false⟩ channels))
    (hl10 : s.locals 10 = some (.int ⟨8, false⟩ topDown))
    (hl11 : s.locals 11 = some (.int ⟨64, false⟩ rowStride))
    (hl12 : s.locals 12 = some (.int ⟨64, false⟩ outSize))
    (hl13 : s.locals 13 = some (.int ⟨64, false⟩ paletteEntries))
    (hl14 : s.locals 14 = some (.int ⟨64, false⟩ paletteOffset))
    (hr64 : rowStride < 18446744073709551616) (hoSize : outSize < 18446744073709551616)
    (hpOffset : paletteOffset < 18446744073709551616) (hWidth : width < 4294967296) (hHeight : height < 4294967296)
    (hpSize : pixelOffset < 4294967296) (hEntries : paletteEntries < 4294967296) (hBc : bitCount < 65536) (hCh : channels < 256) (hTd : topDown < 256)
    (hro : s.ro = false) :
    ExS Gen.prog s
      (.seq (.store (.int ⟨64, false⟩) (.field (.var 2) 0) (.var 11)) (.seq (.store (.int ⟨64, false⟩) (.field (.var 2) 8) (.var 12)) (.seq (.store (.int ⟨64, false⟩) (.field (.var 2) 16) (.var 14)) (.seq (.store (.int ⟨32, false⟩) (.field (.var 2) 24) (.var 7)) (.seq (.store (.int ⟨32, false⟩) (.field (.var 2) 28) (.var 8)) (.seq (.store (.int ⟨32, false⟩) (.field (.var 2) 32) (.var 3)) (.seq (.store (.int ⟨32, false⟩) (.field (.var 2) 36) (.cast ⟨32, false⟩ (.var 13))) (.seq (.store (.int ⟨16, false⟩) (.field (.var 2) 40) (.var 5)) (.seq (.store (.int ⟨8, false⟩) (.field (.var 2) 42) (.var 9)) (.seq (.store (.int ⟨8, false⟩) (.field (.var 2) 43) (.var 10)) (.ret (some (.const (.int ⟨32, true⟩ 0))))))))))))))
      (Outcome.ret (some (.int ⟨32, true⟩ 0)))
      { s with mem := s.mem.upd 3 (niInfoBlock obl0 rowStride outSize paletteOffset width height pixelOffset paletteEntries bitCount channels topDown) } := by
  let b1 := obl0.take 0 ++ encodeLE 8 rowStride ++ obl0.drop 8
  let b2 := b1.take 8 ++ encodeLE 8 outSize ++ b1.drop 16
  let b3 := b2.take 16 ++ encodeLE 8 paletteOffset ++ b2.drop 24
  let b4 := b3.take 24 ++ encodeLE 4 width ++ b3.drop 28
  let b5 := b4.take 28 ++ encodeLE 4 height ++ b4.drop 32
  let b6 := b5.take 32 ++ encodeLE 4 pixelOffset ++ b5.drop 36
  let b7 := b6.take 36 ++ encodeLE 4 paletteEntries ++ b6.drop 40
  let b8 := b7.take 40 ++ encodeLE 2 bitCount ++ b7.drop 42
  let b9 := b8.take 42 ++ encodeLE 1 channels ++ b8.drop 43
  let b10 := b9.take 43 ++ encodeLE 1 topDown ++ b9.drop 44
  have hb1 : b1.length = 48 := by
    simp [b1, h48_0, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have hb2 : b2.length = 48 := by
    simp [b2, hb1, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have hb3 : b3.length = 48 := by
    simp [b3, hb2, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have hb4 : b4.length = 48 := by
    simp [b4, hb3, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have hb5 : b5.length = 48 := by
    simp [b5, hb4, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have hb6 : b6.length = 48 := by
    simp [b6, hb5, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have hb7 : b7.length = 48 := by
    simp [b7, hb6, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have hb8 : b8.length = 48 := by
    simp [b8, hb7, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have hb9 : b9.length = 48 := by
    simp [b9, hb8, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have hb10 : b10.length = 48 := by
    simp [b10, hb9, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have hFin : ((((((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6).upd 3 b7).upd 3 b8).upd 3 b9).upd 3 b10)
      = s.mem.upd 3 b10 := by
    simp [mem_upd_same]
  have hfin2 : niInfoBlock obl0 rowStride outSize paletteOffset width height pixelOffset paletteEntries bitCount channels topDown = b10 := rfl
  have hfin : s.mem.upd 3 (niInfoBlock obl0 rowStride outSize paletteOffset width height pixelOffset paletteEntries bitCount channels topDown)
      = ((((((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6).upd 3 b7).upd 3 b8).upd 3 b9).upd 3 b10) := by
    rw [hfin2]
    exact hFin.symm

  -- store rowStride u64 @0
  let s1 : State := { s with mem := s.mem.upd 3 b1 }
  have hF1 : EvE Gen.prog s (.field (.var 2) 0) (.ptr 3 0) :=
    EvE.field (EvE.var hl2) (ptrAddN_ok hMem (by omega))
  have hV1 : EvE Gen.prog s (.var 11) (.int ⟨64, false⟩ rowStride) := EvE.var hl11
  have hSt1 : ExS Gen.prog s
      (.store (.int ⟨64, false⟩) (.field (.var 2) 0) (.var 11)) .normal s1 :=
    ExS.store hF1 hV1 hro (store_field_u64 s.mem 3 obl0 hMem h48_0 0 (by omega) rowStride hr64)

  -- store outSize u64 @8
  let s2 : State := { s1 with mem := (s.mem.upd 3 b1).upd 3 b2 }
  have h2s : EvE Gen.prog s1 (.var 2) (.ptr 3 0) := EvE.var hl2
  have hF2 : EvE Gen.prog s1 (.field (.var 2) 8) (.ptr 3 8) :=
    EvE.field h2s (ptrAddN_ok (by rfl : (s.mem.upd 3 b1) 3 = some b1) (by omega))
  have hV2 : EvE Gen.prog s1 (.var 12) (.int ⟨64, false⟩ outSize) := EvE.var hl12
  have hSt2 : ExS Gen.prog s1
      (.store (.int ⟨64, false⟩) (.field (.var 2) 8) (.var 12)) .normal s2 :=
    ExS.store hF2 hV2 hro (store_field_u64 (s.mem.upd 3 b1) 3 b1 (by rfl : (s.mem.upd 3 b1) 3 = some b1) hb1 8 (by omega) outSize hoSize)
  -- ========== store paletteOffset u64 @16 ==========
  let s3 : State := { s with mem := (((s.mem.upd 3 b1).upd 3 b2).upd 3 b3) }
  have hF3 : EvE Gen.prog s2 (.field (.var 2) 16) (.ptr 3 16) :=
    EvE.field (EvE.var hl2) (ptrAddN_ok (by rfl : (((s.mem.upd 3 b1).upd 3 b2)) 3 = some b2) (by omega))
  have hV3 : EvE Gen.prog s2 (.var 14) (.int ⟨64, false⟩ paletteOffset) := EvE.var hl14
  have hSt3 : ExS Gen.prog s2
      (.store (.int ⟨64, false⟩) (.field (.var 2) 16) (.var 14)) .normal s3 :=
    ExS.store hF3 hV3 hro (store_field_u64 (((s.mem.upd 3 b1).upd 3 b2)) 3 b2 (by rfl : (((s.mem.upd 3 b1).upd 3 b2)) 3 = some b2) hb2 16 (by omega) paletteOffset hpOffset)
  -- ========== store width u32 @24 ==========
  let s4 : State := { s with mem := ((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4) }
  have hF4 : EvE Gen.prog s3 (.field (.var 2) 24) (.ptr 3 24) :=
    EvE.field (EvE.var hl2) (ptrAddN_ok (by rfl : ((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3)) 3 = some b3) (by omega))
  have hV4 : EvE Gen.prog s3 (.var 7) (.int ⟨32, false⟩ width) := EvE.var hl7
  have hSt4 : ExS Gen.prog s3
      (.store (.int ⟨32, false⟩) (.field (.var 2) 24) (.var 7)) .normal s4 :=
    ExS.store hF4 hV4 hro (store_field_u32 ((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3)) 3 b3 (by rfl : ((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3)) 3 = some b3) hb3 24 (by omega) width hWidth)
  -- ========== store height u32 @28 ==========
  let s5 : State := { s with mem := (((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5) }
  have hF5 : EvE Gen.prog s4 (.field (.var 2) 28) (.ptr 3 28) :=
    EvE.field (EvE.var hl2) (ptrAddN_ok (by rfl : (((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4)) 3 = some b4) (by omega))
  have hV5 : EvE Gen.prog s4 (.var 8) (.int ⟨32, false⟩ height) := EvE.var hl8
  have hSt5 : ExS Gen.prog s4
      (.store (.int ⟨32, false⟩) (.field (.var 2) 28) (.var 8)) .normal s5 :=
    ExS.store hF5 hV5 hro (store_field_u32 (((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4)) 3 b4 (by rfl : (((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4)) 3 = some b4) hb4 28 (by omega) height hHeight)
  -- ========== store pixelOffset u32 @32 ==========
  let s6 : State := { s with mem := ((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6) }
  have hF6 : EvE Gen.prog s5 (.field (.var 2) 32) (.ptr 3 32) :=
    EvE.field (EvE.var hl2) (ptrAddN_ok (by rfl : ((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5)) 3 = some b5) (by omega))
  have hV6 : EvE Gen.prog s5 (.var 3) (.int ⟨32, false⟩ pixelOffset) := EvE.var hl3
  have hSt6 : ExS Gen.prog s5
      (.store (.int ⟨32, false⟩) (.field (.var 2) 32) (.var 3)) .normal s6 :=
    ExS.store hF6 hV6 hro (store_field_u32 ((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5)) 3 b5 (by rfl : ((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5)) 3 = some b5) hb5 32 (by omega) pixelOffset hpSize)
  -- ========== store paletteEntries u32 @36 (cast64->u32) ==========
  let s7 : State := { s with mem := (((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6).upd 3 b7) }
  have hF7 : EvE Gen.prog s6 (.field (.var 2) 36) (.ptr 3 36) :=
    EvE.field (EvE.var hl2) (ptrAddN_ok (by rfl : (((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6)) 3 = some b6) (by omega))
  have hV7 : EvE Gen.prog s6 (.cast ⟨32, false⟩ (.var 13)) (.int ⟨32, false⟩ paletteEntries) :=
    EvE.cast (EvE.var hl13) (u64_u32_trunc_cast paletteEntries hEntries)
  have hSt7 : ExS Gen.prog s6
      (.store (.int ⟨32, false⟩) (.field (.var 2) 36) (.cast ⟨32, false⟩ (.var 13))) .normal s7 :=
    ExS.store hF7 hV7 hro (store_field_u32 (((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6)) 3 b6 (by rfl : (((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6)) 3 = some b6) hb6 36 (by omega) paletteEntries hEntries)
  -- ========== store bitCount u16 @40 ==========
  let s8 : State := { s with mem := ((((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6).upd 3 b7).upd 3 b8) }
  have hF8 : EvE Gen.prog s7 (.field (.var 2) 40) (.ptr 3 40) :=
    EvE.field (EvE.var hl2) (ptrAddN_ok (by rfl : ((((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6).upd 3 b7)) 3 = some b7) (by omega))
  have hV8 : EvE Gen.prog s7 (.var 5) (.int ⟨16, false⟩ bitCount) := EvE.var hl5
  have hSt8 : ExS Gen.prog s7
      (.store (.int ⟨16, false⟩) (.field (.var 2) 40) (.var 5)) .normal s8 :=
    ExS.store hF8 hV8 hro (store_field_u16 ((((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6).upd 3 b7)) 3 b7 (by rfl : ((((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6).upd 3 b7)) 3 = some b7) hb7 40 (by omega) bitCount hBc)
  -- ========== store channels u8 @42 ==========
  let s9 : State := { s with mem := (((((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6).upd 3 b7).upd 3 b8).upd 3 b9) }
  have hF9 : EvE Gen.prog s8 (.field (.var 2) 42) (.ptr 3 42) :=
    EvE.field (EvE.var hl2) (ptrAddN_ok (by rfl : (((((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6).upd 3 b7).upd 3 b8)) 3 = some b8) (by omega))
  have hV9 : EvE Gen.prog s8 (.var 9) (.int ⟨8, false⟩ channels) := EvE.var hl9
  have hSt9 : ExS Gen.prog s8
      (.store (.int ⟨8, false⟩) (.field (.var 2) 42) (.var 9)) .normal s9 :=
    ExS.store hF9 hV9 hro (store_field_u8 (((((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6).upd 3 b7).upd 3 b8)) 3 b8 (by rfl : (((((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6).upd 3 b7).upd 3 b8)) 3 = some b8) hb8 42 (by omega) channels hCh)
  -- ========== store topDown u8 @43 ==========
  let s10 : State := { s with mem := ((((((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6).upd 3 b7).upd 3 b8).upd 3 b9).upd 3 b10) }
  have hF10 : EvE Gen.prog s9 (.field (.var 2) 43) (.ptr 3 43) :=
    EvE.field (EvE.var hl2) (ptrAddN_ok (by rfl : ((((((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6).upd 3 b7).upd 3 b8).upd 3 b9)) 3 = some b9) (by omega))
  have hV10 : EvE Gen.prog s9 (.var 10) (.int ⟨8, false⟩ topDown) := EvE.var hl10
  have hSt10 : ExS Gen.prog s9
      (.store (.int ⟨8, false⟩) (.field (.var 2) 43) (.var 10)) .normal s10 :=
    ExS.store hF10 hV10 hro (store_field_u8 ((((((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6).upd 3 b7).upd 3 b8).upd 3 b9)) 3 b9 (by rfl : ((((((((((s.mem.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 b6).upd 3 b7).upd 3 b8).upd 3 b9)) 3 = some b9) hb9 43 (by omega) topDown hTd)
  have hret : ExS Gen.prog s10 (.ret (some (.const (.int ⟨32, true⟩ 0)))) (Outcome.ret (some (.int ⟨32, true⟩ 0))) s10 :=
    ExS.ret (EvE.const _)
  rw [hfin]
  exact ExS.seq hSt1 (ExS.seq hSt2 (ExS.seq hSt3 (ExS.seq hSt4 (ExS.seq hSt5 (ExS.seq hSt6 (ExS.seq hSt7 (ExS.seq hSt8 (ExS.seq hSt9 (ExS.seq hSt10 (hret))))))))))

end NANO.C.Proofs


namespace NANO.C.Proofs
open NANO NANO.C

/-- The palette bad-check `.ite` (the `.lor` condition evaluating to false):
    `entries = 0 ∨ entries > 256 ∨ paletteOffset + entries*4 > pixelOffset`. -/
theorem palette_check_skip {s : State} {entries paletteOffset pixelOffset : Nat}
    (hE0 : ¬ entries = 0) (hEmax : entries ≤ 256)
    (hOffsetFits : paletteOffset + entries * 4 ≤ pixelOffset)
    (hE64 : entries < 18446744073709551616)
    (hPO64 : paletteOffset ≤ 4294967309) (hp64 : pixelOffset < 18446744073709551616)
    (hp32 : pixelOffset < 4294967296)
    (hl3 : s.locals 3 = some (Val.int ⟨32, false⟩ pixelOffset))
    (hl13 : s.locals 13 = some (Val.int ⟨64, false⟩ entries))
    (hl14 : s.locals 14 = some (Val.int ⟨64, false⟩ paletteOffset)) :
    ExS Gen.prog s
      (.ite (.lor
        (.lor
          (.bin .eq (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
          (.bin .gt (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
        (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 14) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.var 3))))
        (.ret (some (.const (.int ⟨32, true⟩ 10)))) .skip)
      .normal s := by
  have hEcast : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))) (.int ⟨64, false⟩ 0) :=
    EvE.cast (EvE.const _) (u32_u64_cast 0 (by decide))
  have hEcast256 : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256))) (.int ⟨64, false⟩ 256) :=
    EvE.cast (EvE.const _) (u32_u64_cast 256 (by decide))
  have hEcast4 : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))) (.int ⟨64, false⟩ 4) :=
    EvE.cast (EvE.const _) (u32_u64_cast 4 (by decide))
  have hnE : EvE Gen.prog s (.var 13) (.int ⟨64, false⟩ entries) := EvE.var hl13
  have hnO : EvE Gen.prog s (.var 14) (.int ⟨64, false⟩ paletteOffset) := EvE.var hl14
  have hnPx : EvE Gen.prog s (.var 3) (.int ⟨32, false⟩ pixelOffset) := EvE.var hl3
  have hpPx : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 3)) (.int ⟨64, false⟩ pixelOffset) :=
    cast_n_proof 3 hl3 (by omega)
  have hMul4 : EvE Gen.prog s
      (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))
      (.int ⟨64, false⟩ (entries * 4)) :=
    EvE.bin hnE hEcast4 (bin_u64_mul entries 4 (by omega))
  have hMul4B : True := trivial
  have hAdd : EvE Gen.prog s
      (.bin .add (some ⟨64, false⟩) (.var 14) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))))
      (.int ⟨64, false⟩ (paletteOffset + entries * 4)) :=
    EvE.bin hnO hMul4 (bin_u64_add paletteOffset (entries * 4) (by omega))
  have hMic : EvE Gen.prog s
      (.bin .eq (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
      (boolVal false) := by
    have eCmp : EvE Gen.prog s
        (.bin .eq (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
        (boolVal (decide (entries = 0))) :=
      EvE.bin hnE hEcast (bin_u64_eq _ _)
    rwa [decide_eq_false_iff_not.mpr hE0] at eCmp
  have hMax : EvE Gen.prog s
      (.bin .gt (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256))))
      (boolVal false) := by
    have eCmp : EvE Gen.prog s
        (.bin .gt (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256))))
        (boolVal (decide (entries > 256))) :=
      EvE.bin hnE hEcast256 (bin_u64_gt entries 256)
    rwa [decide_eq_false_iff_not.mpr (by omega)] at eCmp
  have hAddGt : EvE Gen.prog s
      (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 14) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.var 3)))
      (boolVal false) := by
    have eCmp : EvE Gen.prog s
        (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 14) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.var 3)))
        (boolVal (decide (paletteOffset + entries * 4 > pixelOffset))) :=
      EvE.bin hAdd hpPx (bin_u64_gt _ _)
    rwa [decide_eq_false_iff_not.mpr (by omega)] at eCmp
  have hLo1 : EvE Gen.prog s
      (.lor
        (.bin .eq (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
        (.bin .gt (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
      (boolVal false) :=
    EvE.lor_false hMic (truthy_boolVal false) hMax (truthy_boolVal false)
  have he : EvE Gen.prog s
      (.lor
        (.lor
          (.bin .eq (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
          (.bin .gt (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
        (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 14) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.var 3))))
      (boolVal false) :=
    EvE.lor_false hLo1 (truthy_boolVal false) hAddGt (truthy_boolVal false)
  exact ExS.ite he (truthy_boolVal false) ExS.skip

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- The palette bad-check `.ite` when the condition fires → return `10`. -/
theorem palette_check_fire {s : State} {entries paletteOffset pixelOffset : Nat}
    (hBad : entries = 0 ∨ 256 < entries ∨ pixelOffset < paletteOffset + entries * 4)
    (hEntries : entries < 4294967296)
    (hE64 : entries < 18446744073709551616)
    (hPO64 : paletteOffset ≤ 4294967309) (hp64 : pixelOffset < 18446744073709551616)
    (hp32 : pixelOffset < 4294967296)
    (hl3 : s.locals 3 = some (Val.int ⟨32, false⟩ pixelOffset))
    (hl13 : s.locals 13 = some (Val.int ⟨64, false⟩ entries))
    (hl14 : s.locals 14 = some (Val.int ⟨64, false⟩ paletteOffset)) :
    ExS Gen.prog s
      (.ite (.lor
        (.lor
          (.bin .eq (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
          (.bin .gt (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
        (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 14) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.var 3))))
        (.ret (some (.const (.int ⟨32, true⟩ 10)))) .skip)
      (Outcome.ret (some (.int ⟨32, true⟩ 10))) s := by
  have hEcast : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))) (.int ⟨64, false⟩ 0) :=
    EvE.cast (EvE.const _) (u32_u64_cast 0 (by decide))
  have hEcast256 : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256))) (.int ⟨64, false⟩ 256) :=
    EvE.cast (EvE.const _) (u32_u64_cast 256 (by decide))
  have hEcast4 : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))) (.int ⟨64, false⟩ 4) :=
    EvE.cast (EvE.const _) (u32_u64_cast 4 (by decide))
  have hnE : EvE Gen.prog s (.var 13) (.int ⟨64, false⟩ entries) := EvE.var hl13
  have hnO : EvE Gen.prog s (.var 14) (.int ⟨64, false⟩ paletteOffset) := EvE.var hl14
  have hnPx : EvE Gen.prog s (.var 3) (.int ⟨32, false⟩ pixelOffset) := EvE.var hl3
  have hpPx : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 3)) (.int ⟨64, false⟩ pixelOffset) :=
    cast_n_proof 3 hl3 (by omega)
  have hMul4 : EvE Gen.prog s
      (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))
      (.int ⟨64, false⟩ (entries * 4)) :=
    EvE.bin hnE hEcast4 (bin_u64_mul entries 4 (by omega))
  have hMul4B : True := trivial
  have hAdd : EvE Gen.prog s
      (.bin .add (some ⟨64, false⟩) (.var 14) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))))
      (.int ⟨64, false⟩ (paletteOffset + entries * 4)) :=
    EvE.bin hnO hMul4 (bin_u64_add paletteOffset (entries * 4) (by omega))
  have hMic : EvE Gen.prog s
      (.bin .eq (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
      (boolVal (decide (entries = 0))) :=
    EvE.bin hnE hEcast (bin_u64_eq _ _)
  have hMax : EvE Gen.prog s
      (.bin .gt (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256))))
      (boolVal (decide (entries > 256))) :=
    EvE.bin hnE hEcast256 (bin_u64_gt entries 256)
  have hAddGt : EvE Gen.prog s
      (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 14) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.var 3)))
      (boolVal (decide (paletteOffset + entries * 4 > pixelOffset))) :=
    EvE.bin hAdd hpPx (bin_u64_gt _ _)
  by_cases hA : entries = 0
  · have he : EvE Gen.prog s
        (.lor
          (.lor
            (.bin .eq (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
            (.bin .gt (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
          (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 14) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.var 3))))
        (boolVal true) := by
      have heq : EvE Gen.prog s
          (.bin .eq (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
          (boolVal true) := by
        rwa [decide_eq_true_eq.mpr hA] at hMic
      exact EvE.lor_true (EvE.lor_true heq (truthy_boolVal true)) (truthy_boolVal true)
    exact ExS.ite he (truthy_boolVal true) (ExS.ret (EvE.const _))
  · by_cases hB : 256 < entries
    · have he : EvE Gen.prog s
          (.lor
            (.lor
              (.bin .eq (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
              (.bin .gt (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
            (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 14) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.var 3))))
          (boolVal true) := by
        have heq : EvE Gen.prog s
            (.bin .eq (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
            (boolVal false) := by
          rwa [decide_eq_false_iff_not.mpr hA] at hMic
        have hgt : EvE Gen.prog s
            (.bin .gt (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256))))
            (boolVal true) := by
          rwa [decide_eq_true_eq.mpr hB] at hMax
        have hLo : EvE Gen.prog s
            (.lor
              (.bin .eq (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
              (.bin .gt (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
            (boolVal true) :=
          EvE.lor_false heq (truthy_boolVal false) hgt (truthy_boolVal true)
        exact EvE.lor_true hLo (truthy_boolVal true)
      exact ExS.ite he (truthy_boolVal true) (ExS.ret (EvE.const _))
    · by_cases hC : pixelOffset < paletteOffset + entries * 4
      · have he : EvE Gen.prog s
            (.lor
              (.lor
                (.bin .eq (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
                (.bin .gt (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
              (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 14) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.var 3))))
            (boolVal true) := by
          have heq : EvE Gen.prog s
              (.bin .eq (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
              (boolVal false) := by
            rwa [decide_eq_false_iff_not.mpr hA] at hMic
          have hgtFalse : ¬ entries > 256 := by omega
          have hgt : EvE Gen.prog s
              (.bin .gt (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256))))
              (boolVal false) := by
            rwa [decide_eq_false_iff_not.mpr hgtFalse] at hMax
          have hLo : EvE Gen.prog s
              (.lor
                (.bin .eq (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
                (.bin .gt (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
              (boolVal false) :=
            EvE.lor_false heq (truthy_boolVal false) hgt (truthy_boolVal false)
          have hgt3 : EvE Gen.prog s
              (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 14) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.var 3)))
              (boolVal true) := by
            rwa [decide_eq_true_eq.mpr hC] at hAddGt
          exact EvE.lor_false hLo (truthy_boolVal false) hgt3 (truthy_boolVal true)
        exact ExS.ite he (truthy_boolVal true) (ExS.ret (EvE.const _))
      · exfalso
        rcases hBad with hBadA | hBadB | hBadC
        · exact absurd hBadA hA
        · exact absurd hBadB hB
        · exact absurd hBadC hC


end NANO.C.Proofs
