/-
  Evaluations of `ni_tga_header`'s gate conditions (C expression ⇒ truthiness),
  as reusable `EvE` lemmas. Each states the exact `boolVal` produced.
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Lemmas
import NANO.Spec
import NANO.Tga
import NANO.C.Proofs.Core
import NANO.C.Proofs.NiGeometryTail
import NANO.C.Proofs.NiBmpDecode
import NANO.C.Proofs.Bmp
import NANO.C.Proofs.NiTgaHeader

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 1600000

namespace NANO.C.Proofs
open NANO NANO.C

/-- Dimensions gate: `w==0 || h==0`. -/
theorem ev_tga_dims (s : State) (w hh : Nat)
    (l6 : s.locals 6 = some (.int u16 w)) (l7 : s.locals 7 = some (.int u16 hh))
    (hw : w < 65536) (hhh : hh < 65536) :
    EvE Gen.prog s (.lor (.bin .eq (some u32) (.cast u32 (.var 6)) (.const (.int u32 0)))
                          (.bin .eq (some u32) (.cast u32 (.var 7)) (.const (.int u32 0))))
      (boolVal (decide (w = 0) || decide (hh = 0))) := by
  have eq6 : EvE Gen.prog s (.bin .eq (some u32) (.cast u32 (.var 6)) (.const (.int u32 0))) (boolVal (decide (w = 0))) :=
    EvE.bin (EvE.cast (EvE.var l6) (u16_u32_cast w hw)) (EvE.const _) (bin_u32_eq w 0)
  have eq7 : EvE Gen.prog s (.bin .eq (some u32) (.cast u32 (.var 7)) (.const (.int u32 0))) (boolVal (decide (hh = 0))) :=
    EvE.bin (EvE.cast (EvE.var l7) (u16_u32_cast hh hhh)) (EvE.const _) (bin_u32_eq hh 0)
  by_cases hw0 : w = 0
  · have e6 := eq6; rw [decide_eq_true_eq.mpr hw0] at e6
    have hv : (decide (w = 0) || decide (hh = 0)) = true := by rw [decide_eq_true_eq.mpr hw0]; rfl
    rw [hv]; exact EvE.lor_true e6 (truthy_boolVal true)
  · have e6 := eq6; rw [decide_eq_false_iff_not.mpr hw0] at e6
    by_cases hh0 : hh = 0
    · have e7 := eq7; rw [decide_eq_true_eq.mpr hh0] at e7
      have hv : (decide (w = 0) || decide (hh = 0)) = true := by
        rw [decide_eq_false_iff_not.mpr hw0, decide_eq_true_eq.mpr hh0]; rfl
      rw [hv]; exact EvE.lor_false e6 (truthy_boolVal false) e7 (truthy_boolVal true)
    · have e7 := eq7; rw [decide_eq_false_iff_not.mpr hh0] at e7
      have hv : (decide (w = 0) || decide (hh = 0)) = false := by
        rw [decide_eq_false_iff_not.mpr hw0, decide_eq_false_iff_not.mpr hh0]; rfl
      rw [hv]; exact EvE.lor_false e6 (truthy_boolVal false) e7 (truthy_boolVal false)

/-- Color-map gate: `colorMapType != 0`. -/
theorem ev_tga_cmap (s : State) (b1v : Nat) (l4 : s.locals 4 = some (.int u8 b1v))
    (hb1 : b1v < 256) :
    EvE Gen.prog s (.bin .ne (some u32) (.cast u32 (.var 4)) (.const (.int u32 0)))
      (boolVal (decide (b1v ≠ 0))) :=
  EvE.bin (EvE.cast (EvE.var l4) (u8_u32_cast b1v hb1)) (EvE.const _) (bin_u32_ne b1v 0)

/-- Image-type validity gate: `type==3 || type==11`. -/
theorem ev_tga_chanbranch (s : State) (b2v : Nat) (l5 : s.locals 5 = some (.int u8 b2v))
    (hb2 : b2v < 256) :
    EvE Gen.prog s (.lor (.bin .eq (some u32) (.cast u32 (.var 5)) (.const (.int u32 3)))
                          (.bin .eq (some u32) (.cast u32 (.var 5)) (.const (.int u32 11))))
      (boolVal (decide (b2v = 3) || decide (b2v = 11))) := by
  have eq3 : EvE Gen.prog s (.bin .eq (some u32) (.cast u32 (.var 5)) (.const (.int u32 3))) (boolVal (decide (b2v = 3))) :=
    EvE.bin (EvE.cast (EvE.var l5) (u8_u32_cast b2v hb2)) (EvE.const _) (bin_u32_eq b2v 3)
  have eq11 : EvE Gen.prog s (.bin .eq (some u32) (.cast u32 (.var 5)) (.const (.int u32 11))) (boolVal (decide (b2v = 11))) :=
    EvE.bin (EvE.cast (EvE.var l5) (u8_u32_cast b2v hb2)) (EvE.const _) (bin_u32_eq b2v 11)
  by_cases h3 : b2v = 3
  · have e := eq3; rw [decide_eq_true_eq.mpr h3] at e
    have hv : (decide (b2v = 3) || decide (b2v = 11)) = true := by rw [decide_eq_true_eq.mpr h3]; rfl
    rw [hv]; exact EvE.lor_true e (truthy_boolVal true)
  · have e3 := eq3; rw [decide_eq_false_iff_not.mpr h3] at e3
    by_cases h11 : b2v = 11
    · have e11 := eq11; rw [decide_eq_true_eq.mpr h11] at e11
      have hv : (decide (b2v = 3) || decide (b2v = 11)) = true := by
        rw [decide_eq_false_iff_not.mpr h3, decide_eq_true_eq.mpr h11]; rfl
      rw [hv]; exact EvE.lor_false e3 (truthy_boolVal false) e11 (truthy_boolVal true)
    · have e11 := eq11; rw [decide_eq_false_iff_not.mpr h11] at e11
      have hv : (decide (b2v = 3) || decide (b2v = 11)) = false := by
        rw [decide_eq_false_iff_not.mpr h3, decide_eq_false_iff_not.mpr h11]; rfl
      rw [hv]; exact EvE.lor_false e3 (truthy_boolVal false) e11 (truthy_boolVal false)

/-- Depth-channels inner test `pixelDepth != 8`. -/
theorem ev_tga_pd8 (s : State) (pd : Nat) (l8 : s.locals 8 = some (.int u8 pd)) (hpd : pd < 256) :
    EvE Gen.prog s (.bin .ne (some u32) (.cast u32 (.var 8)) (.const (.int u32 8)))
      (boolVal (decide (pd ≠ 8))) :=
  EvE.bin (EvE.cast (EvE.var l8) (u8_u32_cast pd hpd)) (EvE.const _) (bin_u32_ne pd 8)

/-- Depth test `pixelDepth == 24`. -/
theorem ev_tga_pd24 (s : State) (pd : Nat) (l8 : s.locals 8 = some (.int u8 pd)) (hpd : pd < 256) :
    EvE Gen.prog s (.bin .eq (some u32) (.cast u32 (.var 8)) (.const (.int u32 24)))
      (boolVal (decide (pd = 24))) :=
  EvE.bin (EvE.cast (EvE.var l8) (u8_u32_cast pd hpd)) (EvE.const _) (bin_u32_eq pd 24)

/-- Depth test `pixelDepth == 32`. -/
theorem ev_tga_pd32 (s : State) (pd : Nat) (l8 : s.locals 8 = some (.int u8 pd)) (hpd : pd < 256) :
    EvE Gen.prog s (.bin .eq (some u32) (.cast u32 (.var 8)) (.const (.int u32 32)))
      (boolVal (decide (pd = 32))) :=
  EvE.bin (EvE.cast (EvE.var l8) (u8_u32_cast pd hpd)) (EvE.const _) (bin_u32_eq pd 32)

/-- ID-length gate: `18 + idLength > size`. -/
theorem ev_tga_id (s : State) (size id : Nat)
    (l1 : s.locals 1 = some (.int u64 size)) (l3 : s.locals 3 = some (.int u8 id))
    (hid : id < 256) (hdv : 18 + id < 2 ^ 64) :
    EvE Gen.prog s (.bin .gt (some u64)
        (.bin .add (some u64) (.cast u64 (.const (.int i32 18))) (.cast u64 (.var 3))) (.var 1))
      (boolVal (decide (18 + id > size))) :=
  EvE.bin (EvE.bin (EvE.cast (EvE.const _) (i32_u64_cast 18 (by omega)))
             (EvE.cast (EvE.var l3) (u8_u64_cast id hid)) (bin_u64_add 18 id hdv))
    (EvE.var l1) (bin_u64_gt (18 + id) size)

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- `land` of two `boolVal`s evaluates to the `&&` of their Bool values. -/
theorem land_step {s : State} {A B : Expr} {ba bb : Bool}
    (hA : EvE Gen.prog s A (boolVal ba)) (hB : EvE Gen.prog s B (boolVal bb)) :
    EvE Gen.prog s (.land A B) (boolVal (ba && bb)) := by
  cases ba
  · exact EvE.land_false hA (truthy_boolVal false)
  · exact EvE.land_true hA (truthy_boolVal true) hB (truthy_boolVal bb)

/-- Image-type validity gate (`!=2 && !=3 && !=10 && !=11`). -/
theorem ev_tga_badtype (s : State) (b2 : Nat) (l5 : s.locals 5 = some (.int u8 b2))
    (hb2 : b2 < 256) :
    EvE Gen.prog s
      (.land (.land (.land (.bin .ne (some u32) (.cast u32 (.var 5)) (.const (.int u32 2)))
                          (.bin .ne (some u32) (.cast u32 (.var 5)) (.const (.int u32 3))))
                     (.bin .ne (some u32) (.cast u32 (.var 5)) (.const (.int u32 10))))
            (.bin .ne (some u32) (.cast u32 (.var 5)) (.const (.int u32 11))))
      (boolVal (decide (b2 ≠ 2) && decide (b2 ≠ 3) && decide (b2 ≠ 10) && decide (b2 ≠ 11))) := by
  have nb : ∀ k, EvE Gen.prog s (.bin .ne (some u32) (.cast u32 (.var 5)) (.const (.int u32 k)))
      (boolVal (decide (b2 ≠ k))) :=
    fun k => EvE.bin (EvE.cast (EvE.var l5) (u8_u32_cast b2 hb2)) (EvE.const _) (bin_u32_ne b2 k)
  exact land_step (land_step (land_step (nb 2) (nb 3)) (nb 10)) (nb 11)

end NANO.C.Proofs
