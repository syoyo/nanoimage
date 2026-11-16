/-/
  BMP refinement proofs — top-level signature/layout checks, and the
  composite `ni_bmp_geometry_exs` verdict.
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Hoare
import NANO.C.Lemmas
import NANO.Spec
import NANO.Bmp
import NANO.C.Proofs.Core
import NANO.C.Proofs.NiGeometryTail
import NANO.C.Proofs.NiGeometryPos
import NANO.C.Proofs.NiGeometryNegNormal

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 40000

namespace NANO.C.Proofs
open NANO NANO.C

/-! ## `ni_bmp_sig_ok` -/

theorem ni_bmp_sig_ok_exs (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hd2 : 2 ≤ d.length) (ro : Bool) :
    ∃ s', ExS Gen.prog ⟨frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size], m, ro⟩ Gen.ni_bmp_sig_ok.body
      (.ret (some (.int i32 (if sigOk size d then 1 else 0)))) s' := by
  have hl0 : frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size] 0 = some (.ptr bd 0) := rfl
  have hl1 : frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size] 1 = some (.int u64 size) := rfl
  have hGE : EvE Gen.prog { locals := frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size], mem := m, ro := ro } (.bin .ge (some ⟨64, false⟩) (.var 1)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 54)))) (boolVal (decide (54 ≤ size))) := by
    have hconst : EvE Gen.prog { locals := frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size], mem := m, ro := ro } (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 54))) (.int ⟨64, false⟩ 54) :=
      EvE.cast (EvE.const (v := (.int ⟨32, false⟩ 54))) rfl
    exact EvE.bin (EvE.var hl1) hconst rfl
  have hLoad0 : EvE Gen.prog { locals := frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size], mem := m, ro := ro } (.cast i32 (.load (.int u8) (.index (.var 0) (.const (.int i32 0)) 1)))
      (.int i32 (byteAt d 0)) :=
    ev_byte_const (s := { locals := frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size], mem := m, ro := ro }) (bd := bd) (k := 0) hm hl0 (by omega) (by omega)
  have hLoad1 : EvE Gen.prog { locals := frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size], mem := m, ro := ro } (.cast i32 (.load (.int u8) (.index (.var 0) (.const (.int i32 1)) 1)))
      (.int i32 (byteAt d 1)) :=
    ev_byte_const (s := { locals := frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size], mem := m, ro := ro }) (bd := bd) (k := 1) hm hl0 (by omega) (by omega)
  have hEQ0 : EvE Gen.prog { locals := frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size], mem := m, ro := ro } (.bin .eq (some ⟨32, true⟩)
        (.cast i32 (.load (.int u8) (.index (.var 0) (.const (.int i32 0)) 1)))
        (.const (.int i32 66))) (boolVal (decide (byteAt d 0 = 66))) := by
    have hconst : EvE Gen.prog { locals := frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size], mem := m, ro := ro } (.const (.int i32 66)) (.int i32 66) := EvE.const _
    exact EvE.bin hLoad0 hconst (bin_i32_eq_bytes (byteAt d 0) 66 (byteAt_lt d 0) (by simp))
  have hEQ1 : EvE Gen.prog { locals := frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size], mem := m, ro := ro } (.bin .eq (some ⟨32, true⟩)
        (.cast i32 (.load (.int u8) (.index (.var 0) (.const (.int i32 1)) 1)))
        (.const (.int i32 77))) (boolVal (decide (byteAt d 1 = 77))) := by
    have hconst : EvE Gen.prog { locals := frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size], mem := m, ro := ro } (.const (.int i32 77)) (.int i32 77) := EvE.const _
    exact EvE.bin hLoad1 hconst (bin_i32_eq_bytes (byteAt d 1) 77 (byteAt_lt d 1) (by simp))

  -- The body is `.ret (some (.land (.land GE EQ0) EQ1))`. `.land` short-circuits.
  let s0 : State := ⟨frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size], m, ro⟩
  let GE : Expr := (.bin .ge (some ⟨64, false⟩) (.var 1) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 54))))
  let EQ0 : Expr := (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.var 0) (.const (.int ⟨32, true⟩ 0)) 1))) (.const (.int ⟨32, true⟩ 66)))
  let EQ1 : Expr := (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.var 0) (.const (.int ⟨32, true⟩ 1)) 1))) (.const (.int ⟨32, true⟩ 77)))
  have eGE : EvE Gen.prog s0 GE (boolVal (decide (54 ≤ size))) := hGE
  have eEQ0 : EvE Gen.prog s0 EQ0 (boolVal (decide (byteAt d 0 = 66))) := hEQ0
  have eEQ1 : EvE Gen.prog s0 EQ1 (boolVal (decide (byteAt d 1 = 77))) := hEQ1
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  by_cases hGE54 : 54 ≤ size
  · by_cases h00 : byteAt d 0 = 66
    · by_cases h01 : byteAt d 1 = 77
      -- accept: all three decisions are true
      have eGE1 : EvE Gen.prog s0 GE (boolVal true) := by
        rw [decide_eq_true_eq.mpr hGE54] at eGE; exact eGE
      have eEQ01 : EvE Gen.prog s0 EQ0 (boolVal true) := by
        rw [decide_eq_true_eq.mpr h00] at eEQ0; exact eEQ0
      have eEQ11 : EvE Gen.prog s0 EQ1 (boolVal true) := by
        rw [decide_eq_true_eq.mpr h01] at eEQ1; exact eEQ1
      have inner : EvE Gen.prog s0 (.land GE EQ0) (boolVal true) :=
        EvE.land_true eGE1 truthy_true eEQ01 truthy_true
      have louter : EvE Gen.prog s0 (.land (.land GE EQ0) EQ1) (boolVal true) :=
        EvE.land_true inner truthy_true eEQ11 truthy_true
      have hbv : (if sigOk size d then 1 else 0) = 1 := by
        show (if decide (54 ≤ size) && decide (byteAt d 0 = 66) && decide (byteAt d 1 = 77) then 1 else 0) = 1
        rw [decide_eq_true_eq.mpr hGE54, decide_eq_true_eq.mpr h00, decide_eq_true_eq.mpr h01]
        simp
      refine ⟨s0, ?_⟩
      rw [hbv]
      exact ExS.ret louter
      · -- byte d 1 != 'M': inner land true; outer land ends false
        have eGE1 : EvE Gen.prog s0 GE (boolVal true) := by
          rw [decide_eq_true_eq.mpr hGE54] at eGE; exact eGE
        have eEQ01 : EvE Gen.prog s0 EQ0 (boolVal true) := by
          rw [decide_eq_true_eq.mpr h00] at eEQ0; exact eEQ0
        have eEQ1f : EvE Gen.prog s0 EQ1 (boolVal false) := by
          rw [decide_eq_false_iff_not.mpr h01] at eEQ1; exact eEQ1
        have inner : EvE Gen.prog s0 (.land GE EQ0) (boolVal true) :=
          EvE.land_true eGE1 truthy_true eEQ01 truthy_true
        have louter : EvE Gen.prog s0 (.land (.land GE EQ0) EQ1) (boolVal false) :=
          EvE.land_true inner truthy_true eEQ1f (by rw [truthy_boolVal])
        have hbv : (if sigOk size d then 1 else 0) = 0 := by
          show (if decide (54 ≤ size) && decide (byteAt d 0 = 66) && decide (byteAt d 1 = 77) then 1 else 0) = 0
          rw [decide_eq_true_eq.mpr hGE54, decide_eq_true_eq.mpr h00, decide_eq_false_iff_not.mpr h01]
          simp
        refine ⟨s0, ?_⟩
        rw [hbv]
        exact ExS.ret louter
    · -- byte d 0 != 'B': inner land false; outer land short-circuits
      have tGE : truthy (boolVal (decide (54 ≤ size))) = .ok true := by
        rw [truthy_boolVal, decide_eq_true_eq.mpr hGE54]
      have t00f : truthy (boolVal (decide (byteAt d 0 = 66))) = .ok false := by
        rw [truthy_boolVal, decide_eq_false_iff_not.mpr h00]
      have inner : EvE Gen.prog s0 (.land GE EQ0) (boolVal false) :=
        EvE.land_true eGE tGE eEQ0 t00f
      have louter : EvE Gen.prog s0 (.land (.land GE EQ0) EQ1) (boolVal false) :=
        EvE.land_false inner truthy_false
      have hbv : (if sigOk size d then 1 else 0) = 0 := by
        show (if decide (54 ≤ size) && decide (byteAt d 0 = 66) && decide (byteAt d 1 = 77) then 1 else 0) = 0
        rw [decide_eq_true_eq.mpr hGE54, decide_eq_false_iff_not.mpr h00]
        simp
      refine ⟨s0, ?_⟩
      rw [hbv]
      exact ExS.ret louter
  · -- size too small: GE false; both lands short-circuit
    have tGEF : truthy (boolVal (decide (54 ≤ size))) = .ok false := by
      rw [truthy_boolVal, decide_eq_false_iff_not.mpr (by omega)]
    have inner : EvE Gen.prog s0 (.land GE EQ0) (boolVal false) :=
      EvE.land_false eGE tGEF
    have louter : EvE Gen.prog s0 (.land (.land GE EQ0) EQ1) (boolVal false) :=
      EvE.land_false inner truthy_false
    have hbv : (if sigOk size d then 1 else 0) = 0 := by
      show (if decide (54 ≤ size) && decide (byteAt d 0 = 66) && decide (byteAt d 1 = 77) then 1 else 0) = 0
      rw [decide_eq_false_iff_not.mpr (by omega)]
      simp
    refine ⟨s0, ?_⟩
    rw [hbv]
    exact ExS.ret louter

/-! ## `ni_bmp_layout_ok` -/

/-- `ni_bmp_layout_ok` returns 1 iff `layoutOk`. -/
theorem ni_bmp_layout_ok_exs (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hd : 18 ≤ d.length) (hlen : d.length < 2 ^ 64) (ro : Bool) :
    ∃ s', ExS Gen.prog ⟨frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size], m, ro⟩
      Gen.ni_bmp_layout_ok.body
      (.ret (some (.int i32 (if layoutOk size d then 1 else 0)))) s' := by
  let s0 : State := ⟨frameLocals [0, 1] [Val.ptr bd 0, Val.int u64 size], m, ro⟩
  have hl0 : s0.locals 0 = some (.ptr bd 0) := rfl
  have hl1 : s0.locals 1 = some (.int u64 size) := rfl
  have hp10 : EvE Gen.prog s0
      (.call 1 [(.index (.var 0) (.const (.int i32 10)) 1)]) (.int u32 (rd32le d 10)) :=
    EvE.call (EvArgs.cons (ev_ptr_const (k := 10) hm hl0 (by omega) (by omega)) EvArgs.nil) rfl rfl
      (ni_read_u32le_exs m bd d hm 10 (by omega) hlen true)
  let s1 : State := {s0 with locals := s0.locals.upd 2 (.int u32 (rd32le d 10))}
  have hl0' : s1.locals 0 = some (.ptr bd 0) := rfl
  have hp14 : EvE Gen.prog s1
      (.call 1 [(.index (.var 0) (.const (.int i32 14)) 1)]) (.int u32 (rd32le d 14)) :=
    EvE.call (EvArgs.cons (ev_ptr_const hm hl0' (by omega) (by omega)) EvArgs.nil) rfl rfl
      (ni_read_u32le_exs m bd d hm 14 (by omega) hlen true)
  let s2 : State := {s1 with locals := s1.locals.upd 3 (.int u32 (rd32le d 14))}
  have hl2 : s2.locals 2 = some (.int u32 (rd32le d 10)) := rfl
  have hl3 : s2.locals 3 = some (.int u32 (rd32le d 14)) := rfl
  have hl1_s2 : s2.locals 1 = some (.int u64 size) := rfl
  have hv2 : EvE Gen.prog s2 (.var 2) (.int u32 (rd32le d 10)) := EvE.var hl2
  have hv3 : EvE Gen.prog s2 (.var 3) (.int u32 (rd32le d 14)) := EvE.var hl3
  have hset1 : ExS Gen.prog s0
      (.set 2 (.call 1 [(.index (.var 0) (.const (.int i32 10)) 1)])) .normal s1 :=
    ExS.set hp10
  have hset2 : ExS Gen.prog s1
      (.set 3 (.call 1 [(.index (.var 0) (.const (.int i32 14)) 1)])) .normal s2 :=
    ExS.set hp14
  -- local layout: the condition `COND` and the two branches.
  let A : Expr := (.bin .lt (some ⟨32, false⟩) (.var 3) (.const (.int ⟨32, false⟩ 40)))
  let B : Expr := (.bin .gt (some ⟨64, false⟩)
      (.bin .add (some ⟨64, false⟩)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 14)))
        (.cast ⟨64, false⟩ (.var 3)))
      (.var 1))
  let C : Expr := (.bin .lt (some ⟨64, false⟩)
      (.cast ⟨64, false⟩ (.var 2))
      (.bin .add (some ⟨64, false⟩)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 14)))
        (.cast ⟨64, false⟩ (.var 3))))
  let D : Expr := (.bin .gt (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 2)) (.var 1))
  have hA : EvE Gen.prog s2 A (boolVal (decide (rd32le d 14 < 40))) :=
    EvE.bin hv3 (EvE.const _) (bin_u32_lt (rd32le d 14) 40)
  have hcast_const : EvE Gen.prog s2
      (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 14))) (.int ⟨64, false⟩ 14) :=
    EvE.cast (EvE.const _) rfl
  have hcast2 : EvE Gen.prog s2
      (.cast ⟨64, false⟩ (.var 2)) (.int ⟨64, false⟩ (rd32le d 10)) :=
    EvE.cast hv2 (u32_u64_cast (rd32le d 10) (rd32_lt d 10))
  have hcast3 : EvE Gen.prog s2
      (.cast ⟨64, false⟩ (.var 3)) (.int ⟨64, false⟩ (rd32le d 14)) :=
    EvE.cast hv3 (u32_u64_cast (rd32le d 14) (rd32_lt d 14))
  have hadd : EvE Gen.prog s2
      (.bin .add (some ⟨64, false⟩)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 14)))
        (.cast ⟨64, false⟩ (.var 3)))
      (.int ⟨64, false⟩ (14 + rd32le d 14)) :=
    EvE.bin hcast_const hcast3 (bin_u64_add 14 (rd32le d 14) (by have := rd32_lt d 14; omega))
  have hB : EvE Gen.prog s2 B (boolVal (decide (14 + rd32le d 14 > size))) :=
    EvE.bin hadd (EvE.var hl1_s2) (bin_u64_gt (14 + rd32le d 14) size)
  have hC : EvE Gen.prog s2 C (boolVal (decide (rd32le d 10 < 14 + rd32le d 14))) :=
    EvE.bin hcast2 hadd (bin_u64_lt (rd32le d 10) (14 + rd32le d 14))
  have hD : EvE Gen.prog s2 D (boolVal (decide (rd32le d 10 > size))) :=
    EvE.bin hcast2 (EvE.var hl1_s2) (bin_u64_gt (rd32le d 10) size)
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  by_cases hA34 : rd32le d 14 < 40
  · -- A true: short-circuit at A
    have hAe : EvE Gen.prog s2 A (boolVal true) := by
      rw [decide_eq_true_eq.mpr hA34] at hA; exact hA
    have tAe : truthy (boolVal (decide (rd32le d 14 < 40))) = .ok true := by
      rw [truthy_boolVal, decide_eq_true_eq.mpr hA34]
    have ei : EvE Gen.prog s2 (.lor A B) (boolVal true) := EvE.lor_true hAe truthy_true
    have ei2 : EvE Gen.prog s2 (.lor (.lor A B) C) (boolVal true) :=
      EvE.lor_true ei truthy_true
    have ei3 : EvE Gen.prog s2 (.lor (.lor (.lor A B) C) D) (boolVal true) :=
      EvE.lor_true ei2 truthy_true
    have hite : ExS Gen.prog s2 (.ite (.lor (.lor (.lor A B) C) D)
        (.ret (some (.const (.int ⟨32, true⟩ 0)))) .skip) (.ret (some (.int i32 0))) s2 :=
      ExS.ite ei3 truthy_true (ExS.ret (EvE.const _))
    have hbv : (if layoutOk size d then 1 else 0) = 0 := by
      show (if !(decide (rd32le d 14 < 40) || decide (14 + rd32le d 14 > size)
             || decide (rd32le d 10 < 14 + rd32le d 14) || decide (rd32le d 10 > size))
          then 1 else 0) = 0
      rw [decide_eq_true_eq.mpr hA34]
      simp
    have hst3 : ExS Gen.prog s2 (.seq (.ite (.lor (.lor (.lor A B) C) D)
        (.ret (some (.const (.int ⟨32, true⟩ 0)))) .skip)
        (.ret (some (.const (.int ⟨32, true⟩ 1))))) (.ret (some (.int i32 0))) s2 :=
      ExS.seq_ret hite
    refine ⟨s2, ?_⟩
    rw [hbv]
    exact ExS.seq hset1 (ExS.seq hset2 hst3)
  · by_cases hB55 : 14 + rd32le d 14 > size
    · -- B true: A false, B true; short-circuit at B
      have tA : truthy (boolVal (decide (rd32le d 14 < 40))) = .ok false := by
        rw [truthy_boolVal, decide_eq_false_iff_not.mpr hA34]
      have hBe : EvE Gen.prog s2 B (boolVal true) := by
        rw [decide_eq_true_eq.mpr hB55] at hB; exact hB
      have ei : EvE Gen.prog s2 (.lor A B) (boolVal true) := EvE.lor_false hA tA hBe truthy_true
      have ei2 : EvE Gen.prog s2 (.lor (.lor A B) C) (boolVal true) :=
        EvE.lor_true ei truthy_true
      have ei3 : EvE Gen.prog s2 (.lor (.lor (.lor A B) C) D) (boolVal true) :=
        EvE.lor_true ei2 truthy_true
      have hite : ExS Gen.prog s2 (.ite (.lor (.lor (.lor A B) C) D)
          (.ret (some (.const (.int ⟨32, true⟩ 0)))) .skip) (.ret (some (.int i32 0))) s2 :=
        ExS.ite ei3 truthy_true (ExS.ret (EvE.const _))
      have hbv : (if layoutOk size d then 1 else 0) = 0 := by
        show (if !(decide (rd32le d 14 < 40) || decide (14 + rd32le d 14 > size)
               || decide (rd32le d 10 < 14 + rd32le d 14) || decide (rd32le d 10 > size))
            then 1 else 0) = 0
        rw [decide_eq_true_eq.mpr hB55]
        simp
      have hst3 : ExS Gen.prog s2 (.seq (.ite (.lor (.lor (.lor A B) C) D)
          (.ret (some (.const (.int ⟨32, true⟩ 0)))) .skip)
          (.ret (some (.const (.int ⟨32, true⟩ 1))))) (.ret (some (.int i32 0))) s2 :=
        ExS.seq_ret hite
      refine ⟨s2, ?_⟩
      rw [hbv]
      exact ExS.seq hset1 (ExS.seq hset2 hst3)
    · by_cases hC66 : rd32le d 10 < 14 + rd32le d 14
      · -- C true: A false, B false, C true
        have tA : truthy (boolVal (decide (rd32le d 14 < 40))) = .ok false := by
          rw [truthy_boolVal, decide_eq_false_iff_not.mpr hA34]
        have hCe : EvE Gen.prog s2 C (boolVal true) := by
          rw [decide_eq_true_eq.mpr hC66] at hC; exact hC
        have hBe : EvE Gen.prog s2 B (boolVal false) := by
          rw [decide_eq_false_iff_not.mpr hB55] at hB; exact hB
        have ei : EvE Gen.prog s2 (.lor A B) (boolVal false) := EvE.lor_false hA tA hBe truthy_false
        have ei2 : EvE Gen.prog s2 (.lor (.lor A B) C) (boolVal true) :=
          EvE.lor_false ei (by rw [truthy_boolVal]) hCe truthy_true
        have ei3 : EvE Gen.prog s2 (.lor (.lor (.lor A B) C) D) (boolVal true) :=
          EvE.lor_true ei2 truthy_true
        have hite : ExS Gen.prog s2 (.ite (.lor (.lor (.lor A B) C) D)
            (.ret (some (.const (.int ⟨32, true⟩ 0)))) .skip) (.ret (some (.int i32 0))) s2 :=
          ExS.ite ei3 truthy_true (ExS.ret (EvE.const _))
        have hbv : (if layoutOk size d then 1 else 0) = 0 := by
          show (if !(decide (rd32le d 14 < 40) || decide (14 + rd32le d 14 > size)
                 || decide (rd32le d 10 < 14 + rd32le d 14) || decide (rd32le d 10 > size))
              then 1 else 0) = 0
          rw [decide_eq_true_eq.mpr hC66]
          simp
        have hst3 : ExS Gen.prog s2 (.seq (.ite (.lor (.lor (.lor A B) C) D)
            (.ret (some (.const (.int ⟨32, true⟩ 0)))) .skip)
            (.ret (some (.const (.int ⟨32, true⟩ 1))))) (.ret (some (.int i32 0))) s2 :=
          ExS.seq_ret hite
        refine ⟨s2, ?_⟩
        rw [hbv]
        exact ExS.seq hset1 (ExS.seq hset2 hst3)
      · by_cases hD77 : rd32le d 10 > size
        · -- D true: only A..C false; cond true via D
          have tA : truthy (boolVal (decide (rd32le d 14 < 40))) = .ok false := by
            rw [truthy_boolVal, decide_eq_false_iff_not.mpr hA34]
          have tB : truthy (boolVal (decide (14 + rd32le d 14 > size))) = .ok false := by
            rw [truthy_boolVal, decide_eq_false_iff_not.mpr hB55]
          have hBe : EvE Gen.prog s2 B (boolVal false) := by
            rw [decide_eq_false_iff_not.mpr hB55] at hB; exact hB
          have hCe : EvE Gen.prog s2 C (boolVal false) := by
            rw [decide_eq_false_iff_not.mpr hC66] at hC; exact hC
          have hDe : EvE Gen.prog s2 D (boolVal true) := by
            rw [decide_eq_true_eq.mpr hD77] at hD; exact hD
          have ei : EvE Gen.prog s2 (.lor A B) (boolVal false) := EvE.lor_false hA tA hBe truthy_false
          have ei2 : EvE Gen.prog s2 (.lor (.lor A B) C) (boolVal false) :=
            EvE.lor_false ei (by rw [truthy_boolVal]) hCe truthy_false
          have ei3 : EvE Gen.prog s2 (.lor (.lor (.lor A B) C) D) (boolVal true) :=
            EvE.lor_false ei2 (by rw [truthy_boolVal]) hDe truthy_true
          have hite : ExS Gen.prog s2 (.ite (.lor (.lor (.lor A B) C) D)
              (.ret (some (.const (.int ⟨32, true⟩ 0)))) .skip) (.ret (some (.int i32 0))) s2 :=
            ExS.ite ei3 truthy_true (ExS.ret (EvE.const _))
          have hbv : (if layoutOk size d then 1 else 0) = 0 := by
            show (if !(decide (rd32le d 14 < 40) || decide (14 + rd32le d 14 > size)
                   || decide (rd32le d 10 < 14 + rd32le d 14) || decide (rd32le d 10 > size))
                then 1 else 0) = 0
            rw [decide_eq_true_eq.mpr hD77]
            simp
          have hst3 : ExS Gen.prog s2 (.seq (.ite (.lor (.lor (.lor A B) C) D)
              (.ret (some (.const (.int ⟨32, true⟩ 0)))) .skip)
              (.ret (some (.const (.int ⟨32, true⟩ 1))))) (.ret (some (.int i32 0))) s2 :=
            ExS.seq_ret hite
          refine ⟨s2, ?_⟩
          rw [hbv]
          exact ExS.seq hset1 (ExS.seq hset2 hst3)
        · -- all false: cond false; skip; fall through to `ret 1`
          have tA : truthy (boolVal (decide (rd32le d 14 < 40))) = .ok false := by
            rw [truthy_boolVal, decide_eq_false_iff_not.mpr hA34]
          have hBe : EvE Gen.prog s2 B (boolVal false) := by
            rw [decide_eq_false_iff_not.mpr hB55] at hB; exact hB
          have hCe : EvE Gen.prog s2 C (boolVal false) := by
            rw [decide_eq_false_iff_not.mpr hC66] at hC; exact hC
          have hDe : EvE Gen.prog s2 D (boolVal false) := by
            rw [decide_eq_false_iff_not.mpr hD77] at hD; exact hD
          have ei : EvE Gen.prog s2 (.lor A B) (boolVal false) := EvE.lor_false hA tA hBe truthy_false
          have ei2 : EvE Gen.prog s2 (.lor (.lor A B) C) (boolVal false) :=
            EvE.lor_false ei (by rw [truthy_boolVal]) hCe truthy_false
          have ei3 : EvE Gen.prog s2 (.lor (.lor (.lor A B) C) D) (boolVal false) :=
            EvE.lor_false ei2 (by rw [truthy_boolVal]) hDe truthy_false
          have hite : ExS Gen.prog s2 (.ite (.lor (.lor (.lor A B) C) D)
              (.ret (some (.const (.int ⟨32, true⟩ 0)))) .skip) .normal s2 :=
            ExS.ite ei3 truthy_false ExS.skip
          have hbv : (if layoutOk size d then 1 else 0) = 1 := by
            show (if !(decide (rd32le d 14 < 40) || decide (14 + rd32le d 14 > size)
                   || decide (rd32le d 10 < 14 + rd32le d 14) || decide (rd32le d 10 > size))
                then 1 else 0) = 1
            rw [decide_eq_false_iff_not.mpr hA34, decide_eq_false_iff_not.mpr hB55,
              decide_eq_false_iff_not.mpr hC66, decide_eq_false_iff_not.mpr hD77]
            simp
          have hst3 : ExS Gen.prog s2 (.seq (.ite (.lor (.lor (.lor A B) C) D)
              (.ret (some (.const (.int ⟨32, true⟩ 0)))) .skip)
              (.ret (some (.const (.int ⟨32, true⟩ 1))))) (.ret (some (.int i32 1))) s2 :=
            ExS.seq hite (ExS.ret (EvE.const _))
          refine ⟨s2, ?_⟩
          rw [hbv]
          exact ExS.seq hset1 (ExS.seq hset2 hst3)

/-! ## `ni_bmp_mul_fits` -/

/-- `ni_bmp_mul_fits` returns 1 iff `a = 0` or `b <= SIZE_MAX / a`. -/
theorem ni_bmp_mul_fits_exs (m : Mem) (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (ro : Bool) :
    ∃ s', ExS Gen.prog ⟨frameLocals [0, 1] [Val.int u64 a, Val.int u64 b], m, ro⟩
      Gen.ni_bmp_mul_fits.body
      (.ret (some (.int i32 (if (a = 0 ∨ b ≤ (18446744073709551615) / a) then 1 else 0)))) s' := by
  let s : State := ⟨frameLocals [0, 1] [Val.int u64 a, Val.int u64 b], m, ro⟩
  have hv0 : EvE Gen.prog s (.var 0) (.int u64 a) := EvE.var rfl
  have hv1 : EvE Gen.prog s (.var 1) (.int u64 b) := EvE.var rfl
  have hc0 : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))) (.int u64 0) :=
    EvE.cast (EvE.const (v := (.int ⟨32, false⟩ 0))) rfl
  have hEQ : EvE Gen.prog s
      (.bin .eq (some ⟨64, false⟩) (.var 0) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
      (boolVal (decide (a = 0))) :=
    EvE.bin hv0 hc0 (bin_u64_eq a 0)
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  classical
  by_cases hazero : a = 0
  · -- short-circuit true
    have hEQ' : EvE Gen.prog s
        (.bin .eq (some ⟨64, false⟩) (.var 0) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
        (boolVal true) := by
      rw [decide_eq_true_eq.mpr hazero] at hEQ; exact hEQ
    have ei : EvE Gen.prog s (.lor (.bin .eq (some ⟨64, false⟩) (.var 0) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) (.bin .le (some ⟨64, false⟩) (.var 1) (.bin .div (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 0)))) (boolVal true) :=
      EvE.lor_true hEQ' truthy_true
    have hbv : (if (a = 0 ∨ b ≤ (18446744073709551615) / a) then 1 else 0) = 1 := by
      simp [hazero]
    refine ⟨s, ?_⟩
    rw [hbv]
    exact ExS.ret ei
  · -- a ≠ 0; check b ≤ (2^64 - 1) / a
    have hEQ' : EvE Gen.prog s
        (.bin .eq (some ⟨64, false⟩) (.var 0) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
        (boolVal false) := by
      rw [decide_eq_false_iff_not.mpr hazero] at hEQ; exact hEQ
    have hdiv : EvE Gen.prog s
        (.bin .div (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 0))
        (.int u64 ((18446744073709551615) / a)) :=
      EvE.bin (EvE.const (v := (.int ⟨64, false⟩ 18446744073709551615))) hv0
        (bin_u64_div (18446744073709551615) a (by omega))
    have hLE : EvE Gen.prog s
        (.bin .le (some ⟨64, false⟩) (.var 1)
          (.bin .div (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 0)))
        (boolVal (decide (b ≤ (18446744073709551615) / a))) :=
      EvE.bin hv1 hdiv (bin_u64_le b ((18446744073709551615) / a))
    classical
    by_cases hfits : b ≤ (18446744073709551615) / a
    · have hLE' : EvE Gen.prog s
          (.bin .le (some ⟨64, false⟩) (.var 1)
            (.bin .div (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 0)))
          (boolVal true) := by
        rw [decide_eq_true_eq.mpr hfits] at hLE; exact hLE
      have ei : EvE Gen.prog s (.lor (.bin .eq (some ⟨64, false⟩) (.var 0) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) (.bin .le (some ⟨64, false⟩) (.var 1) (.bin .div (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 0)))) (boolVal true) :=
        EvE.lor_false hEQ' truthy_false hLE' truthy_true
      have hbv : (if (a = 0 ∨ b ≤ (18446744073709551615) / a) then 1 else 0) = 1 := by
        simp [hfits]
      refine ⟨s, ?_⟩
      rw [hbv]
      exact ExS.ret ei
    · have hLE' : EvE Gen.prog s
          (.bin .le (some ⟨64, false⟩) (.var 1)
            (.bin .div (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 0)))
          (boolVal false) := by
        rw [decide_eq_false_iff_not.mpr hfits] at hLE; exact hLE
      have ei : EvE Gen.prog s (.lor (.bin .eq (some ⟨64, false⟩) (.var 0) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) (.bin .le (some ⟨64, false⟩) (.var 1) (.bin .div (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 0)))) (boolVal false) :=
        EvE.lor_false hEQ' truthy_false hLE' truthy_false
      have hbv : (if (a = 0 ∨ b ≤ (18446744073709551615) / a) then 1 else 0) = 0 := by
        simp [hazero, hfits]
      refine ⟨s, ?_⟩
      rw [hbv]
      exact ExS.ret ei

/-- `ni_bmp_geometry` returns `bmpGeometryCode d`. -/
theorem ni_bmp_geometry_exs (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hd : 34 ≤ d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : m 3 = some obl) (h48 : obl.length = 48) (ro : Bool)
    (hro : ro = false) :
    ∃ s', ExS Gen.prog ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩
      Gen.ni_bmp_geometry.body
      (.ret (some (.int ⟨32, true⟩ (bmpGeometryCode d)))) s' ∧
    (bmpGeometryCode d = 0 → s'.mem 3 = some (geomOutBlock obl d)) ∧
    (bmpGeometryCode d = 0 → ∀ j, j ≠ 3 → s'.mem j = m j) := by
  have h34 : 34 ≤ d.length := hd
  let s5 : State :=
    { locals := ((frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0]).upd 3 (.int ⟨32, true⟩ (rd32le d 18))
                |>.upd 4 (.int ⟨32, true⟩ (rd32le d 22))
                |>.upd 5 (.int ⟨16, false⟩ (rd16le d 26))
                |>.upd 6 (.int ⟨16, false⟩ (rd16le d 28))
                |>.upd 7 (.int ⟨32, false⟩ (rd32le d 30))),
      mem := m, ro := ro }
  have hl0 : frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0] 0 = some (.ptr bd 0) := rfl
  let s4a : State := { locals := ((frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0]).upd 3 (.int ⟨32, true⟩ (rd32le d 18))), mem := m, ro := ro }
  have hw3 : ExS Gen.prog ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩
      (.call (some 3) 2 [(.index (.var 0) (.const (.int ⟨32, true⟩ 18)) 1)]) .normal s4a :=
    ExS.call_dst (EvArgs.cons (ev_ptr_const (s := ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩)
        (d := d) (k := 18) hm hl0 (by omega) (by omega)) EvArgs.nil)
      (show Gen.prog 2 = some Gen.ni_read_i32le from rfl)
      (show Gen.ni_read_i32le.params.length = 1 from rfl)
      (ni_read_i32le_exs m bd d hm 18 (by omega) hlen ro)
  have hl1 : s4a.locals 0 = some (.ptr bd 0) := rfl
  let s4b : State := { locals := s4a.locals.upd 4 (.int ⟨32, true⟩ (rd32le d 22)), mem := m, ro := ro }
  have hl2 : s4b.locals 0 = some (.ptr bd 0) := rfl
  have hw4 : ExS Gen.prog s4a
      (.call (some 4) 2 [(.index (.var 0) (.const (.int ⟨32, true⟩ 22)) 1)]) .normal s4b :=
    ExS.call_dst (EvArgs.cons (ev_ptr_const (s := s4a) (d := d) (k := 22) hm hl1 (by omega) (by omega)) EvArgs.nil)
      (show Gen.prog 2 = some Gen.ni_read_i32le from rfl)
      (show Gen.ni_read_i32le.params.length = 1 from rfl)
      (ni_read_i32le_exs m bd d hm 22 (by omega) hlen ro)
  let s4c : State := { locals := s4b.locals.upd 5 (.int ⟨16, false⟩ (rd16le d 26)), mem := m, ro := ro }
  have hl3 : s4c.locals 0 = some (.ptr bd 0) := rfl
  have hw5 : ExS Gen.prog s4b
      (.call (some 5) 0 [(.index (.var 0) (.const (.int ⟨32, true⟩ 26)) 1)]) .normal s4c :=
    ExS.call_dst (EvArgs.cons (ev_ptr_const (s := s4b) (d := d) (k := 26) hm hl2 (by omega) (by omega)) EvArgs.nil)
      (show Gen.prog 0 = some Gen.ni_read_u16le from rfl)
      (show Gen.ni_read_u16le.params.length = 1 from rfl)
      (ni_read_u16le_exs m bd d hm 26 (by omega) hlen ro)
  let s4d : State := { locals := s4c.locals.upd 6 (.int ⟨16, false⟩ (rd16le d 28)), mem := m, ro := ro }
  have hl4 : s4d.locals 0 = some (.ptr bd 0) := rfl
  have hw6 : ExS Gen.prog s4c
      (.call (some 6) 0 [(.index (.var 0) (.const (.int ⟨32, true⟩ 28)) 1)]) .normal s4d :=
    ExS.call_dst (EvArgs.cons (ev_ptr_const (s := s4c) (d := d) (k := 28) hm hl3 (by omega) (by omega)) EvArgs.nil)
      (show Gen.prog 0 = some Gen.ni_read_u16le from rfl)
      (show Gen.ni_read_u16le.params.length = 1 from rfl)
      (ni_read_u16le_exs m bd d hm 28 (by omega) hlen ro)
  have hw7 : ExS Gen.prog s4d
      (.call (some 7) 1 [(.index (.var 0) (.const (.int ⟨32, true⟩ 30)) 1)]) .normal s5 :=
    ExS.call_dst (EvArgs.cons (ev_ptr_const (s := s4d) (d := d) (k := 30) hm hl4 (by omega) (by omega)) EvArgs.nil)
      (show Gen.prog 1 = some Gen.ni_read_u32le from rfl)
      (show Gen.ni_read_u32le.params.length = 1 from rfl)
      (ni_read_u32le_exs m bd d hm 30 (by omega) hlen ro)
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  have hu64c2 : EvE Gen.prog s5 (.var 2) (.ptr 3 0) := EvE.var rfl
  have hu64c1 : EvE Gen.prog s5 (.var 1) (.int ⟨64, false⟩ size) := EvE.var rfl
  have hu64c0 : EvE Gen.prog s5 (.var 0) (.ptr bd 0) := EvE.var rfl
  have hv3 : EvE Gen.prog s5 (.var 3) (.int ⟨32, true⟩ (rd32le d 18)) := EvE.var rfl
  have hv4 : EvE Gen.prog s5 (.var 4) (.int ⟨32, true⟩ (rd32le d 22)) := EvE.var rfl
  have hv5 : EvE Gen.prog s5 (.var 5) (.int ⟨16, false⟩ (rd16le d 26)) := EvE.var rfl
  have hv6 : EvE Gen.prog s5 (.var 6) (.int ⟨16, false⟩ (rd16le d 28)) := EvE.var rfl
  have hv7 : EvE Gen.prog s5 (.var 7) (.int ⟨32, false⟩ (rd32le d 30)) := EvE.var rfl
  -- Condition A = signed width <= 0
  have hA : EvE Gen.prog s5
      (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
      (boolVal (decide (IntTy.toInt ⟨32, true⟩ (rd32le d 18) ≤ 0))) :=
    EvE.bin hv3 (EvE.const _) (bin_i32_le0 _)
  by_cases hA34 : IntTy.toInt ⟨32, true⟩ (rd32le d 18) ≤ 0
  · -- reject 3: width <= 0
    have eA : EvE Gen.prog s5
        (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0))) (boolVal true) := by
      rw [decide_eq_true_eq.mpr hA34] at hA; exact hA
    have ei : EvE Gen.prog s5
        (.lor (.lor (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
                    (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0))))
               (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5)) (.const (.int ⟨32, false⟩ 1))))
        (boolVal true) :=
      EvE.lor_true (EvE.lor_true eA truthy_true) truthy_true
    have hbv : bmpGeometryCode d = 3 := by
      have e18 : IntTy.toInt ⟨32, true⟩ (rd32le d 18) = NANO.toInt32 (rd32le d 18) :=
        (NANO.C.toInt32_eq (rd32le d 18) (rd32_lt d 18)).symm
      have hle : NANO.toInt32 (rd32le d 18) ≤ 0 := by
        have h2 := hA34
        rw [e18] at h2
        exact h2
      simp [bmpGeometryCode, hle]
    have hite : ExS Gen.prog s5
        (.ite (.lor (.lor (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
                    (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0))))
               (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5)) (.const (.int ⟨32, false⟩ 1))))
          (.ret (some (.const (.int ⟨32, true⟩ 3)))) .skip)
        (.ret (some (.int ⟨32, true⟩ 3))) s5 :=
      ExS.ite ei truthy_true (ExS.ret (EvE.const _))
    refine ⟨s5, ?_, fun hb => by rw [hbv] at hb; exact absurd hb (by decide), fun _ _ _ => rfl⟩
    rw [hbv]
    exact ExS.seq hw3 (ExS.seq hw4 (ExS.seq hw5 (ExS.seq hw6 (ExS.seq hw7 (ExS.seq_ret hite)))))
  · by_cases hB66 : IntTy.toInt ⟨32, true⟩ (rd32le d 22) = 0
    · -- reject 3: height == 0
      have eA : EvE Gen.prog s5
          (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0))) (boolVal false) := by
        have hAval : EvE Gen.prog s5 (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
            (boolVal (decide (IntTy.toInt ⟨32, true⟩ (rd32le d 18) ≤ 0))) :=
          EvE.bin hv3 (EvE.const _) (bin_i32_le0 _)
        have hA34not : ¬ (IntTy.toInt ⟨32, true⟩ (rd32le d 18) ≤ 0) := by omega
        rw [decide_eq_false_iff_not.mpr hA34not] at hAval; exact hAval
      have eB : EvE Gen.prog s5
          (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0))) (boolVal true) := by
        have hEQ : EvE Gen.prog s5 (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0)))
            (boolVal (decide (IntTy.toInt ⟨32, true⟩ (rd32le d 22) = 0))) :=
          EvE.bin hv4 (EvE.const _) (bin_i32_eq0 _)
        rw [decide_eq_true_eq.mpr hB66] at hEQ; exact hEQ
      have tA : truthy (boolVal false) = .ok false := truthy_false
      have tB : truthy (boolVal (decide (IntTy.toInt ⟨32, true⟩ (rd32le d 22) = 0))) = .ok true := by
        rw [truthy_boolVal, decide_eq_true_eq.mpr hB66]
      have eAB : EvE Gen.prog s5
          (.lor (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
                (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0))))
          (boolVal true) :=
        EvE.lor_false eA tA eB truthy_true
      have ei : EvE Gen.prog s5
          (.lor (.lor (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
                      (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0))))
                 (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5)) (.const (.int ⟨32, false⟩ 1))))
          (boolVal true) :=
        EvE.lor_true eAB truthy_true
      have hite : ExS Gen.prog s5
          (.ite (.lor (.lor (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
                      (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0))))
                 (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5)) (.const (.int ⟨32, false⟩ 1))))
            (.ret (some (.const (.int ⟨32, true⟩ 3)))) .skip)
          (.ret (some (.int ⟨32, true⟩ 3))) s5 :=
        ExS.ite ei truthy_true (ExS.ret (EvE.const _))
      have hbv : bmpGeometryCode d = 3 := by
        have e18 : IntTy.toInt ⟨32, true⟩ (rd32le d 18) = NANO.toInt32 (rd32le d 18) :=
          (NANO.C.toInt32_eq (rd32le d 18) (rd32_lt d 18)).symm
        have e22 : IntTy.toInt ⟨32, true⟩ (rd32le d 22) = NANO.toInt32 (rd32le d 22) :=
          (NANO.C.toInt32_eq (rd32le d 22) (rd32_lt d 22)).symm
        have hgt : NANO.toInt32 (rd32le d 18) > 0 := by
          have h2 := hA34
          rw [e18] at h2
          omega
        have hh0 : NANO.toInt32 (rd32le d 22) = 0 := by
          have h2 := hB66
          rw [e22] at h2
          exact h2
        simp [bmpGeometryCode, hgt, hh0]
      refine ⟨s5, ?_, fun hb => by rw [hbv] at hb; exact absurd hb (by decide), fun _ _ _ => rfl⟩
      rw [hbv]
      exact ExS.seq hw3 (ExS.seq hw4 (ExS.seq hw5 (ExS.seq hw6 (ExS.seq hw7 (ExS.seq_ret hite)))))
    · -- planes ≠ 1 → return 3 (short-circuit); else continue
      by_cases hC66 : rd16le d 26 ≠ 1
      · -- planes ≠ 1: return 3
        have eC : EvE Gen.prog s5
            (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5)) (.const (.int ⟨32, false⟩ 1)))
            (boolVal true) := by
          have hAval : EvE Gen.prog s5
              (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5)) (.const (.int ⟨32, false⟩ 1)))
              (boolVal (decide (rd16le d 26 ≠ 1))) :=
            EvE.bin (EvE.cast hv5 (u16_u32_cast (rd16le d 26) (rd16le_lt d 26))) (EvE.const _)
              (bin_u32_ne _ _)
          rw [decide_eq_true_eq.mpr hC66] at hAval; exact hAval
        have eA : EvE Gen.prog s5
            (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0))) (boolVal false) := by
          have hAval : EvE Gen.prog s5 (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
              (boolVal (decide (IntTy.toInt ⟨32, true⟩ (rd32le d 18) ≤ 0))) :=
            EvE.bin hv3 (EvE.const _) (bin_i32_le0 _)
          have hA34not : ¬ (IntTy.toInt ⟨32, true⟩ (rd32le d 18) ≤ 0) := by omega
          rw [decide_eq_false_iff_not.mpr hA34not] at hAval; exact hAval
        have eB : EvE Gen.prog s5
            (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0))) (boolVal false) := by
          have hAval : EvE Gen.prog s5 (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0)))
              (boolVal (decide (IntTy.toInt ⟨32, true⟩ (rd32le d 22) = 0))) :=
            EvE.bin hv4 (EvE.const _) (bin_i32_eq0 _)
          rw [decide_eq_false_iff_not.mpr hB66] at hAval; exact hAval
        have tA : truthy (boolVal false) = .ok false := truthy_false
        have tB : truthy (boolVal false) = .ok false := truthy_false
        have tC : truthy (boolVal true) = .ok true := truthy_true
        have eAB : EvE Gen.prog s5
            (.lor (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
                  (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0))))
            (boolVal false) :=
          EvE.lor_false eA tA eB tB
        have ei : EvE Gen.prog s5
            (.lor (.lor (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
                        (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0))))
                   (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5)) (.const (.int ⟨32, false⟩ 1))))
            (boolVal true) :=
          EvE.lor_false eAB tB eC tC
        have hite : ExS Gen.prog s5
            (.ite (.lor (.lor (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
                        (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0))))
                   (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5)) (.const (.int ⟨32, false⟩ 1))))
              (.ret (some (.const (.int ⟨32, true⟩ 3)))) .skip)
            (.ret (some (.int ⟨32, true⟩ 3))) s5 :=
          ExS.ite ei truthy_true (ExS.ret (EvE.const _))
        have hbv : bmpGeometryCode d = 3 := by
          have e18 : IntTy.toInt ⟨32, true⟩ (rd32le d 18) = NANO.toInt32 (rd32le d 18) :=
            (NANO.C.toInt32_eq (rd32le d 18) (rd32_lt d 18)).symm
          have e22 : IntTy.toInt ⟨32, true⟩ (rd32le d 22) = NANO.toInt32 (rd32le d 22) :=
            (NANO.C.toInt32_eq (rd32le d 22) (rd32_lt d 22)).symm
          have hgt : NANO.toInt32 (rd32le d 18) > 0 := by
            have h2 := hA34
            rw [e18] at h2
            omega
          have hh0 : NANO.toInt32 (rd32le d 22) ≠ 0 := by
            have h2 := hB66
            rw [e22] at h2
            omega
          simp [bmpGeometryCode, hgt, hh0, hC66]
        refine ⟨s5, ?_, fun hb => by rw [hbv] at hb; exact absurd hb (by decide), fun _ _ _ => rfl⟩
        rw [hbv]
        exact ExS.seq hw3 (ExS.seq hw4 (ExS.seq hw5 (ExS.seq hw6 (ExS.seq hw7 (ExS.seq_ret hite)))))
      · -- planes == 1: continue with body
        have hPl : rd16le d 26 = 1 := by simp only [ne_eq] at hC66; omega
        have e18 : IntTy.toInt ⟨32, true⟩ (rd32le d 18) = NANO.toInt32 (rd32le d 18) :=
          (NANO.C.toInt32_eq (rd32le d 18) (rd32_lt d 18)).symm
        have hA34p : IntTy.toInt ⟨32, true⟩ (rd32le d 18) > 0 := by
          have h2 := hA34
          omega
        have hPl : rd16le d 26 = 1 := by simp only [ne_eq] at hC66; omega
        have e18 : IntTy.toInt ⟨32, true⟩ (rd32le d 18) = NANO.toInt32 (rd32le d 18) :=
          (NANO.C.toInt32_eq (rd32le d 18) (rd32_lt d 18)).symm
        have hA34p : IntTy.toInt ⟨32, true⟩ (rd32le d 18) > 0 := by
          have h2 := hA34
          omega
        by_cases hPos : NANO.toInt32 (rd32le d 22) ≥ 0
        · obtain ⟨s', ex', hblk, hUnt⟩ :=
            ni_bmp_geometry_exs_pos m bd d hm size hs hd hlen obl hob h48 ro hro hA34p hB66 hPl hPos
          refine ⟨s', ex', fun hh => ?_, fun hh => hUnt hh⟩
          rw [geomOutBlock_pos obl d hPos]
          exact hblk hh
        · by_cases hInMin : NANO.toInt32 (rd32le d 22) = -2147483648
          · obtain ⟨s', ex', hblk, hUnt⟩ :=
              ni_bmp_geometry_exs_neg_intmin m bd d hm size hs hd hlen obl hob h48 ro hro hA34p hB66 hPl (by
              have hNeg : NANO.toInt32 (rd32le d 22) < 0 := by omega
              exact hNeg) hInMin
            refine ⟨s', ex', fun hh => ?_, fun hh => hUnt hh⟩
            have hNeg : (NANO.toInt32 (rd32le d 22) : Int) < 0 := by
              rw [hInMin]; decide
            rw [geomOutBlock_intmin obl d hNeg hInMin]
            exact hblk hh
          · obtain ⟨s', ex', hblk, hUnt⟩ :=
              ni_bmp_geometry_exs_neg_normal m bd d hm size hs hd hlen obl hob h48 ro hro hA34p hB66 hPl (by
              have hNeg : NANO.toInt32 (rd32le d 22) < 0 := by omega
              exact hNeg) hInMin
            refine ⟨s', ex', fun hh => ?_, fun hh => hUnt hh⟩
            have hNeg : (NANO.toInt32 (rd32le d 22) : Int) < 0 := by omega
            rw [geomOutBlock_neg_normal obl d hNeg (by exact hInMin)]
            exact hblk hh

end NANO.C.Proofs
