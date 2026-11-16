/-
  The NEG normal branch of ni_bmp_geometry (case
  `height_i < 0` and `height_i != INT32_MIN`).
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Lemmas
import NANO.Spec
import NANO.Bmp
import NANO.C.Proofs.Core
import NANO.C.Proofs.NiGeometryTail

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 400000

namespace NANO.C.Proofs
open NANO NANO.C

/-- NEG path with `height_i < 0`, `height_i != INT32_MIN`. -/
theorem ni_bmp_geometry_exs_neg_normal (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hd : 34 ≤ d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : m 3 = some obl) (h48 : obl.length = 48) (ro : Bool)
    (hro : ro = false)
    (hA34 : IntTy.toInt ⟨32, true⟩ (rd32le d 18) > 0)
    (hB66 : IntTy.toInt ⟨32, true⟩ (rd32le d 22) ≠ 0)
    (hPl : rd16le d 26 = 1)
    (hNeg : NANO.toInt32 (rd32le d 22) < 0)
    (hInMin : NANO.toInt32 (rd32le d 22) ≠ -2147483648) :
    ∃ s', ExS Gen.prog ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩
      Gen.ni_bmp_geometry.body
      (.ret (some (.int ⟨32, true⟩ (bmpGeometryCode d)))) s' ∧
    (bmpGeometryCode d = 0 → s'.mem 3 =
      some (bmpTailBlock obl (rd32le d 18) (IntTy.wrap ⟨32, true⟩ (-(IntTy.toInt ⟨32, true⟩ (rd32le d 22))))
        (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3) 1)) := by
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
  have e18 : IntTy.toInt ⟨32, true⟩ (rd32le d 18) = NANO.toInt32 (rd32le d 18) :=
    (NANO.C.toInt32_eq (rd32le d 18) (rd32_lt d 18)).symm
  have e22 : IntTy.toInt ⟨32, true⟩ (rd32le d 22) = NANO.toInt32 (rd32le d 22) :=
    (NANO.C.toInt32_eq (rd32le d 22) (rd32_lt d 22)).symm
  have hgt : NANO.toInt32 (rd32le d 18) > 0 := by
    have h2 := hA34; rw [e18] at h2; omega
  have hh0 : NANO.toInt32 (rd32le d 22) ≠ 0 := by
    have h2 := hB66; rw [e22] at h2; omega
  have eA : EvE Gen.prog s5
      (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
      (boolVal false) := by
    have hAval : EvE Gen.prog s5 (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
        (boolVal (decide (IntTy.toInt ⟨32, true⟩ (rd32le d 18) ≤ 0))) :=
      EvE.bin hv3 (EvE.const _) (bin_i32_le0 _)
    have hA34not : ¬ (IntTy.toInt ⟨32, true⟩ (rd32le d 18) ≤ 0) := by omega
    rw [decide_eq_false_iff_not.mpr hA34not] at hAval; exact hAval
  have eB : EvE Gen.prog s5
      (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0)))
      (boolVal false) := by
    have hAval : EvE Gen.prog s5 (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0)))
        (boolVal (decide (IntTy.toInt ⟨32, true⟩ (rd32le d 22) = 0))) :=
      EvE.bin hv4 (EvE.const _) (bin_i32_eq0 _)
    rw [decide_eq_false_iff_not.mpr hB66] at hAval; exact hAval
  have eC : EvE Gen.prog s5
      (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5)) (.const (.int ⟨32, false⟩ 1)))
      (boolVal false) := by
    have hAval : EvE Gen.prog s5
        (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5)) (.const (.int ⟨32, false⟩ 1)))
        (boolVal (decide (rd16le d 26 ≠ 1))) :=
      EvE.bin (EvE.cast hv5 (u16_u32_cast (rd16le d 26) (rd16le_lt d 26))) (EvE.const _)
        (bin_u32_ne _ _)
    rw [hPl] at hAval
    simpa using hAval
  have tA : truthy (boolVal false) = .ok false := truthy_false
  have tB : truthy (boolVal false) = .ok false := truthy_false
  have tC : truthy (boolVal false) = .ok false := truthy_false
  have eAB : EvE Gen.prog s5
      (.lor (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
            (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0))))
      (boolVal false) :=
    EvE.lor_false eA tA eB tB
  have ei : EvE Gen.prog s5
      (.lor (.lor (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
                  (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0))))
             (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5)) (.const (.int ⟨32, false⟩ 1))))
      (boolVal false) :=
    EvE.lor_false eAB tB eC tC
  have hR_skip : ExS Gen.prog s5
    (.ite (.lor (.lor (.bin .le (some ⟨32, true⟩) (.var 3) (.const (.int ⟨32, true⟩ 0)))
                      (.bin .eq (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0))))
             (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5)) (.const (.int ⟨32, false⟩ 1))))
      (.ret (some (.const (.int ⟨32, true⟩ 3)))) .skip)
    .normal s5 :=
  ExS.ite ei tC ExS.skip
  have e22' : IntTy.toInt ⟨32, true⟩ (rd32le d 22) = NANO.toInt32 (rd32le d 22) :=
    (NANO.C.toInt32_eq (rd32le d 22) (rd32_lt d 22)).symm
  have hv4M : EvE Gen.prog s5 (.var 4) (.int ⟨32, true⟩ (rd32le d 22)) := hv4
  have hY2147483647 : evalUn .neg ⟨32, true⟩ (.int ⟨32, true⟩ 2147483647)
      = .ok (.int ⟨32, true⟩ 2147483649) := by
    simp [evalUn, intOf, arith, IntTy.toInt, IntTy.wrap, IntTy.modulus, IntTy.width, IntTy.signed,
      IntTy.inRange, IntTy.minVal, IntTy.maxVal]
  have hNegConst : EvE Gen.prog s5
      (.un .neg ⟨32, true⟩ (Expr.const (Val.int ⟨32, true⟩ 2147483647)))
      (.int ⟨32, true⟩ 2147483649) :=
    EvE.un (EvE.const _) hY2147483647
  have hSub786 : evalBin .sub (some ⟨32, true⟩)
      (.int ⟨32, true⟩ 2147483649) (.int ⟨32, true⟩ 1)
      = .ok (.int ⟨32, true⟩ 2147483648) := by
    simp only [evalBin, evalBinInt, binInt, intOf, IntTy.toInt, if_true]
    show arith ⟨32, true⟩ (-2147483647 - 1) = .ok (.int ⟨32, true⟩ 2147483648)
    rw [arith, if_pos rfl, if_pos (by decide)]
    simp [IntTy.wrap, IntTy.modulus]
  have hSubConst : EvE Gen.prog s5
      (.bin .sub (some ⟨32, true⟩)
        (.un .neg ⟨32, true⟩ (Expr.const (Val.int ⟨32, true⟩ 2147483647)))
        (Expr.const (Val.int ⟨32, true⟩ 1)))
      (.int ⟨32, true⟩ 2147483648) :=
    EvE.bin hNegConst (EvE.const _) hSub786
  have hEQconst : EvE Gen.prog s5
      (.bin .eq (some ⟨32, true⟩) (.var 4)
        (.bin .sub (some ⟨32, true⟩)
          (.un .neg ⟨32, true⟩ (Expr.const (Val.int ⟨32, true⟩ 2147483647)))
          (Expr.const (Val.int ⟨32, true⟩ 1))))
      (boolVal (decide (IntTy.toInt ⟨32, true⟩ (rd32le d 22) = IntTy.toInt ⟨32, true⟩ 2147483648))) :=
    EvE.bin hv4M hSubConst (bin_i32_eq (rd32le d 22) 2147483648)
  have eMI : EvE Gen.prog s5
      (.bin .eq (some ⟨32, true⟩) (.var 4)
        (.bin .sub (some ⟨32, true⟩)
          (.un .neg ⟨32, true⟩ (Expr.const (Val.int ⟨32, true⟩ 2147483647)))
          (Expr.const (Val.int ⟨32, true⟩ 1))))
      (boolVal false) := by
    rw [e22'] at hEQconst
    have hTwo31 : IntTy.toInt ⟨32, true⟩ 2147483648 = -2147483648 := by
      simp [IntTy.toInt, IntTy.modulus, IntTy.width, IntTy.signed]
    rw [hTwo31] at hEQconst
    rw [decide_eq_false_iff_not.mpr hInMin] at hEQconst
    exact hEQconst
  have hINTMINskip : ExS Gen.prog s5
      (.ite (.bin .eq (some ⟨32, true⟩) (.var 4)
        (.bin .sub (some ⟨32, true⟩)
          (.un .neg ⟨32, true⟩ (Expr.const (Val.int ⟨32, true⟩ 2147483647)))
          (Expr.const (Val.int ⟨32, true⟩ 1))))
        (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 4)))) .skip)
      .normal s5 :=
    ExS.ite eMI (truthy_boolVal false) ExS.skip
  have hSP11 : EvE Gen.prog s5
      (.cast ⟨8, false⟩ (Expr.const (Val.int ⟨32, false⟩ 1))) (.int ⟨8, false⟩ 1) :=
    EvE.cast (EvE.const _) rfl
  have hSet11 : ExS Gen.prog s5
      (.set 11 (.cast ⟨8, false⟩ (Expr.const (Val.int ⟨32, false⟩ 1))))
      .normal
      { s5 with locals := s5.locals.upd 11 (.int ⟨8, false⟩ 1) } :=
    ExS.set hSP11
  let s5A : State := { s5 with locals := s5.locals.upd 11 (.int ⟨8, false⟩ 1) }
  have hv4A : EvE Gen.prog s5A (.var 4) (.int ⟨32, true⟩ (rd32le d 22)) := EvE.var rfl
  have toInt32_eq_w : IntTy.toInt ⟨32, true⟩ (rd32le d 22) = NANO.toInt32 (rd32le d 22) :=
    (NANO.C.toInt32_eq (rd32le d 22) (rd32_lt d 22)).symm
  have htarget_ge : NANO.toInt32 (rd32le d 22) ≥ -2147483647 := by
    by_cases h1 : 2147483648 ≤ rd32le d 22
    · have ht : NANO.toInt32 (rd32le d 22) = (rd32le d 22 : Int) - 4294967296 := by
        show (if 2 ^ 31 ≤ rd32le d 22 then (rd32le d 22 : Int) - 2 ^ 32 else (rd32le d 22 : Int)) = _
        rw [if_pos (show 2 ^ 31 ≤ rd32le d 22 from h1)]
        rw [show (2 : Int) ^ 32 = 4294967296 from rfl]
      rw [ht]
      have hn : (rd32le d 22 : Int) - 4294967296 ≠ -2147483648 := by
        rw [ht] at hInMin
        exact hInMin
      omega
    · have ht : NANO.toInt32 (rd32le d 22) = (rd32le d 22 : Int) := by
        show (if 2 ^ 31 ≤ rd32le d 22 then (rd32le d 22 : Int) - 2 ^ 32 else (rd32le d 22 : Int)) = _
        rw [if_neg (show ¬ 2 ^ 31 ≤ rd32le d 22 from h1)]
      rw [ht]
      omega
  have htarget_le : NANO.toInt32 (rd32le d 22) ≤ -1 := by
    by_cases h1 : 2147483648 ≤ rd32le d 22
    · have ht : NANO.toInt32 (rd32le d 22) = (rd32le d 22 : Int) - 4294967296 := by
        show (if 2 ^ 31 ≤ rd32le d 22 then (rd32le d 22 : Int) - 2 ^ 32 else (rd32le d 22 : Int)) = _
        rw [if_pos (show 2 ^ 31 ≤ rd32le d 22 from h1)]
        rw [show (2 : Int) ^ 32 = 4294967296 from rfl]
      rw [ht]
      omega
    · have ht : NANO.toInt32 (rd32le d 22) = (rd32le d 22 : Int) := by
        show (if 2 ^ 31 ≤ rd32le d 22 then (rd32le d 22 : Int) - 2 ^ 32 else (rd32le d 22 : Int)) = _
        rw [if_neg (show ¬ 2 ^ 31 ≤ rd32le d 22 from h1)]
      rw [ht] at hNeg
      omega
  have hRangeNeg : IntTy.inRange ⟨32, true⟩ (-(IntTy.toInt ⟨32, true⟩ (rd32le d 22))) = true := by
    rw [toInt32_eq_w]
    have hTintGe : NANO.toInt32 (rd32le d 22) ≥ -2147483647 := htarget_ge
    have hTintLe : NANO.toInt32 (rd32le d 22) ≤ -1 := htarget_le
    have hminval : IntTy.minVal ⟨32, true⟩ = -2147483648 := rfl
    have hmaxval : IntTy.maxVal ⟨32, true⟩ = 2147483647 := rfl
    rw [IntTy.inRange, hminval, hmaxval]
    have hAnd : -2147483648 ≤ -(NANO.toInt32 (rd32le d 22)) ∧ -(NANO.toInt32 (rd32le d 22)) ≤ 2147483647 := by
      omega
    simp [hAnd]
  have hNegA : EvE Gen.prog s5A (.un .neg ⟨32, true⟩ (.var 4))
      (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (-(IntTy.toInt ⟨32, true⟩ (rd32le d 22))))) :=
    EvE.un hv4A (NANO.C.evalUnNegI32 (rd32le d 22) hRangeNeg)
  have hCast9 : EvE Gen.prog s5A
      (.cast ⟨32, false⟩ (.un .neg ⟨32, true⟩ (.var 4)))
      (.int ⟨32, false⟩ (IntTy.wrap ⟨32, true⟩ (-(IntTy.toInt ⟨32, true⟩ (rd32le d 22))))) := by
    have hlt : IntTy.wrap ⟨32, true⟩ (-(IntTy.toInt ⟨32, true⟩ (rd32le d 22))) < 4294967296 :=
      wrap_i32_lt _
    exact EvE.cast hNegA (cast_u32_i32 _ hlt)
  have hSet9 : ExS Gen.prog s5A
      (.set 9 (.cast ⟨32, false⟩ (.un .neg ⟨32, true⟩ (.var 4))))
      .normal
      { s5A with locals := s5A.locals.upd 9 (.int ⟨32, false⟩ (IntTy.wrap ⟨32, true⟩ (-(IntTy.toInt ⟨32, true⟩ (rd32le d 22))))) } :=
    ExS.set hCast9
  let s5B : State :=
    { s5A with locals := s5A.locals.upd 9 (.int ⟨32, false⟩ (IntTy.wrap ⟨32, true⟩ (-(IntTy.toInt ⟨32, true⟩ (rd32le d 22))))) }
  have hNegExec : ExS Gen.prog s5
      (.seq (.set 11 (.cast ⟨8, false⟩ (Expr.const (Val.int ⟨32, false⟩ 1))))
            (.set 9 (.cast ⟨32, false⟩ (.un .neg ⟨32, true⟩ (.var 4)))))
      .normal s5B :=
    ExS.seq hSet11 hSet9
  have hNegThen : ExS Gen.prog s5
      (.seq
        (.ite (.bin .eq (some ⟨32, true⟩) (.var 4)
          (.bin .sub (some ⟨32, true⟩)
            (.un .neg ⟨32, true⟩ (Expr.const (Val.int ⟨32, true⟩ 2147483647)))
            (Expr.const (Val.int ⟨32, true⟩ 1))))
          (.ret (some (Expr.const (Val.int ⟨32, true⟩ 4)))) .skip)
        (.seq (.set 11 (.cast ⟨8, false⟩ (Expr.const (Val.int ⟨32, false⟩ 1))))
              (.set 9 (.cast ⟨32, false⟩ (.un .neg ⟨32, true⟩ (.var 4))))))
      .normal s5B :=
    ExS.seq hINTMINskip hNegExec
  have eLT : EvE Gen.prog s5
      (.bin .lt (some ⟨32, true⟩) (.var 4) (Expr.const (Val.int ⟨32, true⟩ 0)))
      (boolVal true) := by
    have hAval : EvE Gen.prog s5
        (.bin .lt (some ⟨32, true⟩) (.var 4) (Expr.const (Val.int ⟨32, true⟩ 0)))
        (boolVal (decide (IntTy.toInt ⟨32, true⟩ (rd32le d 22) < 0))) :=
      EvE.bin hv4M (EvE.const _) (bin_i32_lt0 _)
    rw [e22'] at hAval
    rwa [decide_eq_true_eq.mpr hNeg] at hAval
  have hLTexec : ExS Gen.prog s5
      (.ite (.bin .lt (some ⟨32, true⟩) (.var 4) (Expr.const (Val.int ⟨32, true⟩ 0)))
        (.seq (.ite (.bin .eq (some ⟨32, true⟩) (.var 4)
          (.bin .sub (some ⟨32, true⟩)
            (.un .neg ⟨32, true⟩ (Expr.const (Val.int ⟨32, true⟩ 2147483647)))
            (Expr.const (Val.int ⟨32, true⟩ 1))))
            (.ret (some (Expr.const (Val.int ⟨32, true⟩ 4)))) .skip)
           (.seq (.set 11 (.cast ⟨8, false⟩ (Expr.const (Val.int ⟨32, false⟩ 1))))
                 (.set 9 (.cast ⟨32, false⟩ (.un .neg ⟨32, true⟩ (.var 4))))))
        (.seq (.set 11 (.cast ⟨8, false⟩ (Expr.const (Val.int ⟨32, false⟩ 0))))
              (.set 9 (.cast ⟨32, false⟩ (.var 4)))))
      .normal s5B :=
    ExS.ite eLT (truthy_boolVal true) hNegThen
  have hIntmin : NANO.toInt32 (rd32le d 22) ≠ -2147483648 := hInMin
  obtain ⟨s', code, hpost, hcode, hblk⟩ := tail_exs m bd d hm size hs hd hlen obl hob h48
    ro hro
    (IntTy.wrap ⟨32, true⟩ (-(IntTy.toInt ⟨32, true⟩ (rd32le d 22))))
    (wrap_i32_lt _)
    1 (by omega)
    hgt hh0 hPl hIntmin
  refine ⟨s', ?_, fun hh => hblk (hcode ▸ hh)⟩
  rw [← hcode]
  exact ExS.seq hw3 (ExS.seq hw4 (ExS.seq hw5 (ExS.seq hw6 (ExS.seq hw7 (ExS.seq hR_skip
    (ExS.seq hLTexec hpost))))))

end NANO.C.Proofs
