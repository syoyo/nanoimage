/-/
  The three `ni_bmp_geometry_exs_*` cases: POS `(height_i >= 0)`, INTMIN
  (`height_i == INT32_MIN`) and NEG-normal
  (`height_i < 0`, `height_i != INT32_MIN`).
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
set_option maxHeartbeats 40000

namespace NANO.C.Proofs
open NANO NANO.C

/-- Closed form of the five reader calls of `ni_bmp_geometry`: the resulting
    state has locals 3..7 set to the readers' outputs. -/
theorem ni_bmp_geometry_readers (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hlen : d.length < 2 ^ 64) (hd : 34 ≤ d.length) (ro : Bool) :
    ExS Gen.prog ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩
      (.seq (.call (some 3) 2 [(.index (.var 0) (.const (.int i32 18)) 1)])
      (.seq (.call (some 4) 2 [(.index (.var 0) (.const (.int i32 22)) 1)])
      (.seq (.call (some 5) 0 [(.index (.var 0) (.const (.int i32 26)) 1)])
      (.seq (.call (some 6) 0 [(.index (.var 0) (.const (.int i32 28)) 1)])
            (.call (some 7) 1 [(.index (.var 0) (.const (.int i32 30)) 1)])))))
      .normal
      { locals := ((frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0]).upd 3 (.int i32 (rd32le d 18))
                |>.upd 4 (.int i32 (rd32le d 22))
                |>.upd 5 (.int u16 (rd16le d 26))
                |>.upd 6 (.int u16 (rd16le d 28))
                |>.upd 7 (.int u32 (rd32le d 30))),
        mem := m, ro := ro } := by
  have hl0 : frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0] 0 = some (.ptr bd 0) := rfl
  have hw3 : ExS Gen.prog ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩
      (.call (some 3) 2 [(.index (.var 0) (.const (.int i32 18)) 1)]) .normal
      ⟨(frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0]).upd 3 (.int i32 (rd32le d 18)),
       m, ro⟩ :=
    ExS.call_dst (EvArgs.cons (ev_ptr_const (s := ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩)
        (d := d) (k := 18) hm hl0 (by omega) (by omega)) EvArgs.nil)
      (show Gen.prog 2 = some Gen.ni_read_i32le from rfl)
      (show Gen.ni_read_i32le.params.length = 1 from rfl)
      (ni_read_i32le_exs m bd d hm 18 (by omega) hlen ro)
  let s1 : State := { locals := (frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0]).upd 3 (.int i32 (rd32le d 18)),
                      mem := m, ro := ro }
  have hl1 : s1.locals 0 = some (.ptr bd 0) := rfl
  have hw4 : ExS Gen.prog s1
      (.call (some 4) 2 [(.index (.var 0) (.const (.int i32 22)) 1)]) .normal
      { locals := s1.locals.upd 4 (.int i32 (rd32le d 22)), mem := m, ro := ro } :=
    ExS.call_dst (EvArgs.cons (ev_ptr_const (s := s1) (d := d) (k := 22) hm hl1 (by omega) (by omega)) EvArgs.nil)
      (show Gen.prog 2 = some Gen.ni_read_i32le from rfl)
      (show Gen.ni_read_i32le.params.length = 1 from rfl)
      (ni_read_i32le_exs m bd d hm 22 (by omega) hlen ro)
  let s2 : State := { locals := s1.locals.upd 4 (.int i32 (rd32le d 22)), mem := m, ro := ro }
  have hl2 : s2.locals 0 = some (.ptr bd 0) := rfl
  have hw5 : ExS Gen.prog s2
      (.call (some 5) 0 [(.index (.var 0) (.const (.int i32 26)) 1)]) .normal
      { locals := s2.locals.upd 5 (.int u16 (rd16le d 26)), mem := m, ro := ro } :=
    ExS.call_dst (EvArgs.cons (ev_ptr_const (s := s2) (d := d) (k := 26) hm hl2 (by omega) (by omega)) EvArgs.nil)
      (show Gen.prog 0 = some Gen.ni_read_u16le from rfl)
      (show Gen.ni_read_u16le.params.length = 1 from rfl)
      (ni_read_u16le_exs m bd d hm 26 (by omega) hlen ro)
  let s3 : State := { locals := s2.locals.upd 5 (.int u16 (rd16le d 26)), mem := m, ro := ro }
  have hl3 : s3.locals 0 = some (.ptr bd 0) := rfl
  have hw6 : ExS Gen.prog s3
      (.call (some 6) 0 [(.index (.var 0) (.const (.int i32 28)) 1)]) .normal
      { locals := s3.locals.upd 6 (.int u16 (rd16le d 28)), mem := m, ro := ro } :=
    ExS.call_dst (EvArgs.cons (ev_ptr_const (s := s3) (d := d) (k := 28) hm hl3 (by omega) (by omega)) EvArgs.nil)
      (show Gen.prog 0 = some Gen.ni_read_u16le from rfl)
      (show Gen.ni_read_u16le.params.length = 1 from rfl)
      (ni_read_u16le_exs m bd d hm 28 (by omega) hlen ro)
  let s4 : State := { locals := s3.locals.upd 6 (.int u16 (rd16le d 28)), mem := m, ro := ro }
  have hl4 : s4.locals 0 = some (.ptr bd 0) := rfl
  have hw7 : ExS Gen.prog s4
      (.call (some 7) 1 [(.index (.var 0) (.const (.int i32 30)) 1)]) .normal
      { locals := s4.locals.upd 7 (.int u32 (rd32le d 30)), mem := m, ro := ro } :=
    ExS.call_dst (EvArgs.cons (ev_ptr_const (s := s4) (d := d) (k := 30) hm hl4 (by omega) (by omega)) EvArgs.nil)
      (show Gen.prog 1 = some Gen.ni_read_u32le from rfl)
      (show Gen.ni_read_u32le.params.length = 1 from rfl)
      (ni_read_u32le_exs m bd d hm 30 (by omega) hlen ro)
  exact ExS.seq hw3 (ExS.seq hw4 (ExS.seq hw5 (ExS.seq hw6 hw7)))







theorem ni_bmp_geometry_exs_pos (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hd : 34 ≤ d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : m 3 = some obl) (h48 : obl.length = 48) (ro : Bool)
    (hro : ro = false)
    (hA34 : IntTy.toInt ⟨32, true⟩ (rd32le d 18) > 0)
    (hB66 : IntTy.toInt ⟨32, true⟩ (rd32le d 22) ≠ 0)
    (hPl : rd16le d 26 = 1)
    (hPos : NANO.toInt32 (rd32le d 22) ≥ 0) :
    ∃ s', ExS Gen.prog ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩
      Gen.ni_bmp_geometry.body
      (.ret (some (.int ⟨32, true⟩ (bmpGeometryCode d)))) s' ∧
    (bmpGeometryCode d = 0 → s'.mem 3 =
      some (bmpTailBlock obl (rd32le d 18) (rd32le d 22) (rd16le d 28)
        (if rd16le d 28 = 32 then 4 else 3) 0)) ∧
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
  have eLT : EvE Gen.prog s5
      (.bin .lt (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0)))
      (boolVal false) := by
    have hAval : EvE Gen.prog s5
        (.bin .lt (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0)))
        (boolVal (decide (IntTy.toInt ⟨32, true⟩ (rd32le d 22) < 0))) :=
      EvE.bin hv4 (EvE.const _) (bin_i32_lt0 _)
    rw [e22] at hAval
    rw [decide_eq_false_iff_not.mpr (by omega : ¬ (NANO.toInt32 (rd32le d 22) < 0))] at hAval
    exact hAval
  have hSP11 : EvE Gen.prog s5
      (.cast ⟨8, false⟩ (.const (.int ⟨32, false⟩ 0))) (.int ⟨8, false⟩ 0) :=
    EvE.cast (EvE.const _) rfl
  have hSet11P : ExS Gen.prog s5
      (.set 11 (.cast ⟨8, false⟩ (.const (.int ⟨32, false⟩ 0))))
      .normal
      { s5 with locals := s5.locals.upd 11 (.int ⟨8, false⟩ 0) } :=
    ExS.set hSP11
  let s5A : State := { s5 with locals := s5.locals.upd 11 (.int ⟨8, false⟩ 0) }
  have hv4A : EvE Gen.prog s5A (.var 4) (.int ⟨32, true⟩ (rd32le d 22)) := EvE.var rfl
  have cast9P : EvE Gen.prog s5A
      (.cast ⟨32, false⟩ (.var 4)) (.int ⟨32, false⟩ (rd32le d 22)) :=
    EvE.cast hv4A (cast_u32_i32 (rd32le d 22) (rd32_lt d 22))
  have hSet9P : ExS Gen.prog s5A
      (.set 9 (.cast ⟨32, false⟩ (.var 4)))
      .normal
      { s5A with locals := s5A.locals.upd 9 (.int ⟨32, false⟩ (rd32le d 22)) } :=
    ExS.set cast9P
  let s5B : State := { s5A with locals := s5A.locals.upd 9 (.int ⟨32, false⟩ (rd32le d 22)) }
  have hPOSexec : ExS Gen.prog s5
      (.seq (.set 11 (.cast ⟨8, false⟩ (.const (.int ⟨32, false⟩ 0))))
            (.set 9 (.cast ⟨32, false⟩ (.var 4))))
      .normal s5B :=
    ExS.seq hSet11P hSet9P
  have hLTexec : ExS Gen.prog s5
      (.ite (.bin .lt (some ⟨32, true⟩) (.var 4) (.const (.int ⟨32, true⟩ 0)))
        (.seq (.ite (.bin .eq (some ⟨32, true⟩) (.var 4)
                      (.bin .sub (some ⟨32, true⟩)
                        (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 2147483647)))
                        (.const (.int ⟨32, true⟩ 1))))
                    (.ret (some (.const (.int ⟨32, true⟩ 4)))) .skip)
               (.seq (.set 11 (.cast ⟨8, false⟩ (.const (.int ⟨32, false⟩ 1))))
                     (.set 9 (.cast ⟨32, false⟩ (.un .neg ⟨32, true⟩ (.var 4))))))
        (.seq (.set 11 (.cast ⟨8, false⟩ (.const (.int ⟨32, false⟩ 0))))
              (.set 9 (.cast ⟨32, false⟩ (.var 4)))))
      .normal s5B :=
    ExS.ite eLT (truthy_boolVal false) hPOSexec
  have hIntmin : NANO.toInt32 (rd32le d 22) ≠ -2147483648 := by omega
  obtain ⟨s', code, hpost, hcode, hblk, hUnt⟩ := tail_exs m bd d hm size hs hd hlen obl hob h48
    ro hro
    (rd32le d 22) (rd32_lt d 22)
    0 (by omega)
    hgt hh0 hPl hIntmin
  refine ⟨s', ?_, fun hh => hblk (hcode ▸ hh), fun hh j hj => hUnt (hcode ▸ hh) j hj⟩
  rw [← hcode]
  exact ExS.seq hw3 (ExS.seq hw4 (ExS.seq hw5 (ExS.seq hw6 (ExS.seq hw7 (ExS.seq hR_skip
    (ExS.seq hLTexec hpost))))))


/-- NEG path with `height_i == INT32_MIN` (returns 4). -/
theorem ni_bmp_geometry_exs_neg_intmin (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hd : 34 ≤ d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : m 3 = some obl) (h48 : obl.length = 48) (ro : Bool)
    (hro : ro = false)
    (hA34 : IntTy.toInt ⟨32, true⟩ (rd32le d 18) > 0)
    (hB66 : IntTy.toInt ⟨32, true⟩ (rd32le d 22) ≠ 0)
    (hPl : rd16le d 26 = 1)
    (hNeg : NANO.toInt32 (rd32le d 22) < 0)
    (hInMin : NANO.toInt32 (rd32le d 22) = -2147483648) :
    ∃ s', ExS Gen.prog ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩
      Gen.ni_bmp_geometry.body
      (.ret (some (.int ⟨32, true⟩ (bmpGeometryCode d)))) s' ∧
    (bmpGeometryCode d = 0 → s'.mem 3 =
      some (bmpTailBlock obl (rd32le d 18) 2147483648 (rd16le d 28)
        (if rd16le d 28 = 32 then 4 else 3) 1)) ∧
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
      (boolVal true) := by
    rw [e22', hInMin] at hEQconst
    have hTwo31 : IntTy.toInt ⟨32, true⟩ 2147483648 = -2147483648 := by
      simp [IntTy.toInt, IntTy.modulus, IntTy.width, IntTy.signed]
    rw [hTwo31] at hEQconst
    simpa using hEQconst
  have hINTMINe : ExS Gen.prog s5
      (.ite (.bin .eq (some ⟨32, true⟩) (.var 4)
        (.bin .sub (some ⟨32, true⟩)
          (.un .neg ⟨32, true⟩ (Expr.const (Val.int ⟨32, true⟩ 2147483647)))
          (Expr.const (Val.int ⟨32, true⟩ 1))))
        (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 4)))) .skip)
      (Outcome.ret (some (.int ⟨32, true⟩ 4))) s5 :=
    ExS.ite eMI (truthy_boolVal true) (ExS.ret (EvE.const (v := (.int ⟨32, true⟩ 4))))
  have hNegThen : ExS Gen.prog s5
      (.seq
        (.ite (.bin .eq (some ⟨32, true⟩) (.var 4)
          (.bin .sub (some ⟨32, true⟩)
            (.un .neg ⟨32, true⟩ (Expr.const (Val.int ⟨32, true⟩ 2147483647)))
            (Expr.const (Val.int ⟨32, true⟩ 1))))
          (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 4)))) .skip)
        (.seq (.set 11 (.cast ⟨8, false⟩ (Expr.const (Val.int ⟨32, false⟩ 1))))
              (.set 9 (.cast ⟨32, false⟩ (.un .neg ⟨32, true⟩ (.var 4))))))
      (Outcome.ret (some (.int ⟨32, true⟩ 4))) s5 :=
    ExS.seq_ret hINTMINe
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
            (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 4)))) .skip)
           (.seq (.set 11 (.cast ⟨8, false⟩ (Expr.const (Val.int ⟨32, false⟩ 1))))
                 (.set 9 (.cast ⟨32, false⟩ (.un .neg ⟨32, true⟩ (.var 4))))))
        (.seq (.set 11 (.cast ⟨8, false⟩ (Expr.const (Val.int ⟨32, false⟩ 0))))
              (.set 9 (.cast ⟨32, false⟩ (.var 4)))))
      (Outcome.ret (some (.int ⟨32, true⟩ 4))) s5 :=
    ExS.ite eLT (truthy_boolVal true) hNegThen
  have hbv : bmpGeometryCode d = 4 := by
    have hgt' : ¬ (NANO.toInt32 (rd32le d 18) ≤ 0) := by omega
    simp [bmpGeometryCode, hgt', hh0, hPl, hInMin]
  refine ⟨s5, ?_, fun hb => by rw [hbv] at hb; exact absurd hb (by decide),
    fun _ _ _ => rfl⟩
  rw [hbv]
  exact ExS.seq hw3 (ExS.seq hw4 (ExS.seq hw5 (ExS.seq hw6 (ExS.seq hw7 (ExS.seq hR_skip
    (ExS.seq_ret hLTexec))))))


