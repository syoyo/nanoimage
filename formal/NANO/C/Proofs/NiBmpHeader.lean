/-
  `ni_bmp_header` — the BMP header checks, composed from the individually
  proven pieces (`ni_bmp_sig_ok`, `ni_bmp_layout_ok`, and
  `ni_bmp_header_rem_exs` for everything after the readers).
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Lemmas
import NANO.Spec
import NANO.Bmp
import NANO.C.Proofs.Core
import NANO.C.Proofs.Bmp
import NANO.C.Proofs.NiBmpHeaderSpec
import NANO.C.Proofs.NiBmpHeaderLoads
import NANO.C.Proofs.NiBmpHeaderSpecGeo
import NANO.C.Proofs.NiBmpHeaderCompose

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 800000

namespace NANO.C.Proofs
open NANO NANO.C

/-- `ni_bmp_header` returns `bmpHeaderCode`; when the header succeeds, the
    info object holds `bmpHeaderFinalBlock` (guarded on the spec-side stage
    verdicts, which the caller supplies). -/
theorem ni_bmp_header_exs (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hd : 54 ≤ d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : m 3 = some obl) (h48 : obl.length = 48) (ro : Bool)
    (hro : ro = false) :
    ∃ s', ExS Gen.prog ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩
      Gen.ni_bmp_header.body
      (.ret (some (.int ⟨32, true⟩ (bmpHeaderCode size d)))) s' ∧
      (sigOk size d = true → layoutOk size d = true → bmpGeometryCode d = 0 →
       bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
         (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size = 0 →
       bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10) = 0 →
       ∃ gout, s'.mem 3 = some (bmpHeaderFinalBlock d gout) ∧ gout.length = 48) := by
  have h54 : 54 ≤ d.length := hd
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  let s0 : State := { locals := frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], mem := m, ro := ro }
  have hl0 : frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0] 0 = some (.ptr bd 0) := rfl
  have ptr0 : EvE Gen.prog s0 (.var 0) (.ptr bd 0) := EvE.var rfl
  have size0 : EvE Gen.prog s0 (.var 1) (.int u64 size) := EvE.var rfl
  have ptr3 : EvE Gen.prog s0 (.var 2) (.ptr 3 0) := EvE.var rfl
  -- ===== Sig gate: call ni_bmp_sig_ok (fid 12) as an expression-call =====
  obtain ⟨sSig, exSig⟩ := ni_bmp_sig_ok_exs m bd d hm size hs (by omega) true
  have hSigExpr : EvE Gen.prog s0 (.call 12 [(.var 0), (.var 1)])
      (.int ⟨32, true⟩ (if sigOk size d then 1 else 0)) :=
    EvE.call (EvArgs.cons (EvE.var rfl) (EvArgs.cons (EvE.var rfl) EvArgs.nil))
      (show Gen.prog 12 = some Gen.ni_bmp_sig_ok from rfl)
      (show Gen.ni_bmp_sig_ok.params.length = 2 from rfl)
      exSig
  have hNot : EvE Gen.prog s0 (.un .lnot ⟨32, true⟩ (.call 12 [(.var 0), (.var 1)]))
      (.int ⟨32, true⟩ (if sigOk size d then 0 else 1)) := by
    have he : evalUn .lnot ⟨32, true⟩ (.int ⟨32, true⟩ (if sigOk size d then 1 else 0)) =
        .ok (.int ⟨32, true⟩ (if sigOk size d then 0 else 1)) := by
      cases sigOk size d <;> rfl
    exact EvE.un hSigExpr he
  -- ===== Layout gate: call ni_bmp_layout_ok (fid 13) as an expression-call =====
  obtain ⟨sLay, exLay⟩ := ni_bmp_layout_ok_exs m bd d hm size hs (by omega) (by omega) true
  have hLayExpr : EvE Gen.prog s0 (.call 13 [(.var 0), (.var 1)])
      (.int ⟨32, true⟩ (if layoutOk size d then 1 else 0)) :=
    EvE.call (EvArgs.cons (EvE.var rfl) (EvArgs.cons (EvE.var rfl) EvArgs.nil))
      (show Gen.prog 13 = some Gen.ni_bmp_layout_ok from rfl)
      (show Gen.ni_bmp_layout_ok.params.length = 2 from rfl)
      exLay
  have hNot2 : EvE Gen.prog s0 (.un .lnot ⟨32, true⟩ (.call 13 [(.var 0), (.var 1)]))
      (.int ⟨32, true⟩ (if layoutOk size d then 0 else 1)) := by
    have he : evalUn .lnot ⟨32, true⟩ (.int ⟨32, true⟩ (if layoutOk size d then 1 else 0)) =
        .ok (.int ⟨32, true⟩ (if layoutOk size d then 0 else 1)) := by
      cases layoutOk size d <;> rfl
    exact EvE.un hLayExpr he
  -- =================== SIG GATE ===================
  by_cases hSig : sigOk size d
  · -- sig passes
    have hNot1t : EvE Gen.prog s0 (.un .lnot ⟨32, true⟩ (.call 12 [(.var 0), (.var 1)])) (boolVal false) := by
      have he : evalUn .lnot ⟨32, true⟩ (.int ⟨32, true⟩ (if sigOk size d then 1 else 0)) = .ok (.int ⟨32, true⟩ 0) := by
        rw [hSig]; rfl
      exact EvE.un hSigExpr he
    have hsig_skip : ExS Gen.prog s0
        (.ite (.un .lnot ⟨32, true⟩ (.call 12 [(.var 0), (.var 1)]))
          (.ret (some (.const (.int ⟨32, true⟩ 1)))) .skip)
        .normal s0 :=
      ExS.ite hNot1t truthy_false ExS.skip
    -- =================== LAYOUT GATE ===================
    by_cases hLayout : layoutOk size d
    · -- layout passes → proceed past the layout ITE
      have hNot2t : EvE Gen.prog s0
          (.un .lnot ⟨32, true⟩ (.call 13 [(.var 0), (.var 1)])) (boolVal false) := by
        have he : evalUn .lnot ⟨32, true⟩ (.int ⟨32, true⟩ (if layoutOk size d then 1 else 0)) =
            .ok (.int ⟨32, true⟩ 0) := by
          rw [hLayout]; rfl
        exact EvE.un hLayExpr he
      have hlay_skip : ExS Gen.prog s0
          (.ite (.un .lnot ⟨32, true⟩ (.call 13 [(.var 0), (.var 1)]))
            (.ret (some (.const (.int ⟨32, true⟩ 2)))) .skip)
          .normal s0 :=
        ExS.ite hNot2t truthy_false ExS.skip
      -- =================== readers (pixel offset, dib_size, colors_used) ===================
      let s3 : State := { locals := s0.locals.upd 3 (.int ⟨32, false⟩ (rd32le d 10)), mem := m, ro := ro }
      have hw3 : ExS Gen.prog s0
          (.call (some 3) 1 [(.index (.var 0) (.const (.int ⟨32, true⟩ 10)) 1)]) .normal s3 :=
        ExS.call_dst (EvArgs.cons (ev_ptr_const (s := s0) (d := d) (k := 10) hm hl0 (by omega) (by omega)) EvArgs.nil)
          (show Gen.prog 1 = some Gen.ni_read_u32le from rfl)
          (show Gen.ni_read_u32le.params.length = 1 from rfl)
          (ni_read_u32le_exs m bd d hm 10 (by omega) hlen ro)
      have hl3 : s3.locals 0 = some (.ptr bd 0) := rfl
      let s4 : State := { locals := s3.locals.upd 4 (.int ⟨32, false⟩ (rd32le d 14)), mem := m, ro := ro }
      have hw4 : ExS Gen.prog s3
          (.call (some 4) 1 [(.index (.var 0) (.const (.int ⟨32, true⟩ 14)) 1)]) .normal s4 :=
        ExS.call_dst (EvArgs.cons (ev_ptr_const (s := s3) (d := d) (k := 14) hm hl3 (by omega) (by omega)) EvArgs.nil)
          (show Gen.prog 1 = some Gen.ni_read_u32le from rfl)
          (show Gen.ni_read_u32le.params.length = 1 from rfl)
          (ni_read_u32le_exs m bd d hm 14 (by omega) hlen ro)
      have hl4 : s4.locals 0 = some (.ptr bd 0) := rfl
      let s6 : State := { locals := s4.locals.upd 6 (.int ⟨32, false⟩ (rd32le d 46)), mem := m, ro := ro }
      have hw6 : ExS Gen.prog s4
          (.call (some 6) 1 [(.index (.var 0) (.const (.int ⟨32, true⟩ 46)) 1)]) .normal s6 :=
        ExS.call_dst (EvArgs.cons (ev_ptr_const (s := s4) (d := d) (k := 46) hm hl4 (by omega) (by omega)) EvArgs.nil)
          (show Gen.prog 1 = some Gen.ni_read_u32le from rfl)
          (show Gen.ni_read_u32le.params.length = 1 from rfl)
          (ni_read_u32le_exs m bd d hm 46 (by omega) hlen ro)
      have hl6 : s6.locals 0 = some (.ptr bd 0) := rfl
      -- =================== readers done. S6 enters the Rem phase ==================
      have hl0n : s6.locals 0 = some (.ptr bd 0) := rfl
      have hl1n : s6.locals 1 = some (.int ⟨64, false⟩ size) := rfl
      have hl2n : s6.locals 2 = some (.ptr 3 0) := rfl
      have hl3n : s6.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)) := rfl
      have hl4n : s6.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)) := rfl
      have hl6n : s6.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46)) := rfl
      have hMem6 : s6.mem 3 = some obl := hob
      have hS6ro : s6.ro = false := hro
      obtain ⟨s', hRem, hRemMem⟩ := ni_bmp_header_rem_exs s6 d bd hm size hs hd hlen obl hMem6 h48 hS6ro
        hSig hLayout hl0n hl2n hl1n hl3n hl4n hl6n
      refine ⟨s', ?_, fun _ _ hg ha hp => hRemMem hg ha hp⟩
      show ExS Gen.prog ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩
        Gen.ni_bmp_header.body (.ret (some (.int ⟨32, true⟩ (bmpHeaderCode size d)))) s'
      exact ExS.seq hsig_skip (ExS.seq hlay_skip (ExS.seq hw3 (ExS.seq hw4 (ExS.seq hw6 hRem))))

    · -- layout fails → return 2
      have hFalseL : layoutOk size d = false := by
        cases hb : layoutOk size d
        · rfl
        · exact absurd hb hLayout
      rw [hFalseL] at hNot2
      have hv : (if false then (0 : Nat) else 1) = 1 := rfl
      simp only [hv] at hNot2
      have hbv : bmpHeaderCode size d = 2 := bmpHeaderCode_two_of_not_layoutOk size d hSig hFalseL
      have hite : ExS Gen.prog s0
          (.ite (.un .lnot ⟨32, true⟩ (.call 13 [(.var 0), (.var 1)]))
            (.ret (some (.const (.int ⟨32, true⟩ 2)))) .skip)
          (.ret (some (.int ⟨32, true⟩ 2))) s0 :=
        ExS.ite hNot2 truthy_true (ExS.ret (EvE.const _))
      refine ⟨s0, ?_, fun _ hlay _ _ _ => absurd hlay hLayout⟩
      show ExS Gen.prog ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩
        Gen.ni_bmp_header.body (.ret (some (.int ⟨32, true⟩ (bmpHeaderCode size d)))) s0
      rw [hbv]
      exact ExS.seq hsig_skip (ExS.seq_ret hite)
  · -- sig failure → return 1
    have hFalse : sigOk size d = false := by
      cases hb : sigOk size d
      · rfl
      · exact absurd hb hSig
    rw [hFalse] at hNot
    have hv : (if false then (0 : Nat) else 1) = 1 := rfl
    simp only [hv] at hNot
    have hite : ExS Gen.prog s0
        (.ite (.un .lnot ⟨32, true⟩ (.call 12 [(.var 0), (.var 1)]))
          (.ret (some (.const (.int ⟨32, true⟩ 1)))) .skip)
        (.ret (some (.int ⟨32, true⟩ 1))) s0 :=
      ExS.ite hNot truthy_true (ExS.ret (EvE.const _))
    have hbv : bmpHeaderCode size d = 1 := bmpHeaderCode_one_of_not_sigOk size d hFalse
    refine ⟨s0, ?_, fun hsig _ _ _ _ => absurd hsig hSig⟩
    show ExS Gen.prog ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩
      Gen.ni_bmp_header.body (.ret (some (.int ⟨32, true⟩ (bmpHeaderCode size d)))) s0
    rw [hbv]
    exact ExS.seq_ret hite

end NANO.C.Proofs
