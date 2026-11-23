/-
  `ni_tga_write_pixel` refinement proof.

  C body (fid 22), locals: 0=out (ptr at block offset 0), 1=base (u64),
  2=channels, 3=s0, 4=s1, 5=s2, 6=s3 (all u8). Writes channel-swizzled
  bytes at `out[base .. base+channels)` and returns 1; bad channel returns 0.
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

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 1600000

namespace NANO.C.Proofs
open NANO NANO.C

private theorem t_true_wp : truthy (boolVal true) = .ok true := truthy_boolVal true
private theorem t_false_wp : truthy (boolVal false) = .ok false := truthy_boolVal false

private theorem encodeLE_one_wp (x : Nat) (hx : x < 256) : encodeLE 1 x = [UInt8.ofNat x] := by
  simp [encodeLE, Nat.mod_eq_of_lt hx]

private theorem tgaPixelOut_one_wp (a b c d : UInt8) : tgaPixelOut 1 a b c d = [a] := by
  simp [tgaPixelOut]

private theorem tgaPixelOut_three_wp (a b c d : UInt8) : tgaPixelOut 3 a b c d = [c, b, a] := by
  simp [tgaPixelOut]

private theorem tgaPixelOut_four_wp (a b c d : UInt8) : tgaPixelOut 4 a b c d = [c, b, a, d] := by
  simp [tgaPixelOut]

private theorem ev_eq_u32_wp {s : State} {e1 e2 : Expr} {a b : Nat}
    (h1 : EvE Gen.prog s e1 (.int ⟨32, false⟩ a)) (h2 : EvE Gen.prog s e2 (.int ⟨32, false⟩ b)) :
    EvE Gen.prog s (.bin .eq (some ⟨32, false⟩) e1 e2) (boolVal (decide (a = b))) :=
  EvE.bin h1 h2 (by simp [evalBin, evalBinInt, binInt, intOf, isPtr, ptrEq])

/-- Length of `obl.take base ++ encodeLE 1 v ++ obl.drop (base+1)` is preserved. -/
private theorem blk1_len (obl : List UInt8) (base v : Nat) (hb : base + 1 ≤ obl.length) :
    (obl.take base ++ encodeLE 1 v ++ obl.drop (base + 1)).length = obl.length := by
  simp [encodeLE_length, List.length_take, List.length_drop, List.length_append,
    Nat.min_eq_left (by omega : base ≤ obl.length)]
  omega

private theorem blk2_len (obl : List UInt8) (base a b : Nat) (hb : base + 2 ≤ obl.length) :
    ((obl.take base ++ encodeLE 1 a ++ obl.drop (base + 1)).take (base + 1) ++ encodeLE 1 b ++
        (obl.take base ++ encodeLE 1 a ++ obl.drop (base + 1)).drop (base + 2)).length = obl.length := by
  have h1 : (obl.take base ++ encodeLE 1 a ++ obl.drop (base + 1)).length = obl.length := blk1_len obl base a (by omega)
  simp [encodeLE_length, List.length_take, List.length_drop, List.length_append, h1,
    Nat.min_eq_left (by omega : base + 1 ≤ obl.length)]
  omega

private theorem blk3_len (obl : List UInt8) (base a b c : Nat) (hb : base + 3 ≤ obl.length) :
    (((obl.take base ++ encodeLE 1 a ++ obl.drop (base + 1)).take (base + 1) ++ encodeLE 1 b ++
        (obl.take base ++ encodeLE 1 a ++ obl.drop (base + 1)).drop (base + 2)).take (base + 2) ++
        encodeLE 1 c ++
        ((obl.take base ++ encodeLE 1 a ++ obl.drop (base + 1)).take (base + 1) ++ encodeLE 1 b ++
          (obl.take base ++ encodeLE 1 a ++ obl.drop (base + 1)).drop (base + 2)).drop (base + 3)).length = obl.length := by
  have h2 : ((obl.take base ++ encodeLE 1 a ++ obl.drop (base + 1)).take (base + 1) ++ encodeLE 1 b ++
        (obl.take base ++ encodeLE 1 a ++ obl.drop (base + 1)).drop (base + 2)).length = obl.length := blk2_len obl base a b (by omega)
  simp [encodeLE_length, List.length_take, List.length_drop, List.length_append, h2,
    Nat.min_eq_left (by omega : base + 2 ≤ obl.length)]
  omega

private theorem take_pref (pre rest : List UInt8) (k : Nat) (h : pre.length = k) :
    (pre ++ rest).take k = pre := by
  rw [← h]; exact List.take_append_length

private theorem drop_pref (pre rest : List UInt8) (k j : Nat) (h : pre.length = k) :
    (pre ++ rest).drop (k + j) = rest.drop j := by
  rw [← h]; exact List.drop_length_add_append j

/-- Byte shape after the three channel-3 stores (target: `tgaPixelOut 3`). -/
private theorem shape3 (obl : List UInt8) (base s0 s1 s2 : Nat)
    (hb : base + 3 ≤ obl.length) (h0 : s0 < 256) (h1 : s1 < 256) (h2 : s2 < 256) :
    let b1 := obl.take base ++ encodeLE 1 s2 ++ obl.drop (base + 1)
    let b2 := b1.take (base + 1) ++ encodeLE 1 s1 ++ b1.drop (base + 2)
    b2.take (base + 2) ++ encodeLE 1 s0 ++ b2.drop (base + 3) =
      obl.take base
        ++ tgaPixelOut 3 (UInt8.ofNat s0) (UInt8.ofNat s1) (UInt8.ofNat s2) (UInt8.ofNat s3)
        ++ obl.drop (base + (tgaPixelOut 3 (UInt8.ofNat s0) (UInt8.ofNat s1) (UInt8.ofNat s2) (UInt8.ofNat s3)).length) := by
  intro b1 b2
  have h12 : b2 = obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1 ++ obl.drop (base + 2) := by
    have h := splice_enc_3 obl s2 s1 base (by omega)
    simpa [b2, b1] using h
  rw [h12]
  have ht : (obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1).length = base + 2 := by
    simp [encodeLE_length, List.length_take, Nat.min_eq_left (by omega : base ≤ obl.length)]
  have htake : (obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1 ++ obl.drop (base + 2)).take (base + 2)
      = obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1 := take_pref _ _ _ ht
  have hdrop : (obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1 ++ obl.drop (base + 2)).drop (base + 3)
      = obl.drop (base + 3) := by
    have h3 : base + 3 = (base + 2) + 1 := by omega
    rw [h3, drop_pref (obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1) (obl.drop (base + 2)) (base + 2) 1 ht]
    simp [List.drop_drop]
  rw [htake, hdrop]
  rw [encodeLE_one_wp s2 h2, encodeLE_one_wp s1 h1, encodeLE_one_wp s0 h0]
  simp [tgaPixelOut_three_wp, List.append_assoc]

/-- Byte shape after the four channel-4 stores (target: `tgaPixelOut 4`). -/
private theorem shape4 (obl : List UInt8) (base s0 s1 s2 s3 : Nat)
    (hb : base + 4 ≤ obl.length)
    (h0 : s0 < 256) (h1 : s1 < 256) (h2 : s2 < 256) (h3 : s3 < 256) :
    let b1 := obl.take base ++ encodeLE 1 s2 ++ obl.drop (base + 1)
    let b2 := b1.take (base + 1) ++ encodeLE 1 s1 ++ b1.drop (base + 2)
    let b3 := b2.take (base + 2) ++ encodeLE 1 s0 ++ b2.drop (base + 3)
    b3.take (base + 3) ++ encodeLE 1 s3 ++ b3.drop (base + 4) =
      obl.take base
        ++ tgaPixelOut 4 (UInt8.ofNat s0) (UInt8.ofNat s1) (UInt8.ofNat s2) (UInt8.ofNat s3)
        ++ obl.drop (base + (tgaPixelOut 4 (UInt8.ofNat s0) (UInt8.ofNat s1) (UInt8.ofNat s2) (UInt8.ofNat s3)).length) := by
  intro b1 b2 b3
  have h12 : b2 = obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1 ++ obl.drop (base + 2) := by
    have h := splice_enc_3 obl s2 s1 base (by omega); simpa [b2, b1] using h
  have h23 : b3 = obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1 ++ encodeLE 1 s0 ++ obl.drop (base + 3) := by
    rw [show b3 = b2.take (base + 2) ++ encodeLE 1 s0 ++ b2.drop (base + 3) from rfl, h12]
    have ht : (obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1).length = base + 2 := by
      simp [encodeLE_length, List.length_take, Nat.min_eq_left (by omega : base ≤ obl.length)]
    have htake : (obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1 ++ obl.drop (base + 2)).take (base + 2)
        = obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1 := take_pref _ _ _ ht
    have hdrop : (obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1 ++ obl.drop (base + 2)).drop (base + 3)
        = obl.drop (base + 3) := by
      have h3 : base + 3 = (base + 2) + 1 := by omega
      rw [h3, drop_pref (obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1) (obl.drop (base + 2)) (base + 2) 1 ht]
      simp [List.drop_drop]
    rw [htake, hdrop]
  rw [h23]
  have ht : (obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1 ++ encodeLE 1 s0).length = base + 3 := by
    simp [encodeLE_length, List.length_take, Nat.min_eq_left (by omega : base ≤ obl.length)]
  have htake : (obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1 ++ encodeLE 1 s0 ++ obl.drop (base + 3)).take (base + 3)
      = obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1 ++ encodeLE 1 s0 := take_pref _ _ _ ht
  have hdrop : (obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1 ++ encodeLE 1 s0 ++ obl.drop (base + 3)).drop (base + 4)
      = obl.drop (base + 4) := by
    have h4 : base + 4 = (base + 3) + 1 := by omega
    rw [h4, drop_pref (obl.take base ++ encodeLE 1 s2 ++ encodeLE 1 s1 ++ encodeLE 1 s0) (obl.drop (base + 3)) (base + 3) 1 ht]
    simp [List.drop_drop]
  rw [htake, hdrop]
  rw [encodeLE_one_wp s2 h2, encodeLE_one_wp s1 h1, encodeLE_one_wp s0 h0, encodeLE_one_wp s3 h3]
  simp [tgaPixelOut_four_wp, List.append_assoc]

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- `ni_tga_write_pixel` success refinement: for a valid channel count it
    writes exactly `tgaPixelOut` at `base` and returns 1. -/
theorem ni_tga_write_pixel_exs (m : Mem) (ob : Nat) (obl : List UInt8) (hm : m ob = some obl)
    (base : Nat) (hbase : base < 2 ^ 64) (hlobl : obl.length < 2 ^ 64)
    (channels s0 s1 s2 s3 : Nat)
    (hc : channels = 1 ∨ channels = 3 ∨ channels = 4)
    (hs0 : s0 < 256) (hs1 : s1 < 256) (hs2 : s2 < 256) (hs3 : s3 < 256)
    (hlen : base + (tgaPixelOut channels (UInt8.ofNat s0) (UInt8.ofNat s1) (UInt8.ofNat s2) (UInt8.ofNat s3)).length ≤ obl.length)
    (ro : Bool) (hro : ro = false) :
    ∃ s', ExS Gen.prog ⟨frameLocals [0,1,2,3,4,5,6]
        [.ptr ob 0, .int u64 base, .int u8 channels, .int u8 s0, .int u8 s1, .int u8 s2, .int u8 s3], m, ro⟩
      Gen.ni_tga_write_pixel.body (.ret (some (.int i32 1))) s' ∧
      s'.mem ob = some (obl.take base ++ (tgaPixelOut channels (UInt8.ofNat s0) (UInt8.ofNat s1) (UInt8.ofNat s2) (UInt8.ofNat s3)) ++ obl.drop (base + (tgaPixelOut channels (UInt8.ofNat s0) (UInt8.ofNat s1) (UInt8.ofNat s2) (UInt8.ofNat s3)).length)) ∧
      (∀ j, j ≠ ob → s'.mem j = m j) := by
  let st : State := ⟨frameLocals [0,1,2,3,4,5,6]
      [.ptr ob 0, .int u64 base, .int u8 channels, .int u8 s0, .int u8 s1, .int u8 s2, .int u8 s3], m, ro⟩
  have l0 : st.locals 0 = some (.ptr ob 0) := rfl
  have l1 : st.locals 1 = some (.int u64 base) := rfl
  have l2 : st.locals 2 = some (.int u8 channels) := rfl
  have l3 : st.locals 3 = some (.int u8 s0) := rfl
  have l4 : st.locals 4 = some (.int u8 s1) := rfl
  have l5 : st.locals 5 = some (.int u8 s2) := rfl
  have l6 : st.locals 6 = some (.int u8 s3) := rfl
  have hSro : st.ro = false := hro
  rcases hc with hc1 | hc3 | hc4
  · -- channels = 1
    subst hc1
    have heq : EvE Gen.prog st (.bin .eq (some u32) (.cast u32 (.var 2)) (.const (.int u32 1))) (boolVal true) := by
      exact ev_eq_u32_wp (EvE.cast (EvE.var l2) rfl) (EvE.const _)
    have hb : base + 1 ≤ obl.length := by simpa [tgaPixelOut_one_wp] using hlen
    have haddr0 : EvE Gen.prog st (.index (.var 0) (.var 1) 1) (.ptr ob (0 + base * 1)) :=
      EvE.index (EvE.var l0) (EvE.var l1) (ptrAddN_ok hm (by omega))
    have hst0 : ExS Gen.prog st (.store (.int u8) (.index (.var 0) (.var 1) 1) (.var 3)) .normal
        {st with mem := m.upd ob (obl.take base ++ encodeLE 1 s0 ++ obl.drop (base + 1))} :=
      ExS.store haddr0 (EvE.var l3) hSro (store_byte_at m ob obl hm base (by omega) s0 hs0)
    refine ⟨{st with mem := m.upd ob (obl.take base ++ encodeLE 1 s0 ++ obl.drop (base + 1))}, ?_, ?_, ?_⟩
    · exact ExS.seq_ret (ExS.ite heq t_true_wp (ExS.seq hst0 (ExS.ret (EvE.const _))))
    · dsimp only
      rw [Mem.upd_same]
      simp [tgaPixelOut_one_wp, encodeLE_one_wp s0 hs0]
    · intro j hj; simp [Mem.upd, hj]
  · -- channels = 3
    subst hc3
    have heq1f : EvE Gen.prog st (.bin .eq (some u32) (.cast u32 (.var 2)) (.const (.int u32 1))) (boolVal false) := by
      exact ev_eq_u32_wp (EvE.cast (EvE.var l2) rfl) (EvE.const _)
    have hskip1 : ExS Gen.prog st (.ite (.bin .eq (some u32) (.cast u32 (.var 2)) (.const (.int u32 1))) (.seq (.store (.int u8) (.index (.var 0) (.var 1) 1) (.var 3)) (.ret (some (.const (.int i32 1))))) .skip) .normal st :=
      ExS.ite heq1f t_false_wp ExS.skip
    have heq3 : EvE Gen.prog st (.bin .eq (some u32) (.cast u32 (.var 2)) (.const (.int u32 3))) (boolVal true) := by
      exact ev_eq_u32_wp (EvE.cast (EvE.var l2) rfl) (EvE.const _)
    have hb : base + 3 ≤ obl.length := by simpa [tgaPixelOut_three_wp] using hlen
    have haddr0 : EvE Gen.prog st (.index (.var 0) (.var 1) 1) (.ptr ob (0 + base * 1)) :=
      EvE.index (EvE.var l0) (EvE.var l1) (ptrAddN_ok hm (by omega))
    have hst0 : ExS Gen.prog st (.store (.int u8) (.index (.var 0) (.var 1) 1) (.var 5)) .normal
        {st with mem := m.upd ob (obl.take base ++ encodeLE 1 s2 ++ obl.drop (base + 1))} :=
      ExS.store haddr0 (EvE.var l5) hSro (store_byte_at m ob obl hm base (by omega) s2 hs2)
    let b1 := obl.take base ++ encodeLE 1 s2 ++ obl.drop (base + 1)
    let m1 := m.upd ob b1
    let s1s : State := {st with mem := m1}
    have hm1 : m1 ob = some b1 := by simp [m1]
    have hb1 : b1.length = obl.length := blk1_len obl base s2 (by omega)
    have haddr1 : EvE Gen.prog s1s (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 1)))) 1) (.ptr ob (0 + (base + 1) * 1)) :=
      EvE.index (EvE.var (show s1s.locals 0 = some (.ptr ob 0) from rfl))
        (EvE_u64_add_const (i := 1) (k := 1) (show s1s.locals 1 = some (.int u64 base) from rfl) (by omega) (by omega))
        (ptrAddN_ok hm1 (by rw [hb1]; omega))
    have hst1 : ExS Gen.prog s1s (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 1)))) 1) (.var 4)) .normal
        {s1s with mem := m1.upd ob (b1.take (base + 1) ++ encodeLE 1 s1 ++ b1.drop (base + 2))} :=
      ExS.store haddr1
        (EvE.var (show s1s.locals 4 = some (.int u8 s1) from rfl))
        (by rw [show s1s.ro = st.ro from rfl]; exact hSro)
        (store_byte_at m1 ob b1 hm1 (base + 1) (by rw [hb1]; omega) s1 hs1)
    let b2 := b1.take (base + 1) ++ encodeLE 1 s1 ++ b1.drop (base + 2)
    let m2 := m1.upd ob b2
    let s2s : State := {s1s with mem := m2}
    have hm2 : m2 ob = some b2 := by simp [m2]
    have hb2 : b2.length = obl.length := blk2_len obl base s2 s1 (by omega)
    have haddr2 : EvE Gen.prog s2s (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 2)))) 1) (.ptr ob (0 + (base + 2) * 1)) :=
      EvE.index (EvE.var (show s2s.locals 0 = some (.ptr ob 0) from rfl))
        (EvE_u64_add_const (i := 1) (k := 2) (show s2s.locals 1 = some (.int u64 base) from rfl) (by omega) (by omega))
        (ptrAddN_ok hm2 (by rw [hb2]; omega))
    have hst2 : ExS Gen.prog s2s (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 2)))) 1) (.var 3)) .normal
        {s2s with mem := m2.upd ob (b2.take (base + 2) ++ encodeLE 1 s0 ++ b2.drop (base + 3))} :=
      ExS.store haddr2
        (EvE.var (show s2s.locals 3 = some (.int u8 s0) from rfl))
        (by rw [show s2s.ro = st.ro from rfl]; exact hSro)
        (store_byte_at m2 ob b2 hm2 (base + 2) (by rw [hb2]; omega) s0 hs0)
    have hbody3 : ExS Gen.prog st (.ite (.bin .eq (some u32) (.cast u32 (.var 2)) (.const (.int u32 3))) (.seq (.store (.int u8) (.index (.var 0) (.var 1) 1) (.var 5)) (.seq (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 1)))) 1) (.var 4)) (.seq (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 2)))) 1) (.var 3)) (.ret (some (.const (.int i32 1))))))) .skip) (.ret (some (.int i32 1))) {s2s with mem := m2.upd ob (b2.take (base + 2) ++ encodeLE 1 s0 ++ b2.drop (base + 3))} := by
      refine ExS.ite heq3 t_true_wp ?_
      exact ExS.seq hst0 (ExS.seq hst1 (ExS.seq hst2 (ExS.ret (EvE.const _))))
    refine ⟨{s2s with mem := m2.upd ob (b2.take (base + 2) ++ encodeLE 1 s0 ++ b2.drop (base + 3))}, ?_, ?_, ?_⟩
    · exact ExS.seq hskip1 (ExS.seq_ret hbody3)
    · dsimp only
      rw [Mem.upd_same]
      exact congrArg some (shape3 obl base s0 s1 s2 hb hs0 hs1 hs2)
    · intro j hj; simp [Mem.upd, hj, s2s, s1s, m2, m1]
  · -- channels = 4
    subst hc4
    have heq1f : EvE Gen.prog st (.bin .eq (some u32) (.cast u32 (.var 2)) (.const (.int u32 1))) (boolVal false) := by
      exact ev_eq_u32_wp (EvE.cast (EvE.var l2) rfl) (EvE.const _)
    have hskip1 : ExS Gen.prog st (.ite (.bin .eq (some u32) (.cast u32 (.var 2)) (.const (.int u32 1))) (.seq (.store (.int u8) (.index (.var 0) (.var 1) 1) (.var 3)) (.ret (some (.const (.int i32 1))))) .skip) .normal st :=
      ExS.ite heq1f t_false_wp ExS.skip
    have heq3f : EvE Gen.prog st (.bin .eq (some u32) (.cast u32 (.var 2)) (.const (.int u32 3))) (boolVal false) := by
      exact ev_eq_u32_wp (EvE.cast (EvE.var l2) rfl) (EvE.const _)
    have hskip3 : ExS Gen.prog st (.ite (.bin .eq (some u32) (.cast u32 (.var 2)) (.const (.int u32 3))) (.seq (.store (.int u8) (.index (.var 0) (.var 1) 1) (.var 5)) (.seq (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 1)))) 1) (.var 4)) (.seq (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 2)))) 1) (.var 3)) (.ret (some (.const (.int i32 1))))))) .skip) .normal st :=
      ExS.ite heq3f t_false_wp ExS.skip
    have heq4 : EvE Gen.prog st (.bin .eq (some u32) (.cast u32 (.var 2)) (.const (.int u32 4))) (boolVal true) := by
      exact ev_eq_u32_wp (EvE.cast (EvE.var l2) rfl) (EvE.const _)
    have hb : base + 4 ≤ obl.length := by simpa [tgaPixelOut_four_wp] using hlen
    have haddr0 : EvE Gen.prog st (.index (.var 0) (.var 1) 1) (.ptr ob (0 + base * 1)) :=
      EvE.index (EvE.var l0) (EvE.var l1) (ptrAddN_ok hm (by omega))
    have hst0 : ExS Gen.prog st (.store (.int u8) (.index (.var 0) (.var 1) 1) (.var 5)) .normal
        {st with mem := m.upd ob (obl.take base ++ encodeLE 1 s2 ++ obl.drop (base + 1))} :=
      ExS.store haddr0 (EvE.var l5) hSro (store_byte_at m ob obl hm base (by omega) s2 hs2)
    let b1 := obl.take base ++ encodeLE 1 s2 ++ obl.drop (base + 1)
    let m1 := m.upd ob b1
    let s1s : State := {st with mem := m1}
    have hm1 : m1 ob = some b1 := by simp [m1]
    have hb1 : b1.length = obl.length := blk1_len obl base s2 (by omega)
    have haddr1 : EvE Gen.prog s1s (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 1)))) 1) (.ptr ob (0 + (base + 1) * 1)) :=
      EvE.index (EvE.var (show s1s.locals 0 = some (.ptr ob 0) from rfl))
        (EvE_u64_add_const (i := 1) (k := 1) (show s1s.locals 1 = some (.int u64 base) from rfl) (by omega) (by omega))
        (ptrAddN_ok hm1 (by rw [hb1]; omega))
    have hst1 : ExS Gen.prog s1s (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 1)))) 1) (.var 4)) .normal
        {s1s with mem := m1.upd ob (b1.take (base + 1) ++ encodeLE 1 s1 ++ b1.drop (base + 2))} :=
      ExS.store haddr1
        (EvE.var (show s1s.locals 4 = some (.int u8 s1) from rfl))
        (by rw [show s1s.ro = st.ro from rfl]; exact hSro)
        (store_byte_at m1 ob b1 hm1 (base + 1) (by rw [hb1]; omega) s1 hs1)
    let b2 := b1.take (base + 1) ++ encodeLE 1 s1 ++ b1.drop (base + 2)
    let m2 := m1.upd ob b2
    let s2s : State := {s1s with mem := m2}
    have hm2 : m2 ob = some b2 := by simp [m2]
    have hb2 : b2.length = obl.length := blk2_len obl base s2 s1 (by omega)
    have haddr2 : EvE Gen.prog s2s (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 2)))) 1) (.ptr ob (0 + (base + 2) * 1)) :=
      EvE.index (EvE.var (show s2s.locals 0 = some (.ptr ob 0) from rfl))
        (EvE_u64_add_const (i := 1) (k := 2) (show s2s.locals 1 = some (.int u64 base) from rfl) (by omega) (by omega))
        (ptrAddN_ok hm2 (by rw [hb2]; omega))
    have hst2 : ExS Gen.prog s2s (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 2)))) 1) (.var 3)) .normal
        {s2s with mem := m2.upd ob (b2.take (base + 2) ++ encodeLE 1 s0 ++ b2.drop (base + 3))} :=
      ExS.store haddr2
        (EvE.var (show s2s.locals 3 = some (.int u8 s0) from rfl))
        (by rw [show s2s.ro = st.ro from rfl]; exact hSro)
        (store_byte_at m2 ob b2 hm2 (base + 2) (by rw [hb2]; omega) s0 hs0)
    let b3 := b2.take (base + 2) ++ encodeLE 1 s0 ++ b2.drop (base + 3)
    let m3 := m2.upd ob b3
    let s3s : State := {s2s with mem := m3}
    have hm3 : m3 ob = some b3 := by simp [m3]
    have hb3 : b3.length = obl.length := blk3_len obl base s2 s1 s0 (by omega)
    have haddr3 : EvE Gen.prog s3s (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 3)))) 1) (.ptr ob (0 + (base + 3) * 1)) :=
      EvE.index (EvE.var (show s3s.locals 0 = some (.ptr ob 0) from rfl))
        (EvE_u64_add_const (i := 1) (k := 3) (show s3s.locals 1 = some (.int u64 base) from rfl) (by omega) (by omega))
        (ptrAddN_ok hm3 (by rw [hb3]; omega))
    have hst3 : ExS Gen.prog s3s (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 3)))) 1) (.var 6)) .normal
        {s3s with mem := m3.upd ob (b3.take (base + 3) ++ encodeLE 1 s3 ++ b3.drop (base + 4))} :=
      ExS.store haddr3
        (EvE.var (show s3s.locals 6 = some (.int u8 s3) from rfl))
        (by rw [show s3s.ro = st.ro from rfl]; exact hSro)
        (store_byte_at m3 ob b3 hm3 (base + 3) (by rw [hb3]; omega) s3 hs3)
    have hbody4 : ExS Gen.prog st (.seq (.ite (.bin .eq (some u32) (.cast u32 (.var 2)) (.const (.int u32 4))) (.seq (.store (.int u8) (.index (.var 0) (.var 1) 1) (.var 5)) (.seq (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 1)))) 1) (.var 4)) (.seq (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 2)))) 1) (.var 3)) (.seq (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 3)))) 1) (.var 6)) (.ret (some (.const (.int i32 1)))))))) .skip) (.ret (some (.const (.int i32 0))))) (.ret (some (.int i32 1))) {s3s with mem := m3.upd ob (b3.take (base + 3) ++ encodeLE 1 s3 ++ b3.drop (base + 4))} := by
      refine ExS.seq_ret ?_
      refine ExS.ite heq4 t_true_wp ?_
      exact ExS.seq hst0 (ExS.seq hst1 (ExS.seq hst2 (ExS.seq hst3 (ExS.ret (EvE.const _)))))
    refine ⟨{s3s with mem := m3.upd ob (b3.take (base + 3) ++ encodeLE 1 s3 ++ b3.drop (base + 4))}, ?_, ?_, ?_⟩
    · exact ExS.seq hskip1 (ExS.seq hskip3 hbody4)
    · dsimp only
      rw [Mem.upd_same]
      exact congrArg some (shape4 obl base s0 s1 s2 s3 hb hs0 hs1 hs2 hs3)
    · intro j hj; simp [Mem.upd, hj, s3s, s2s, s1s, m3, m2, m1]


/-- `ni_tga_write_pixel` failure refinement: a bad channel count returns 0
    and leaves memory untouched. -/
theorem ni_tga_write_pixel_bad_exs (m : Mem) (ob : Nat) (base : Nat)
    (channels s0 s1 s2 s3 : Nat) (hch : channels < 2 ^ 32)
    (hc1 : channels ≠ 1) (hc3 : channels ≠ 3) (hc4 : channels ≠ 4)
    (ro : Bool) (hro : ro = false) :
    ∃ s', ExS Gen.prog ⟨frameLocals [0,1,2,3,4,5,6]
        [.ptr ob 0, .int u64 base, .int u8 channels, .int u8 s0, .int u8 s1, .int u8 s2, .int u8 s3], m, ro⟩
      Gen.ni_tga_write_pixel.body (.ret (some (.int i32 0))) s' ∧ s'.mem = m := by
  let st : State := ⟨frameLocals [0,1,2,3,4,5,6]
      [.ptr ob 0, .int u64 base, .int u8 channels, .int u8 s0, .int u8 s1, .int u8 s2, .int u8 s3], m, ro⟩
  have l2 : st.locals 2 = some (.int u8 channels) := rfl
  have hcast : evalCast u32 (.int u8 channels) = .ok (.int u32 channels) := by
    simp [evalCast, IntTy.modulus, u8, u32, Nat.mod_eq_of_lt (by omega : channels < 2 ^ 32)]
  have mkEq (k : Nat) (hk : channels ≠ k) :
      EvE Gen.prog st (.bin .eq (some u32) (.cast u32 (.var 2)) (.const (.int u32 k))) (boolVal false) := by
    have h := ev_eq_u32_wp (EvE.cast (EvE.var l2) hcast) (EvE.const (v := .int u32 k))
    have hdec : decide (channels = k) = false := decide_eq_false_iff_not.mpr hk
    simpa [hdec] using h
  have heq1 := mkEq 1 hc1
  have heq3 := mkEq 3 hc3
  have heq4 := mkEq 4 hc4
  have hskip1 : ExS Gen.prog st (.ite (.bin .eq (some u32) (.cast u32 (.var 2)) (.const (.int u32 1))) (.seq (.store (.int u8) (.index (.var 0) (.var 1) 1) (.var 3)) (.ret (some (.const (.int i32 1))))) .skip) .normal st :=
    ExS.ite heq1 t_false_wp ExS.skip
  have hskip3 : ExS Gen.prog st (.ite (.bin .eq (some u32) (.cast u32 (.var 2)) (.const (.int u32 3))) (.seq (.store (.int u8) (.index (.var 0) (.var 1) 1) (.var 5)) (.seq (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 1)))) 1) (.var 4)) (.seq (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 2)))) 1) (.var 3)) (.ret (some (.const (.int i32 1))))))) .skip) .normal st :=
    ExS.ite heq3 t_false_wp ExS.skip
  have hskip4 : ExS Gen.prog st (.ite (.bin .eq (some u32) (.cast u32 (.var 2)) (.const (.int u32 4))) (.seq (.store (.int u8) (.index (.var 0) (.var 1) 1) (.var 5)) (.seq (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 1)))) 1) (.var 4)) (.seq (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 2)))) 1) (.var 3)) (.seq (.store (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 1) (.cast u64 (.const (.int u32 3)))) 1) (.var 6)) (.ret (some (.const (.int i32 1)))))))) .skip) .normal st :=
    ExS.ite heq4 t_false_wp ExS.skip
  have hret : ExS Gen.prog st (.ret (some (.const (.int i32 0)))) (.ret (some (.int i32 0))) st :=
    ExS.ret (EvE.const (v := .int i32 0))
  refine ⟨st, ?_, rfl⟩
  exact ExS.seq hskip1 (ExS.seq hskip3 (ExS.seq hskip4 hret))

end NANO.C.Proofs
