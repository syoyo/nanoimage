/-
  `ni_bmp_header_palette` — the 8-bit palette bounds stage of the BMP header,
  proved against `bmpOutputPaletteCode`. On success `palette_entries`@36 (u32)
  and `palette_offset`@16 (u64) are spliced into the block; on failure (code 10)
  the block is untouched.
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
set_option maxHeartbeats 800000

namespace NANO.C.Proofs
open NANO NANO.C

/-- Stage 4b of `ni_bmp_info` (C store order: palette_entries@36 first, then
    palette_offset@16). -/
def bmpPaletteBlock (obl : List UInt8) (po entries : Nat) : List UInt8 :=
  let s := obl.take 36 ++ encodeLE 4 entries ++ obl.drop 40
  s.take 16 ++ encodeLE 8 po ++ s.drop 24

theorem bmpPaletteBlock_length (obl : List UInt8) (h48 : obl.length = 48) (po entries : Nat) :
    (bmpPaletteBlock obl po entries).length = 48 := by
  have e4 : (encodeLE 4 entries).length = 4 := encodeLE_length 4 entries
  have e8 : (encodeLE 8 po).length = 8 := encodeLE_length 8 po
  simp [bmpPaletteBlock, h48, e4, e8, List.length_take, List.length_append, List.length_drop]

/-- Two stores (u32 @36, then u64 @16) into a 48-byte `ni_bmp_info` block.
    Exactly the common tail of `Gen.ni_bmp_header_palette.body`. -/
theorem bmp_palette_stores_exs (m : Mem) (obl : List UInt8) (hob : m 3 = some obl) (h48 : obl.length = 48)
    (ro : Bool) (hro : ro = false)
    (l : Locals) (hl4 : l 4 = some (.ptr 3 0))
    (po entries : Nat) (hpo : po < 18446744073709551616) (hentries : entries < 4294967296)
    (hl5 : l 5 = some (Val.int ⟨64, false⟩ entries)) (hl6 : l 6 = some (Val.int ⟨64, false⟩ po)) :
    ∃ s', ExS Gen.prog ⟨l, m, ro⟩
      (.seq (.store (.int ⟨32, false⟩) (.field (.var 4) 36) (.cast ⟨32, false⟩ (.var 5)))
            (.seq (.store (.int ⟨64, false⟩) (.field (.var 4) 16) (.var 6))
                  (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 0))))))
      (Outcome.ret (some (.int ⟨32, true⟩ 0))) s' ∧
    s'.mem 3 = some (bmpPaletteBlock obl po entries) := by
  have h4 : EvE Gen.prog ⟨l, m, ro⟩ (.var 4) (.ptr 3 0) := EvE.var hl4
  have h5 : EvE Gen.prog ⟨l, m, ro⟩ (.var 5) (.int ⟨64, false⟩ entries) := EvE.var hl5
  have h6 : EvE Gen.prog ⟨l, m, ro⟩ (.var 6) (.int ⟨64, false⟩ po) := EvE.var hl6
  have hcap : EvE Gen.prog ⟨l, m, ro⟩ (.cast ⟨32, false⟩ (.var 5)) (.int ⟨32, false⟩ entries) :=
    EvE.cast h5 (u64_u32_trunc_cast entries hentries)
  have hr36 : EvE Gen.prog ⟨l, m, ro⟩ (.field (.var 4) 36) (.ptr 3 36) :=
    EvE.field h4 (ptrAddN_ok hob (by omega))
  have hS1 : ExS Gen.prog ⟨l, m, ro⟩ (.store (.int ⟨32, false⟩) (.field (.var 4) 36) (.cast ⟨32, false⟩ (.var 5))) .normal
      { locals := l, mem := m.upd 3 (obl.take 36 ++ encodeLE 4 entries ++ obl.drop 40), ro := ro } :=
    ExS.store hr36 hcap hro (store_field_u32 m 3 obl hob h48 36 (by omega) entries hentries)
  let b1 : List UInt8 := obl.take 36 ++ encodeLE 4 entries ++ obl.drop 40
  have hb1 : b1.length = 48 := by
    simp [b1, h48, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have h2m1 : (m.upd 3 b1) 3 = some b1 := rfl
  let s1 : State := { locals := l, mem := m.upd 3 b1, ro := ro }
  have h4s : EvE Gen.prog s1 (.var 4) (.ptr 3 0) := EvE.var hl4
  have h6s : EvE Gen.prog s1 (.var 6) (.int ⟨64, false⟩ po) := EvE.var hl6
  have hr16 : EvE Gen.prog s1 (.field (.var 4) 16) (.ptr 3 16) :=
    EvE.field h4s (ptrAddN_ok h2m1 (by omega))
  have hS2 : ExS Gen.prog s1 (.store (.int ⟨64, false⟩) (.field (.var 4) 16) (.var 6)) .normal
      { s1 with mem := (m.upd 3 b1).upd 3 (b1.take 16 ++ encodeLE 8 po ++ b1.drop 24) } :=
    ExS.store hr16 h6s hro (store_field_u64 (m.upd 3 b1) 3 b1 h2m1 hb1 16 (by omega) po hpo)
  let b2 : List UInt8 := b1.take 16 ++ encodeLE 8 po ++ b1.drop 24
  have hb2 : b2.length = 48 := by
    simp [b2, hb1, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have h2m2 : ((m.upd 3 b1).upd 3 b2) 3 = some b2 := rfl
  let s2 : State := { s1 with mem := (m.upd 3 b1).upd 3 b2 }
  have hret : ExS Gen.prog s2 (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 0))))
      (Outcome.ret (some (.int ⟨32, true⟩ 0))) s2 :=
    ExS.ret (EvE.const (v := (.int ⟨32, true⟩ 0)))
  have hblk : b2 = bmpPaletteBlock obl po entries := by
    have e4 : (encodeLE 4 entries).length = 4 := encodeLE_length 4 entries
    have e8 : (encodeLE 8 po).length = 8 := encodeLE_length 8 po
    simp [bmpPaletteBlock, b1, b2, h48, e4, e8, encodeLE_length, List.take_append, List.drop_append,
          List.take_left', List.drop_left', List.take_take, List.drop_drop, List.nil_append,
          List.append_nil]
  have hfin : ((m.upd 3 b1).upd 3 b2) = m.upd 3 (bmpPaletteBlock obl po entries) := by
    rw [mem_upd_same, hblk]
  refine ⟨s2, ExS.seq hS1 (ExS.seq hS2 hret), ?_⟩
  show s2.mem 3 = some (bmpPaletteBlock obl po entries)
  rw [show s2.mem = ((m.upd 3 b1).upd 3 b2) from rfl, hfin]
  rfl


/-- The `mid` statement of the 8-bit palette path: `palette_offset` set, then
    the bounds check. Kept as a literal copy of the subterm of
    `Gen.ni_bmp_header_palette.body`. -/
def ni_bmp_header_palette_mid : Stmt :=
  (.seq (.set 6 (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 14))) (.cast ⟨64, false⟩ (.var 2))))
    (.ite (.lor (.lor (.bin .eq (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
                (.bin .gt (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
           (.bin .gt (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 6) (.bin .mul (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.var 3))))
          (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 10)))) .skip))

/-- The bounds-check part of the 8-bit palette path: returns either the
    `ret 10` outcome (bounds violated) or the falling-through `.normal` state
    carrying `palette_offset = 14 + dibSize`. Both outcomes carry the
    corresponding evidence for `bmpOutputPaletteCode`. -/
theorem palette_mid (m : Mem) (s : State) (obl : List UInt8)
    (hBC : bitCount = 8)
    (entries : Nat) (hEnt : (if colorsUsed = 0 then 256 else colorsUsed) = entries)
    (hE : entries < 4294967296)
    (hCU : colorsUsed < 4294967296) (hD : dibSize < 4294967296) (hP : pixelOffset < 4294967296)
    (hob : s.mem 3 = some obl) (h48 : obl.length = 48) (hro : s.ro = false)
    (hl1 : s.locals 1 = some (.int ⟨32, false⟩ colorsUsed))
    (hl2 : s.locals 2 = some (.int ⟨32, false⟩ dibSize))
    (hl3 : s.locals 3 = some (.int ⟨32, false⟩ pixelOffset))
    (hl4 : s.locals 4 = some (.ptr 3 0))
    (hl5 : s.locals 5 = some (.int ⟨64, false⟩ entries)) :
    (∃ hBad : (entries = 0 ∨ entries > 256 ∨ (14 + dibSize) + entries * 4 > pixelOffset), ∃ s',
        ExS Gen.prog s ni_bmp_header_palette_mid (Outcome.ret (some (.int ⟨32, true⟩ 10))) s') ∨
    (∃ hNotBad : ¬ (entries = 0 ∨ entries > 256 ∨ (14 + dibSize) + entries * 4 > pixelOffset), ∃ s6,
        ExS Gen.prog s ni_bmp_header_palette_mid .normal s6 ∧
        s6.locals 4 = s.locals 4 ∧ s6.locals 5 = s.locals 5 ∧
        s6.locals 6 = some (.int ⟨64, false⟩ (14 + dibSize)) ∧ s6.mem = s.mem ∧ s6.ro = s.ro) := by
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  classical
  have h14 : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 14))) (.int ⟨64, false⟩ 14) :=
    EvE.cast (EvE.const _) (i32_u64_cast_small 14 (by decide))
  have h2c : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 2)) (.int ⟨64, false⟩ dibSize) :=
    EvE.cast (EvE.var hl2) (u32_u64_cast dibSize (by omega))
  have hadd : EvE Gen.prog s
      (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 14))) (.cast ⟨64, false⟩ (.var 2)))
      (.int ⟨64, false⟩ (14 + dibSize)) :=
    EvE.bin h14 h2c (bin_u64_add 14 dibSize (by omega))
  have hSet6 : ExS Gen.prog s
      (.set 6 (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 14))) (.cast ⟨64, false⟩ (.var 2))))
      .normal { s with locals := s.locals.upd 6 (.int ⟨64, false⟩ (14 + dibSize)) } :=
    ExS.set hadd
  let s2 : State := { s with locals := s.locals.upd 6 (.int ⟨64, false⟩ (14 + dibSize)) }
  have hl4_2 : s2.locals 4 = some (.ptr 3 0) := by
    show s2.locals 4 = some (.ptr 3 0)
    have : s.locals 4 = some (.ptr 3 0) := hl4
    simp [s2, Locals.upd, this]
  have hl5_2 : s2.locals 5 = some (.int ⟨64, false⟩ entries) := by
    show s2.locals 5 = some (.int ⟨64, false⟩ entries)
    have : s.locals 5 = some (.int ⟨64, false⟩ entries) := hl5
    simp [s2, Locals.upd, this]
  have hl6_2 : s2.locals 6 = some (.int ⟨64, false⟩ (14 + dibSize)) := rfl
  have hl3_2 : s2.locals 3 = some (.int ⟨32, false⟩ pixelOffset) := by
    show s2.locals 3 = some (.int ⟨32, false⟩ pixelOffset)
    have : s.locals 3 = some (.int ⟨32, false⟩ pixelOffset) := hl3
    simp [s2, Locals.upd, this]
  have hne0 : entries ≠ 0 := by
    rw [← hEnt]
    by_cases h : colorsUsed = 0 <;> simp [h]
  -- c1: entries == 0 (always false)
  have hC1 : EvE Gen.prog s2
      (.bin .eq (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
      (boolVal false) := by
    have hc : EvE Gen.prog s2 (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))) (.int ⟨64, false⟩ 0) :=
      EvE.cast (EvE.const _) (u32_u64_cast 0 (by decide))
    have he : EvE Gen.prog s2
        (.bin .eq (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
        (boolVal (decide (entries = 0))) :=
      EvE.bin (EvE.var hl5_2) hc (bin_u64_eq entries 0)
    rw [decide_eq_false_iff_not.mpr hne0] at he
    exact he
  have hC2_full : EvE Gen.prog s2
      (.bin .gt (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256))))
      (boolVal (decide (entries > 256))) := by
    have hc : EvE Gen.prog s2 (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256))) (.int ⟨64, false⟩ 256) :=
      EvE.cast (EvE.const _) (u32_u64_cast 256 (by decide))
    exact EvE.bin (EvE.var hl5_2) hc (bin_u64_gt entries 256)
  have hmul : EvE Gen.prog s2
      (.bin .mul (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))
      (.int ⟨64, false⟩ (entries * 4)) := by
    have hc : EvE Gen.prog s2 (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))) (.int ⟨64, false⟩ 4) :=
      EvE.cast (EvE.const _) (u32_u64_cast 4 (by decide))
    exact EvE.bin (EvE.var hl5_2) hc (bin_u64_mul entries 4 (by omega))
  have hadd2 : EvE Gen.prog s2
      (.bin .add (some ⟨64, false⟩) (.var 6)
        (.bin .mul (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))))
      (.int ⟨64, false⟩ ((14 + dibSize) + entries * 4)) :=
    EvE.bin (EvE.var hl6_2) hmul (bin_u64_add (14 + dibSize) (entries * 4) (by omega))
  have hpoc : EvE Gen.prog s2 (.cast ⟨64, false⟩ (.var 3)) (.int ⟨64, false⟩ pixelOffset) :=
    EvE.cast (EvE.var hl3_2) (u32_u64_cast pixelOffset (by omega))
  have hC3_full : EvE Gen.prog s2
      (.bin .gt (some ⟨64, false⟩)
        (.bin .add (some ⟨64, false⟩) (.var 6)
          (.bin .mul (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))))
        (.cast ⟨64, false⟩ (.var 3)))
      (boolVal (decide ((14 + dibSize) + entries * 4 > pixelOffset))) :=
    EvE.bin hadd2 hpoc (bin_u64_gt ((14 + dibSize) + entries * 4) pixelOffset)
  by_cases hC2 : entries > 256
  · -- fires via c2 (regardless of c3)
    have hC2t : EvE Gen.prog s2
        (.bin .gt (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256))))
        (boolVal true) := by
      rw [decide_eq_true_eq.mpr hC2] at hC2_full; exact hC2_full
    have hr1 : EvE Gen.prog s2
        (.lor (.bin .eq (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
              (.bin .gt (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
        (boolVal true) :=
      EvE.lor_false hC1 truthy_false hC2t truthy_true
    have hr2 : EvE Gen.prog s2
        (.lor (.lor (.bin .eq (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
                    (.bin .gt (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
              (.bin .gt (some ⟨64, false⟩)
                (.bin .add (some ⟨64, false⟩) (.var 6)
                  (.bin .mul (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))))
                (.cast ⟨64, false⟩ (.var 3))))
        (boolVal true) :=
      EvE.lor_true hr1 truthy_true
    exact Or.inl ⟨Or.inr (Or.inl hC2), s2, ExS.seq hSet6
      (ExS.ite hr2 truthy_true (ExS.ret (EvE.const _)))⟩
  · by_cases hC3 : (14 + dibSize) + entries * 4 > pixelOffset
    · -- fires with c2 false, c3 true
      have hC2f : EvE Gen.prog s2
          (.bin .gt (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256))))
          (boolVal false) := by
        rw [decide_eq_false_iff_not.mpr hC2] at hC2_full; exact hC2_full
      have hC3t : EvE Gen.prog s2
          (.bin .gt (some ⟨64, false⟩)
            (.bin .add (some ⟨64, false⟩) (.var 6)
              (.bin .mul (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))))
            (.cast ⟨64, false⟩ (.var 3)))
          (boolVal true) := by
        rw [decide_eq_true_eq.mpr hC3] at hC3_full; exact hC3_full
      have hr1 : EvE Gen.prog s2
          (.lor (.bin .eq (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
                (.bin .gt (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
          (boolVal false) :=
        EvE.lor_false hC1 truthy_false hC2f truthy_false
      have hr2 : EvE Gen.prog s2
          (.lor (.lor (.bin .eq (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
                      (.bin .gt (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
                (.bin .gt (some ⟨64, false⟩)
                  (.bin .add (some ⟨64, false⟩) (.var 6)
                    (.bin .mul (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))))
                  (.cast ⟨64, false⟩ (.var 3))))
          (boolVal true) :=
        EvE.lor_false hr1 truthy_false hC3t truthy_true
      exact Or.inl ⟨Or.inr (Or.inr hC3), s2, ExS.seq hSet6
        (ExS.ite hr2 truthy_true (ExS.ret (EvE.const _)))⟩
    · -- no bounds violation: fall through
      have hC2f : EvE Gen.prog s2
          (.bin .gt (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256))))
          (boolVal false) := by
        rw [decide_eq_false_iff_not.mpr hC2] at hC2_full; exact hC2_full
      have hC3f : EvE Gen.prog s2
          (.bin .gt (some ⟨64, false⟩)
            (.bin .add (some ⟨64, false⟩) (.var 6)
              (.bin .mul (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))))
            (.cast ⟨64, false⟩ (.var 3)))
          (boolVal false) := by
        rw [decide_eq_false_iff_not.mpr hC3] at hC3_full; exact hC3_full
      have hr1 : EvE Gen.prog s2
          (.lor (.bin .eq (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
                (.bin .gt (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
          (boolVal false) :=
        EvE.lor_false hC1 truthy_false hC2f truthy_false
      have hr2 : EvE Gen.prog s2
          (.lor (.lor (.bin .eq (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
                      (.bin .gt (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
                (.bin .gt (some ⟨64, false⟩)
                  (.bin .add (some ⟨64, false⟩) (.var 6)
                    (.bin .mul (some ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))))
                  (.cast ⟨64, false⟩ (.var 3))))
          (boolVal false) :=
        EvE.lor_false hr1 truthy_false hC3f truthy_false
      have hNotBad : ¬ (entries = 0 ∨ entries > 256 ∨ (14 + dibSize) + entries * 4 > pixelOffset) := by
        intro hbad
        rcases hbad with h1 | h2 | h3
        · exact hne0 h1
        · exact hC2 h2
        · exact hC3 h3
      exact Or.inr ⟨hNotBad, s2, ExS.seq hSet6 (ExS.ite hr2 truthy_false ExS.skip),
        rfl, rfl, hl6_2, rfl, rfl⟩

/-- Assemble the 8-bit branch: after `set 5`, run `palette_mid`; either
    `ret 10` fires or the common stores run. -/
theorem palette_case_exs (m : Mem) (s0 : State) (s1 : State)
    (hBC : bitCount = 8)
    (hEqT : EvE Gen.prog s0
      (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.const (.int ⟨32, false⟩ 8)))
      (boolVal true))
    (hSet5 : ExS Gen.prog s0
      (.set 5 (.cond (.bin .ne (some ⟨32, false⟩) (.var 1) (.const (.int ⟨32, false⟩ 0)))
             (.cast ⟨64, false⟩ (.var 1)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
      .normal s1)
    (entries : Nat)
    (hEnt : (if colorsUsed = 0 then 256 else colorsUsed) = entries)
    (hmid :
      (∃ hBad : (entries = 0 ∨ entries > 256 ∨ (14 + dibSize) + entries * 4 > pixelOffset), ∃ s',
          ExS Gen.prog s1 ni_bmp_header_palette_mid (Outcome.ret (some (.int ⟨32, true⟩ 10))) s') ∨
      (∃ hNotBad : ¬ (entries = 0 ∨ entries > 256 ∨ (14 + dibSize) + entries * 4 > pixelOffset), ∃ s6,
          ExS Gen.prog s1 ni_bmp_header_palette_mid .normal s6 ∧
          s6.locals 4 = s1.locals 4 ∧ s6.locals 5 = s1.locals 5 ∧
          s6.locals 6 = some (.int ⟨64, false⟩ (14 + dibSize)) ∧ s6.mem = s1.mem ∧ s6.ro = s1.ro))
    (obl : List UInt8) (hob : m 3 = some obl) (h48 : obl.length = 48)
    (hro : s0.ro = false) (hro1 : s1.ro = false)
    (hl4_1 : s1.locals 4 = some (.ptr 3 0))
    (hl5_1 : s1.locals 5 = some (.int ⟨64, false⟩ entries))
    (hCU : colorsUsed < 4294967296) (hD : dibSize < 4294967296)
    (hob1 : s1.mem 3 = some obl) :
    ∃ s', ExS Gen.prog s0 Gen.ni_bmp_header_palette.body
      (.ret (some (.int ⟨32, true⟩ (bmpOutputPaletteCode bitCount colorsUsed dibSize pixelOffset)))) s' ∧
    (bmpOutputPaletteCode bitCount colorsUsed dibSize pixelOffset = 0 →
      s'.mem 3 = some (bmpPaletteBlock obl
        (if bitCount = 8 then 14 + dibSize else 0)
        (if bitCount = 8 then (if colorsUsed = 0 then 256 else colorsUsed) else 0))) := by
  have hE : entries < 4294967296 := by
    rw [← hEnt]
    by_cases h : colorsUsed = 0
    · simp [h]
    · simp [h]
      omega
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  classical
  cases hmid with
  | inl hFire =>
    obtain ⟨hBad, s', hMid⟩ := hFire
    have hSpec : bmpOutputPaletteCode bitCount colorsUsed dibSize pixelOffset = 10 := by
      simp [bmpOutputPaletteCode, hBC, hEnt, hBad]
    refine ⟨s', ?_, fun hc => by rw [hSpec] at hc; exact absurd hc (by decide)⟩
    show ExS Gen.prog s0 Gen.ni_bmp_header_palette.body
        (.ret (some (.int ⟨32, true⟩ (bmpOutputPaletteCode bitCount colorsUsed dibSize pixelOffset)))) s'
    rw [hSpec]
    exact ExS.seq_ret (ExS.ite hEqT truthy_true (ExS.seq hSet5 hMid))
  | inr hFall =>
    obtain ⟨hNotBad, s6, hMid, hl4_6, hl5_6, hl6_6, hmem6, hro6⟩ := hFall
    have hSpec : bmpOutputPaletteCode bitCount colorsUsed dibSize pixelOffset = 0 := by
      simp [bmpOutputPaletteCode, hBC, hEnt, hNotBad]
    have hITE : ExS Gen.prog s0
        (.ite (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.const (.int ⟨32, false⟩ 8)))
          (.seq (.set 5 (.cond (.bin .ne (some ⟨32, false⟩) (.var 1) (.const (.int ⟨32, false⟩ 0)))
                     (.cast ⟨64, false⟩ (.var 1)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
                ni_bmp_header_palette_mid)
          (.seq (.set 5 (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
                (.set 6 (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))))
        .normal s6 :=
      ExS.ite hEqT truthy_true (ExS.seq hSet5 hMid)
    have hl4_6' : s6.locals 4 = some (.ptr 3 0) := by rw [hl4_6]; exact hl4_1
    have hl5_6' : s6.locals 5 = some (.int ⟨64, false⟩ entries) := by rw [hl5_6]; exact hl5_1
    obtain ⟨s', hStores, hblk⟩ := bmp_palette_stores_exs s6.mem obl
      (by rw [hmem6]; exact hob1) h48 s6.ro (by rw [hro6]; exact hro1) s6.locals hl4_6'
      (14 + dibSize) entries (by omega) hE hl5_6' hl6_6
    refine ⟨s', ?_, ?_⟩
    · show ExS Gen.prog s0 Gen.ni_bmp_header_palette.body
          (.ret (some (.int ⟨32, true⟩ (bmpOutputPaletteCode bitCount colorsUsed dibSize pixelOffset)))) s'
      rw [hSpec]
      exact ExS.seq hITE hStores
    · intro _
      simpa [hBC, hEnt] using hblk

/-- `ni_bmp_header_palette` returns `bmpOutputPaletteCode`. -/
theorem ni_bmp_header_palette_exs (m : Mem)
    (bitCount colorsUsed dibSize pixelOffset : Nat)
    (hB : bitCount < 65536) (hCU : colorsUsed < 4294967296) (hD : dibSize < 4294967296)
    (hP : pixelOffset < 4294967296)
    (obl : List UInt8) (hob : m 3 = some obl) (h48 : obl.length = 48) (ro : Bool)
    (hro : ro = false) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals [0, 1, 2, 3, 4]
        [.int ⟨16, false⟩ bitCount, .int ⟨32, false⟩ colorsUsed, .int ⟨32, false⟩ dibSize,
         .int ⟨32, false⟩ pixelOffset, .ptr 3 0], m, ro⟩
      Gen.ni_bmp_header_palette.body
      (.ret (some (.int ⟨32, true⟩ (bmpOutputPaletteCode bitCount colorsUsed dibSize pixelOffset)))) s' ∧
    (bmpOutputPaletteCode bitCount colorsUsed dibSize pixelOffset = 0 →
      s'.mem 3 = some (bmpPaletteBlock obl
        (if bitCount = 8 then 14 + dibSize else 0)
        (if bitCount = 8 then (if colorsUsed = 0 then 256 else colorsUsed) else 0))) := by
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  let s0 : State :=
    ⟨frameLocals [0, 1, 2, 3, 4]
      [.int ⟨16, false⟩ bitCount, .int ⟨32, false⟩ colorsUsed, .int ⟨32, false⟩ dibSize,
       .int ⟨32, false⟩ pixelOffset, .ptr 3 0], m, ro⟩
  have hl0 : frameLocals [0, 1, 2, 3, 4]
      [.int ⟨16, false⟩ bitCount, .int ⟨32, false⟩ colorsUsed, .int ⟨32, false⟩ dibSize,
       .int ⟨32, false⟩ pixelOffset, .ptr 3 0] 0 = some (.int ⟨16, false⟩ bitCount) := rfl
  have hl1 : frameLocals [0, 1, 2, 3, 4]
      [.int ⟨16, false⟩ bitCount, .int ⟨32, false⟩ colorsUsed, .int ⟨32, false⟩ dibSize,
       .int ⟨32, false⟩ pixelOffset, .ptr 3 0] 1 = some (.int ⟨32, false⟩ colorsUsed) := rfl
  have hl2 : frameLocals [0, 1, 2, 3, 4]
      [.int ⟨16, false⟩ bitCount, .int ⟨32, false⟩ colorsUsed, .int ⟨32, false⟩ dibSize,
       .int ⟨32, false⟩ pixelOffset, .ptr 3 0] 2 = some (.int ⟨32, false⟩ dibSize) := rfl
  have hl3 : frameLocals [0, 1, 2, 3, 4]
      [.int ⟨16, false⟩ bitCount, .int ⟨32, false⟩ colorsUsed, .int ⟨32, false⟩ dibSize,
       .int ⟨32, false⟩ pixelOffset, .ptr 3 0] 3 = some (.int ⟨32, false⟩ pixelOffset) := rfl
  have hl4 : frameLocals [0, 1, 2, 3, 4]
      [.int ⟨16, false⟩ bitCount, .int ⟨32, false⟩ colorsUsed, .int ⟨32, false⟩ dibSize,
       .int ⟨32, false⟩ pixelOffset, .ptr 3 0] 4 = some (.ptr 3 0) := rfl
  -- ========== bitCount == 8? ==========
  have vc0 : EvE Gen.prog s0 (.cast ⟨32, false⟩ (.var 0)) (.int ⟨32, false⟩ bitCount) :=
    EvE.cast (EvE.var hl0) (u16_u32_cast bitCount (by omega))
  have hEq : EvE Gen.prog s0
      (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.const (.int ⟨32, false⟩ 8)))
      (boolVal (decide (bitCount = 8))) :=
    EvE.bin vc0 (EvE.const _) (bin_u32_eq bitCount 8)
  classical
  by_cases hBC : bitCount = 8
  · -- ========== 8-bit palette path ==========
    have hEqT : EvE Gen.prog s0
        (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.const (.int ⟨32, false⟩ 8)))
        (boolVal true) := by
      rw [decide_eq_true_eq.mpr hBC] at hEq; exact hEq
    have hcu_ne : EvE Gen.prog s0
        (.bin .ne (some ⟨32, false⟩) (.var 1) (.const (.int ⟨32, false⟩ 0)))
        (boolVal (decide (colorsUsed ≠ 0))) :=
      EvE.bin (EvE.var hl1) (EvE.const _) (bin_u32_ne colorsUsed 0)
    -- ========== entries selection ==========
    have v1c : EvE Gen.prog s0 (.cast ⟨64, false⟩ (.var 1)) (.int ⟨64, false⟩ colorsUsed) :=
      EvE.cast (EvE.var hl1) (u32_u64_cast colorsUsed (by omega))
    have v256c : EvE Gen.prog s0 (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256))) (.int ⟨64, false⟩ 256) :=
      EvE.cast (EvE.const _) (u32_u64_cast 256 (by decide))
    classical
    by_cases hCU0 : colorsUsed = 0
    · -- entries = 256
      have hne_f : EvE Gen.prog s0
          (.bin .ne (some ⟨32, false⟩) (.var 1) (.const (.int ⟨32, false⟩ 0)))
          (boolVal false) := by
        rw [decide_eq_false_iff_not.mpr (by omega)] at hcu_ne; exact hcu_ne
      have hCond : EvE Gen.prog s0
          (.cond (.bin .ne (some ⟨32, false⟩) (.var 1) (.const (.int ⟨32, false⟩ 0)))
                 (.cast ⟨64, false⟩ (.var 1)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256))))
          (.int ⟨64, false⟩ 256) :=
        EvE.cond hne_f truthy_false v256c
      have hSet5 : ExS Gen.prog s0
          (.set 5 (.cond (.bin .ne (some ⟨32, false⟩) (.var 1) (.const (.int ⟨32, false⟩ 0)))
                 (.cast ⟨64, false⟩ (.var 1)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
          .normal { s0 with locals := s0.locals.upd 5 (.int ⟨64, false⟩ 256) } :=
        ExS.set hCond
      let s1 : State := { s0 with locals := s0.locals.upd 5 (.int ⟨64, false⟩ 256) }
      have hEnt256 : (if colorsUsed = 0 then 256 else colorsUsed) = 256 := if_pos hCU0
      have hl1_1 : s1.locals 1 = some (.int ⟨32, false⟩ colorsUsed) := rfl
      have hl2_1 : s1.locals 2 = some (.int ⟨32, false⟩ dibSize) := rfl
      have hl3_1 : s1.locals 3 = some (.int ⟨32, false⟩ pixelOffset) := rfl
      have hl4_1 : s1.locals 4 = some (.ptr 3 0) := rfl
      have hl5_1 : s1.locals 5 = some (.int ⟨64, false⟩ 256) := rfl
      obtain h := palette_mid m s1 obl hBC 256 hEnt256 (by omega) hCU hD hP hob h48 hro
        hl1_1 hl2_1 hl3_1 hl4_1 hl5_1
      have hob1 : s1.mem 3 = some obl := hob
      exact palette_case_exs m s0 s1 hBC hEqT hSet5 256 hEnt256 h obl hob h48 hro hro hl4_1 hl5_1 hCU hD hob1
    · -- entries = colorsUsed
      have hne_t : EvE Gen.prog s0
          (.bin .ne (some ⟨32, false⟩) (.var 1) (.const (.int ⟨32, false⟩ 0)))
          (boolVal true) := by
        rw [decide_eq_true_eq.mpr hCU0] at hcu_ne; exact hcu_ne
      have hCond : EvE Gen.prog s0
          (.cond (.bin .ne (some ⟨32, false⟩) (.var 1) (.const (.int ⟨32, false⟩ 0)))
                 (.cast ⟨64, false⟩ (.var 1)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256))))
          (.int ⟨64, false⟩ colorsUsed) :=
        EvE.cond hne_t truthy_true v1c
      have hSet5 : ExS Gen.prog s0
          (.set 5 (.cond (.bin .ne (some ⟨32, false⟩) (.var 1) (.const (.int ⟨32, false⟩ 0)))
                 (.cast ⟨64, false⟩ (.var 1)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 256)))))
          .normal { s0 with locals := s0.locals.upd 5 (.int ⟨64, false⟩ colorsUsed) } :=
        ExS.set hCond
      let s1 : State := { s0 with locals := s0.locals.upd 5 (.int ⟨64, false⟩ colorsUsed) }
      have hEntCU : (if colorsUsed = 0 then 256 else colorsUsed) = colorsUsed := if_neg hCU0
      have hl1_1 : s1.locals 1 = some (.int ⟨32, false⟩ colorsUsed) := rfl
      have hl2_1 : s1.locals 2 = some (.int ⟨32, false⟩ dibSize) := rfl
      have hl3_1 : s1.locals 3 = some (.int ⟨32, false⟩ pixelOffset) := rfl
      have hl4_1 : s1.locals 4 = some (.ptr 3 0) := rfl
      have hl5_1 : s1.locals 5 = some (.int ⟨64, false⟩ colorsUsed) := rfl
      obtain h := palette_mid m s1 obl hBC colorsUsed hEntCU hCU hCU hD hP hob h48 hro
        hl1_1 hl2_1 hl3_1 hl4_1 hl5_1
      have hob1 : s1.mem 3 = some obl := hob
      exact palette_case_exs m s0 s1 hBC hEqT hSet5 colorsUsed hEntCU h obl hob h48 hro hro hl4_1 hl5_1 hCU hD hob1
  · -- ========== bitCount ≠ 8: entries = offset = 0 ==========
    have hEqF : EvE Gen.prog s0
        (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.const (.int ⟨32, false⟩ 8)))
        (boolVal false) := by
      rw [decide_eq_false_iff_not.mpr hBC] at hEq; exact hEq
    have hElse : ExS Gen.prog s0
        (.seq (.set 5 (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
              (.set 6 (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))))
        .normal { s0 with locals := (s0.locals.upd 5 (.int ⟨64, false⟩ 0)).upd 6 (.int ⟨64, false⟩ 0) } := by
      have h5 : EvE Gen.prog s0 (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))) (.int ⟨64, false⟩ 0) :=
        EvE.cast (EvE.const _) (u32_u64_cast 0 (by decide))
      have hSet5 : ExS Gen.prog s0
          (.set 5 (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
          .normal { s0 with locals := s0.locals.upd 5 (.int ⟨64, false⟩ 0) } :=
        ExS.set h5
      let s1 : State := { s0 with locals := s0.locals.upd 5 (.int ⟨64, false⟩ 0) }
      have h6 : EvE Gen.prog s1 (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))) (.int ⟨64, false⟩ 0) :=
        EvE.cast (EvE.const _) (u32_u64_cast 0 (by decide))
      have hSet6 : ExS Gen.prog s1
          (.set 6 (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
          .normal { s1 with locals := s1.locals.upd 6 (.int ⟨64, false⟩ 0) } :=
        ExS.set h6
      exact ExS.seq hSet5 hSet6
    have hSpec : bmpOutputPaletteCode bitCount colorsUsed dibSize pixelOffset = 0 := by
      unfold bmpOutputPaletteCode
      rw [if_neg hBC]
    let s1 : State := { s0 with locals := (s0.locals.upd 5 (.int ⟨64, false⟩ 0)).upd 6 (.int ⟨64, false⟩ 0) }
    have hl4_1 : s1.locals 4 = some (.ptr 3 0) := rfl
    have hl5_1 : s1.locals 5 = some (.int ⟨64, false⟩ 0) := rfl
    have hl6_1 : s1.locals 6 = some (.int ⟨64, false⟩ 0) := rfl
    obtain ⟨s', hStores, hblk⟩ := bmp_palette_stores_exs s1.mem obl hob h48 ro hro s1.locals hl4_1
      0 0 (by decide) (by decide) hl5_1 hl6_1
    refine ⟨s', ?_, ?_⟩
    · show ExS Gen.prog s0 Gen.ni_bmp_header_palette.body
          (.ret (some (.int ⟨32, true⟩ (bmpOutputPaletteCode bitCount colorsUsed dibSize pixelOffset)))) s'
      rw [hSpec]
      exact ExS.seq (ExS.ite hEqF truthy_false hElse) hStores
    · intro _
      simpa [hBC] using hblk
end NANO.C.Proofs
