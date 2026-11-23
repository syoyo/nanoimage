/-
  `ni_tga_header` output-size computation: the two `set 11` multiplies.
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Lemmas
import NANO.Spec
import NANO.Tga
import NANO.C.Proofs.Core
import NANO.C.Proofs.NiGeometryTail
import NANO.C.Proofs.NiTgaHeader
import NANO.C.Proofs.NiTgaHeaderBody
import NANO.C.Proofs.NiTgaHeaderStores
import NANO.C.Proofs.NiTgaHeaderSpecCode
import NANO.C.Proofs.NiTgaHeaderGates

set_option linter.unusedVariables false
set_option maxRecDepth 8000000
set_option maxHeartbeats 1600000

namespace NANO.C.Proofs
open NANO NANO.C

/-- `set 11 (width*height)` (with the overflow check passing). -/
theorem tgaMulW_exs (s : State) (ww hhv : Nat)
    (l6 : s.locals 6 = some (.int u16 ww)) (l7 : s.locals 7 = some (.int u16 hhv))
    (hww : ww < 65536) (hhh : hhv < 65536) (hm : sizeMulOK ww hhv = true) :
    ExS Gen.prog s tgaMulW .normal ⟨s.locals.upd 11 (.int u64 (ww * hhv)), s.mem, s.ro⟩ :=
  ExS.set (EvE.bin (EvE.cast (EvE.var l6) (u16_u64_cast ww hww))
    (EvE.cast (EvE.var l7) (u16_u64_cast hhv hhh))
    (bin_u64_mul ww hhv (sizeMulOK_mul_lt ww hhv hm)))

/-- `set 11 ((width*height)*channels)` (with the overflow check passing). -/
theorem tgaMulWC_exs (s : State) (osz ch : Nat)
    (l11 : s.locals 11 = some (.int u64 osz)) (l10 : s.locals 10 = some (.int u8 ch))
    (hosz : osz < 2 ^ 64) (hch : ch < 256) (hm : sizeMulOK osz ch = true) :
    ExS Gen.prog s tgaMulWC .normal ⟨s.locals.upd 11 (.int u64 (osz * ch)), s.mem, s.ro⟩ :=
  ExS.set (EvE.bin (EvE.var l11)
    (EvE.cast (EvE.var l10) (u8_u64_cast ch hch))
    (bin_u64_mul osz ch (sizeMulOK_mul_lt osz ch hm)))

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem tgaHeader_rest_exs (m : Mem) (d : List UInt8) (size : Nat) (obl : List UInt8)
    (hob : m 3 = some obl) (h32 : obl.length = 32) (ro : Bool) (hro : ro = false)
    (ch : Nat) (hch : ch < 256) (l : Locals)
    (l1 : l 1 = some (.int u64 size)) (l2 : l 2 = some (.ptr 3 0))
    (l3 : l 3 = some (.int u8 (byteAt d 0))) (l5 : l 5 = some (.int u8 (byteAt d 2)))
    (l6 : l 6 = some (.int u16 (rd16le d 12))) (l7 : l 7 = some (.int u16 (rd16le d 14)))
    (l9 : l 9 = some (.int u8 (byteAt d 17))) (l10 : l 10 = some (.int u8 ch))
    (hww : rd16le d 12 < 65536) (hhh : rd16le d 14 < 65536) (hid : byteAt d 0 < 256)
    (htype : byteAt d 2 < 256) (hde : byteAt d 17 < 256) (hdv : 18 + byteAt d 0 < 2 ^ 64)
    (hok_cond : ¬ (18 + byteAt d 0 > size) →
      sizeMulOK (rd16le d 12) (rd16le d 14) = true →
      sizeMulOK (rd16le d 12 * rd16le d 14) ch = true →
      tgaHeader size d = .ok
      { outputSize := rd16le d 12 * rd16le d 14 * ch, dataOffset := 18 + byteAt d 0,
        width := rd16le d 12, height := rd16le d 14, channels := ch,
        rle := if byteAt d 2 = 10 ∨ byteAt d 2 = 11 then 1 else 0,
        topOrigin := if byteAt d 17 &&& 0x20 ≠ 0 then 1 else 0,
        rightOrigin := if byteAt d 17 &&& 0x10 ≠ 0 then 1 else 0 })
    (hs_id : 18 + byteAt d 0 > size → tgaHeader size d = .error 6)
    (hs_m1 : ¬ (18 + byteAt d 0 > size) → sizeMulOK (rd16le d 12) (rd16le d 14) = false → tgaHeader size d = .error 7)
    (hs_m2 : ¬ (18 + byteAt d 0 > size) → sizeMulOK (rd16le d 12) (rd16le d 14) = true → sizeMulOK (rd16le d 12 * rd16le d 14) ch = false → tgaHeader size d = .error 7) :
    ∃ s', ExS Gen.prog (⟨l, m, ro⟩ : State)
        (.seq tgaIdBad (.seq tgaMulBad1 (.seq tgaMulW (.seq tgaMulBad2 (.seq tgaMulWC tgaStores)))))
        (.ret (some (.int i32 (tgaHeaderCode size d)))) s' ∧
      (∀ j, j ≠ 3 → s'.mem j = m j) ∧
      (match tgaHeader size d with
       | .ok h => s'.mem 3 = some (tgaHeaderBlock obl h)
       | .error _ => True) := by
  have x_tt : truthy (boolVal true) = .ok true := truthy_boolVal true
  have x_tf : truthy (boolVal false) = .ok false := truthy_boolVal false
  have evId := ev_tga_id (⟨l, m, ro⟩ : State) size (byteAt d 0) l1 l3 hid hdv
  by_cases hidg : 18 + byteAt d 0 > size
  · have hB : decide (18 + byteAt d 0 > size) = true := decide_eq_true_eq.mpr hidg
    rw [hB] at evId
    have hite : ExS Gen.prog (⟨l, m, ro⟩ : State) tgaIdBad (.ret (some (.int i32 6))) (⟨l, m, ro⟩ : State) :=
      ExS.ite evId x_tt (ExS.ret (EvE.const (v := .int i32 6)))
    have hc : tgaHeaderCode size d = 6 := by unfold tgaHeaderCode; rw [hs_id hidg]
    refine ⟨⟨l, m, ro⟩, ?_, (fun j _ => rfl), ?_⟩
    · rw [hc]; exact ExS.seq_ret hite
    · simp only [hs_id hidg]
  · have hB : decide (18 + byteAt d 0 > size) = false := decide_eq_false_iff_not.mpr hidg
    rw [hB] at evId
    have hskipId : ExS Gen.prog (⟨l, m, ro⟩ : State) tgaIdBad .normal (⟨l, m, ro⟩ : State) :=
      ExS.ite evId x_tf ExS.skip
    have evM1 := ev_tga_mul1 (⟨l, m, ro⟩ : State) (rd16le d 12) (rd16le d 14) l6 l7 hww hhh
    by_cases hm1 : sizeMulOK (rd16le d 12) (rd16le d 14) = true
    · have hB1 : (! sizeMulOK (rd16le d 12) (rd16le d 14)) = false := by rw [hm1]; rfl
      rw [hB1] at evM1
      have hskipM1 : ExS Gen.prog (⟨l, m, ro⟩ : State) tgaMulBad1 .normal (⟨l, m, ro⟩ : State) :=
        ExS.ite evM1 x_tf ExS.skip
      have hMW := tgaMulW_exs (⟨l, m, ro⟩ : State) (rd16le d 12) (rd16le d 14) l6 l7 hww hhh hm1
      let lM1 : Locals := l.upd 11 (.int u64 (rd16le d 12 * rd16le d 14))
      have lM1_10 : lM1 10 = some (.int u8 ch) := by
        simp only [lM1, Locals.upd_ne]; exact l10
      have lM1_11 : lM1 11 = some (.int u64 (rd16le d 12 * rd16le d 14)) := by
        dsimp only [lM1]; exact Locals.upd_same l 11 _
      have evM2 := ev_tga_mul2 (⟨lM1, m, ro⟩ : State) (rd16le d 12 * rd16le d 14) ch
        lM1_11 lM1_10 (sizeMulOK_mul_lt _ _ hm1) hch
      by_cases hm2 : sizeMulOK (rd16le d 12 * rd16le d 14) ch = true
      · have hB2 : (! sizeMulOK (rd16le d 12 * rd16le d 14) ch) = false := by rw [hm2]; rfl
        rw [hB2] at evM2
        have hskipM2 : ExS Gen.prog (⟨lM1, m, ro⟩ : State) tgaMulBad2 .normal (⟨lM1, m, ro⟩ : State) :=
          ExS.ite evM2 x_tf ExS.skip
        have hMWC := tgaMulWC_exs (⟨lM1, m, ro⟩ : State) (rd16le d 12 * rd16le d 14) ch
          lM1_11 lM1_10 (sizeMulOK_mul_lt _ _ hm1) hch hm2
        let lB : Locals := lM1.upd 11 (.int u64 ((rd16le d 12 * rd16le d 14) * ch))
        have lB2 : lB 2 = some (.ptr 3 0) := by
          simp only [lB, lM1, Locals.upd_ne]; exact l2
        have lB3 : lB 3 = some (.int u8 (byteAt d 0)) := by
          simp only [lB, lM1, Locals.upd_ne]; exact l3
        have lB5 : lB 5 = some (.int u8 (byteAt d 2)) := by
          simp only [lB, lM1, Locals.upd_ne]; exact l5
        have lB6 : lB 6 = some (.int u16 (rd16le d 12)) := by
          simp only [lB, lM1, Locals.upd_ne]; exact l6
        have lB7 : lB 7 = some (.int u16 (rd16le d 14)) := by
          simp only [lB, lM1, Locals.upd_ne]; exact l7
        have lB9 : lB 9 = some (.int u8 (byteAt d 17)) := by
          simp only [lB, lM1, Locals.upd_ne]; exact l9
        have lB10 : lB 10 = some (.int u8 ch) := by
          simp only [lB, lM1, Locals.upd_ne]; exact l10
        have lB11 : lB 11 = some (.int u64 ((rd16le d 12 * rd16le d 14) * ch)) := by
          dsimp only [lB]; exact Locals.upd_same lM1 11 _
        have e16 : ∀ mm, EvE Gen.prog (⟨lB, mm, ro⟩ : State) (.cast u32 (.var 6)) (.int u32 (rd16le d 12)) :=
          fun _ => EvE.cast (EvE.var lB6) (u16_u32_cast _ hww)
        have e20 : ∀ mm, EvE Gen.prog (⟨lB, mm, ro⟩ : State) (.cast u32 (.var 7)) (.int u32 (rd16le d 14)) :=
          fun _ => EvE.cast (EvE.var lB7) (u16_u32_cast _ hhh)
        have e24 : ∀ mm, EvE Gen.prog (⟨lB, mm, ro⟩ : State) (.var 10) (.int u8 ch) :=
          fun _ => EvE.var lB10
        have e25 : ∀ mm, EvE Gen.prog (⟨lB, mm, ro⟩ : State)
            (.cast u8 (.lor (.bin .eq (some u32) (.cast u32 (.var 5)) (.const (.int u32 10)))
                             (.bin .eq (some u32) (.cast u32 (.var 5)) (.const (.int u32 11)))))
            (.int u8 (if byteAt d 2 = 10 ∨ byteAt d 2 = 11 then 1 else 0)) :=
          fun mm => ev_tga_rle (⟨lB, mm, ro⟩ : State) (byteAt d 2) lB5 htype
        have e26 : ∀ mm, EvE Gen.prog (⟨lB, mm, ro⟩ : State)
            (.cast u8 (.bin .ne (some u32) (.bin .band (some u32) (.cast u32 (.var 9)) (.const (.int u32 32))) (.const (.int u32 0))))
            (.int u8 (if byteAt d 17 &&& 0x20 ≠ 0 then 1 else 0)) :=
          fun mm => ev_tga_top (⟨lB, mm, ro⟩ : State) (byteAt d 17) lB9 hde
        have e27 : ∀ mm, EvE Gen.prog (⟨lB, mm, ro⟩ : State)
            (.cast u8 (.bin .ne (some u32) (.bin .band (some u32) (.cast u32 (.var 9)) (.const (.int u32 16))) (.const (.int u32 0))))
            (.int u8 (if byteAt d 17 &&& 0x10 ≠ 0 then 1 else 0)) :=
          fun mm => ev_tga_right (⟨lB, mm, ro⟩ : State) (byteAt d 17) lB9 hde
        have e8 : ∀ mm, EvE Gen.prog (⟨lB, mm, ro⟩ : State)
            (.bin .add (some u64) (.cast u64 (.const (.int i32 18))) (.cast u64 (.var 3))) (.int u64 (18 + byteAt d 0)) :=
          fun _ => EvE.bin (EvE.cast (EvE.const _) (i32_u64_cast 18 (by omega)))
            (EvE.cast (EvE.var lB3) (u8_u64_cast _ hid)) (bin_u64_add 18 (byteAt d 0) hdv)
        have e0 : ∀ mm, EvE Gen.prog (⟨lB, mm, ro⟩ : State) (.var 11) (.int u64 ((rd16le d 12 * rd16le d 14) * ch)) :=
          fun _ => EvE.var lB11
        obtain ⟨sS, hStores, hSmem, hSblk⟩ := tgaStores_exs m obl hob h32
          (rd16le d 12) (rd16le d 14) ch
          (if byteAt d 2 = 10 ∨ byteAt d 2 = 11 then 1 else 0)
          (if byteAt d 17 &&& 0x20 ≠ 0 then 1 else 0)
          (if byteAt d 17 &&& 0x10 ≠ 0 then 1 else 0)
          (byteAt d 0) ((rd16le d 12 * rd16le d 14) * ch)
          hww hhh hch (by split <;> omega) (by split <;> omega) (by split <;> omega)
          hid (sizeMulOK_mul_lt (rd16le d 12 * rd16le d 14) ch hm2) hdv ro hro lB lB2 lB6 lB7 lB10 lB11 lB3
          e16 e20 e24 e25 e26 e27 e8 e0
        have hok := hok_cond hidg hm1 hm2
        have hc : tgaHeaderCode size d = 0 := by unfold tgaHeaderCode; rw [hok]
        refine ⟨sS, ?_, hSblk, ?_⟩
        · rw [hc]
          exact ExS.seq hskipId (ExS.seq hskipM1 (ExS.seq hMW (ExS.seq hskipM2 (ExS.seq hMWC hStores))))
        · simp only [hok]; exact hSmem
      · have hm2f : sizeMulOK (rd16le d 12 * rd16le d 14) ch = false := by
          cases h : sizeMulOK (rd16le d 12 * rd16le d 14) ch <;> simp_all
        have hB2 : (! sizeMulOK (rd16le d 12 * rd16le d 14) ch) = true := by rw [hm2f]; rfl
        rw [hB2] at evM2
        have hite : ExS Gen.prog (⟨lM1, m, ro⟩ : State) tgaMulBad2 (.ret (some (.int i32 7))) (⟨lM1, m, ro⟩ : State) :=
          ExS.ite evM2 x_tt (ExS.ret (EvE.const (v := .int i32 7)))
        have hc : tgaHeaderCode size d = 7 := by unfold tgaHeaderCode; rw [hs_m2 hidg hm1 hm2f]
        refine ⟨⟨lM1, m, ro⟩, ?_, (fun j _ => rfl), ?_⟩
        · rw [hc]
          exact ExS.seq hskipId (ExS.seq hskipM1 (ExS.seq hMW (ExS.seq_ret hite)))
        · simp only [hs_m2 hidg hm1 hm2f]
    · have hm1f : sizeMulOK (rd16le d 12) (rd16le d 14) = false := by
        cases h : sizeMulOK (rd16le d 12) (rd16le d 14) <;> simp_all
      have hB1 : (! sizeMulOK (rd16le d 12) (rd16le d 14)) = true := by rw [hm1f]; rfl
      rw [hB1] at evM1
      have hite : ExS Gen.prog (⟨l, m, ro⟩ : State) tgaMulBad1 (.ret (some (.int i32 7))) (⟨l, m, ro⟩ : State) :=
        ExS.ite evM1 x_tt (ExS.ret (EvE.const (v := .int i32 7)))
      have hc : tgaHeaderCode size d = 7 := by unfold tgaHeaderCode; rw [hs_m1 hidg hm1f]
      refine ⟨⟨l, m, ro⟩, ?_, (fun j _ => rfl), ?_⟩
      · rw [hc]; exact ExS.seq hskipId (ExS.seq_ret hite)
      · simp only [hs_m1 hidg hm1f]

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem tgaHeader_tail_exs (m : Mem) (d : List UInt8) (size : Nat) (obl : List UInt8)
    (hob : m 3 = some obl) (h32 : obl.length = 32) (ro : Bool) (hro : ro = false)
    (hsz : ¬ size < 18) (l : Locals)
    (l1 : l 1 = some (.int u64 size)) (l2 : l 2 = some (.ptr 3 0))
    (l3 : l 3 = some (.int u8 (byteAt d 0))) (l4 : l 4 = some (.int u8 (byteAt d 1)))
    (l5 : l 5 = some (.int u8 (byteAt d 2))) (l6 : l 6 = some (.int u16 (rd16le d 12)))
    (l7 : l 7 = some (.int u16 (rd16le d 14))) (l8 : l 8 = some (.int u8 (byteAt d 16)))
    (l9 : l 9 = some (.int u8 (byteAt d 17))) :
    ∃ s', ExS Gen.prog (⟨l, m, ro⟩ : State) tgaTail
        (.ret (some (.int i32 (tgaHeaderCode size d)))) s' ∧
      (∀ j, j ≠ 3 → s'.mem j = m j) ∧
      (match tgaHeader size d with
       | .ok h => s'.mem 3 = some (tgaHeaderBlock obl h)
       | .error _ => True) := by
  have x_tt : truthy (boolVal true) = .ok true := truthy_boolVal true
  have x_tf : truthy (boolVal false) = .ok false := truthy_boolVal false
  have hww := rd16le_lt d 12
  have hhh := rd16le_lt d 14
  have hid := byteAt_lt d 0
  have hb1 := byteAt_lt d 1
  have hb2 := byteAt_lt d 2
  have hpd := byteAt_lt d 16
  have hde := byteAt_lt d 17
  have evD := ev_tga_dims (⟨l, m, ro⟩ : State) (rd16le d 12) (rd16le d 14) l6 l7 hww hhh
  by_cases hdim : rd16le d 12 = 0 ∨ rd16le d 14 = 0
  case pos =>
    have hB : (decide (rd16le d 12 = 0) || decide (rd16le d 14 = 0)) = true := by
      rcases hdim with h | h <;> simp [h]
    rw [hB] at evD
    have hite : ExS Gen.prog (⟨l, m, ro⟩ : State) tgaDims (.ret (some (.int i32 2))) (⟨l, m, ro⟩ : State) :=
      ExS.ite evD x_tt (ExS.ret (EvE.const (v := .int i32 2)))
    exact ⟨⟨l, m, ro⟩, (by rw [tgaCode_dims d size hsz hdim]; exact ExS.seq_ret hite), (fun j _ => rfl), (by simp [tgaHeader_dims d size hsz hdim])⟩
  case neg =>
    have hdimN : ¬ (rd16le d 12 = 0 ∨ rd16le d 14 = 0) := hdim
    have hB : (decide (rd16le d 12 = 0) || decide (rd16le d 14 = 0)) = false := by
      rw [show decide (rd16le d 12 = 0) = false from decide_eq_false_iff_not.mpr (fun h => hdim (Or.inl h)),
          show decide (rd16le d 14 = 0) = false from decide_eq_false_iff_not.mpr (fun h => hdim (Or.inr h))]
      rfl
    rw [hB] at evD
    have hskipD : ExS Gen.prog (⟨l, m, ro⟩ : State) tgaDims .normal (⟨l, m, ro⟩ : State) :=
      ExS.ite evD x_tf ExS.skip
    have evC := ev_tga_cmap (⟨l, m, ro⟩ : State) (byteAt d 1) l4 hb1
    by_cases hcm : byteAt d 1 = 0
    case pos =>
      have hBc : decide (byteAt d 1 ≠ 0) = false := by simp [hcm]
      rw [hBc] at evC
      have hskipC : ExS Gen.prog (⟨l, m, ro⟩ : State) tgaCmap .normal (⟨l, m, ro⟩ : State) :=
        ExS.ite evC x_tf ExS.skip
      have evT := ev_tga_badtype (⟨l, m, ro⟩ : State) (byteAt d 2) l5 hb2
      by_cases hbad : ¬ byteAt d 2 = 2 ∧ ¬ byteAt d 2 = 3 ∧ ¬ byteAt d 2 = 10 ∧ ¬ byteAt d 2 = 11
      case pos =>
        have hBt : (decide (byteAt d 2 ≠ 2) && decide (byteAt d 2 ≠ 3) && decide (byteAt d 2 ≠ 10) && decide (byteAt d 2 ≠ 11)) = true := by
          simp [hbad.1, hbad.2.1, hbad.2.2.1, hbad.2.2.2]
        rw [hBt] at evT
        have hite : ExS Gen.prog (⟨l, m, ro⟩ : State) tgaBadType (.ret (some (.int i32 4))) (⟨l, m, ro⟩ : State) :=
          ExS.ite evT x_tt (ExS.ret (EvE.const (v := .int i32 4)))
        exact ⟨⟨l, m, ro⟩, (by rw [tgaCode_badtype d size hsz hdimN hcm hbad]; exact ExS.seq hskipD (ExS.seq hskipC (ExS.seq_ret hite))), (fun j _ => rfl), (by simp [tgaHeader_badtype d size hsz hdimN hcm hbad])⟩
      case neg =>
        have hvalid : ¬ (¬ byteAt d 2 = 2 ∧ ¬ byteAt d 2 = 3 ∧ ¬ byteAt d 2 = 10 ∧ ¬ byteAt d 2 = 11) := hbad
        have hBt : (decide (byteAt d 2 ≠ 2) && decide (byteAt d 2 ≠ 3) && decide (byteAt d 2 ≠ 10) && decide (byteAt d 2 ≠ 11)) = false := by
          by_cases h2 : byteAt d 2 = 2
          · simp [h2]
          · by_cases h3 : byteAt d 2 = 3
            · simp [h3]
            · by_cases h10 : byteAt d 2 = 10
              · simp [h10]
              · by_cases h11 : byteAt d 2 = 11
                · simp [h11]
                · exact absurd ⟨h2, h3, h10, h11⟩ hbad
        rw [hBt] at evT
        have hskipT : ExS Gen.prog (⟨l, m, ro⟩ : State) tgaBadType .normal (⟨l, m, ro⟩ : State) :=
          ExS.ite evT x_tf ExS.skip
        have evCh := ev_tga_chanbranch (⟨l, m, ro⟩ : State) (byteAt d 2) l5 hb2
        by_cases hchan : byteAt d 2 = 3 ∨ byteAt d 2 = 11
        case pos =>
          have hBch : (decide (byteAt d 2 = 3) || decide (byteAt d 2 = 11)) = true := by
            rcases hchan with h | h <;> simp [h]
          rw [hBch] at evCh
          have evP8 := ev_tga_pd8 (⟨l, m, ro⟩ : State) (byteAt d 16) l8 hpd
          by_cases hpd8 : byteAt d 16 = 8
          case pos =>
            have hBp : decide (byteAt d 16 ≠ 8) = false := by simp [hpd8]
            rw [hBp] at evP8
            let lC : Locals := l.upd 10 (.int u8 1)
            have hset : ExS Gen.prog (⟨l, m, ro⟩ : State) (.set 10 (.cast u8 (.const (.int u32 1)))) .normal (⟨lC, m, ro⟩ : State) :=
              ExS.set (EvE.cast (EvE.const (v := .int u32 1)) (u32_u8_cast 1 (by omega)))
            have hChan : ExS Gen.prog (⟨l, m, ro⟩ : State) tgaChannels .normal (⟨lC, m, ro⟩ : State) :=
              ExS.ite evCh x_tt (ExS.seq (ExS.ite evP8 x_tf ExS.skip) hset)
            have lC1 : lC 1 = some (.int u64 size) := by simp only [lC, Locals.upd_ne]; exact l1
            have lC2 : lC 2 = some (.ptr 3 0) := by simp only [lC, Locals.upd_ne]; exact l2
            have lC3 : lC 3 = some (.int u8 (byteAt d 0)) := by simp only [lC, Locals.upd_ne]; exact l3
            have lC5 : lC 5 = some (.int u8 (byteAt d 2)) := by simp only [lC, Locals.upd_ne]; exact l5
            have lC6 : lC 6 = some (.int u16 (rd16le d 12)) := by simp only [lC, Locals.upd_ne]; exact l6
            have lC7 : lC 7 = some (.int u16 (rd16le d 14)) := by simp only [lC, Locals.upd_ne]; exact l7
            have lC9 : lC 9 = some (.int u8 (byteAt d 17)) := by simp only [lC, Locals.upd_ne]; exact l9
            have lC10 : lC 10 = some (.int u8 1) := by simp only [lC]; exact Locals.upd_same l 10 _
            obtain ⟨s', hrest, hmem, hblk⟩ := tgaHeader_rest_exs m d size obl hob h32 ro hro 1 (by omega) lC
              lC1 lC2 lC3 lC5 lC6 lC7 lC9 lC10 hww hhh hid hb2 hde (by omega)
              (fun hidg hm1 hm2 => tgaHeader_ok1 d size hsz hdimN hcm hvalid hchan hpd8 hidg hm1 hm2)
              (fun hidg => by
                unfold tgaHeader
                simp only [if_neg hsz, if_neg hdimN, if_neg (by simp [hcm] : ¬ (byteAt d 1 ≠ 0)),
                  if_neg hvalid, if_pos hchan, if_neg (by simp [hpd8] : ¬ (byteAt d 16 ≠ 8)),
                  if_pos hidg, Except.bind, Bind.bind, pure, Except.pure, id]
                rfl)
              (fun hidgN hm1f => by
                unfold tgaHeader
                simp only [if_neg hsz, if_neg hdimN, if_neg (by simp [hcm] : ¬ (byteAt d 1 ≠ 0)),
                  if_neg hvalid, if_pos hchan, if_neg (by simp [hpd8] : ¬ (byteAt d 16 ≠ 8)),
                  if_neg hidgN, if_pos (by rw [hm1f]; decide : (! sizeMulOK (rd16le d 12) (rd16le d 14)) = true),
                  Except.bind, Bind.bind, pure, Except.pure, id]
                rfl)
              (fun hidgN hm1 hm2f => by
                unfold tgaHeader
                simp only [if_neg hsz, if_neg hdimN, if_neg (by simp [hcm] : ¬ (byteAt d 1 ≠ 0)),
                  if_neg hvalid, if_pos hchan, if_neg (by simp [hpd8] : ¬ (byteAt d 16 ≠ 8)),
                  if_neg hidgN, if_neg (by rw [hm1]; decide : ¬ ((! sizeMulOK (rd16le d 12) (rd16le d 14)) = true)),
                  if_pos (by rw [hm2f]; decide : (! sizeMulOK (rd16le d 12 * rd16le d 14) 1) = true),
                  Except.bind, Bind.bind, pure, Except.pure, id]
                rfl)
            exact ⟨s', (by exact ExS.seq hskipD (ExS.seq hskipC (ExS.seq hskipT (ExS.seq hChan hrest)))), hmem, hblk⟩
          case neg =>
            have hBp : decide (byteAt d 16 ≠ 8) = true := by simp [hpd8]
            rw [hBp] at evP8
            have hiteP : ExS Gen.prog (⟨l, m, ro⟩ : State) (.ite (.bin .ne (some u32) (.cast u32 (.var 8)) (.const (.int u32 8))) (.ret (some (.const (.int i32 5)))) .skip) (.ret (some (.int i32 5))) (⟨l, m, ro⟩ : State) :=
              ExS.ite evP8 x_tt (ExS.ret (EvE.const (v := .int i32 5)))
            have hChan : ExS Gen.prog (⟨l, m, ro⟩ : State) tgaChannels (.ret (some (.int i32 5))) (⟨l, m, ro⟩ : State) :=
              ExS.ite evCh x_tt (ExS.seq_ret hiteP)
            exact ⟨⟨l, m, ro⟩, (by rw [tgaCode_depth1 d size hsz hdimN hcm hvalid hchan hpd8]; exact ExS.seq hskipD (ExS.seq hskipC (ExS.seq hskipT (ExS.seq_ret hChan)))), (fun j _ => rfl), (by simp [tgaHeader_depth1 d size hsz hdimN hcm hvalid hchan hpd8])⟩
        case neg =>
          have hBchF : (decide (byteAt d 2 = 3) || decide (byteAt d 2 = 11)) = false := by
            rw [show decide (byteAt d 2 = 3) = false from decide_eq_false_iff_not.mpr (fun h => hchan (Or.inl h)),
                show decide (byteAt d 2 = 11) = false from decide_eq_false_iff_not.mpr (fun h => hchan (Or.inr h))]
            rfl
          rw [hBchF] at evCh
          have evP24 := ev_tga_pd24 (⟨l, m, ro⟩ : State) (byteAt d 16) l8 hpd
          by_cases hpd24 : byteAt d 16 = 24
          case pos =>
            have hB24 : decide (byteAt d 16 = 24) = true := by simp [hpd24]
            rw [hB24] at evP24
            let lC : Locals := l.upd 10 (.int u8 3)
            have hset : ExS Gen.prog (⟨l, m, ro⟩ : State) (.set 10 (.cast u8 (.const (.int u32 3)))) .normal (⟨lC, m, ro⟩ : State) :=
              ExS.set (EvE.cast (EvE.const (v := .int u32 3)) (u32_u8_cast 3 (by omega)))
            have hChan : ExS Gen.prog (⟨l, m, ro⟩ : State) tgaChannels .normal (⟨lC, m, ro⟩ : State) :=
              ExS.ite evCh x_tf (ExS.ite evP24 x_tt hset)
            have lC1 : lC 1 = some (.int u64 size) := by simp only [lC, Locals.upd_ne]; exact l1
            have lC2 : lC 2 = some (.ptr 3 0) := by simp only [lC, Locals.upd_ne]; exact l2
            have lC3 : lC 3 = some (.int u8 (byteAt d 0)) := by simp only [lC, Locals.upd_ne]; exact l3
            have lC5 : lC 5 = some (.int u8 (byteAt d 2)) := by simp only [lC, Locals.upd_ne]; exact l5
            have lC6 : lC 6 = some (.int u16 (rd16le d 12)) := by simp only [lC, Locals.upd_ne]; exact l6
            have lC7 : lC 7 = some (.int u16 (rd16le d 14)) := by simp only [lC, Locals.upd_ne]; exact l7
            have lC9 : lC 9 = some (.int u8 (byteAt d 17)) := by simp only [lC, Locals.upd_ne]; exact l9
            have lC10 : lC 10 = some (.int u8 3) := by simp only [lC]; exact Locals.upd_same l 10 _
            obtain ⟨s', hrest, hmem, hblk⟩ := tgaHeader_rest_exs m d size obl hob h32 ro hro 3 (by omega) lC
              lC1 lC2 lC3 lC5 lC6 lC7 lC9 lC10 hww hhh hid hb2 hde (by omega)
              (fun hidg hm1 hm2 => tgaHeader_ok3 d size hsz hdimN hcm hvalid hchan hpd24 hidg hm1 hm2)
              (fun hidg => by
                unfold tgaHeader
                simp only [if_neg hsz, if_neg hdimN, if_neg (by simp [hcm] : ¬ (byteAt d 1 ≠ 0)),
                  if_neg hvalid, if_neg hchan, if_pos hpd24, if_pos hidg,
                  Except.bind, Bind.bind, pure, Except.pure, id]
                rfl)
              (fun hidgN hm1f => by
                unfold tgaHeader
                simp only [if_neg hsz, if_neg hdimN, if_neg (by simp [hcm] : ¬ (byteAt d 1 ≠ 0)),
                  if_neg hvalid, if_neg hchan, if_pos hpd24, if_neg hidgN,
                  if_pos (by rw [hm1f]; decide : (! sizeMulOK (rd16le d 12) (rd16le d 14)) = true),
                  Except.bind, Bind.bind, pure, Except.pure, id]
                rfl)
              (fun hidgN hm1 hm2f => by
                unfold tgaHeader
                simp only [if_neg hsz, if_neg hdimN, if_neg (by simp [hcm] : ¬ (byteAt d 1 ≠ 0)),
                  if_neg hvalid, if_neg hchan, if_pos hpd24, if_neg hidgN,
                  if_neg (by rw [hm1]; decide : ¬ ((! sizeMulOK (rd16le d 12) (rd16le d 14)) = true)),
                  if_pos (by rw [hm2f]; decide : (! sizeMulOK (rd16le d 12 * rd16le d 14) 3) = true),
                  Except.bind, Bind.bind, pure, Except.pure, id]
                rfl)
            exact ⟨s', (by exact ExS.seq hskipD (ExS.seq hskipC (ExS.seq hskipT (ExS.seq hChan hrest)))), hmem, hblk⟩
          case neg =>
            have hB24 : decide (byteAt d 16 = 24) = false := by simp [hpd24]
            rw [hB24] at evP24
            have evP32 := ev_tga_pd32 (⟨l, m, ro⟩ : State) (byteAt d 16) l8 hpd
            by_cases hpd32 : byteAt d 16 = 32
            case pos =>
              have hB32 : decide (byteAt d 16 = 32) = true := by simp [hpd32]
              rw [hB32] at evP32
              let lC : Locals := l.upd 10 (.int u8 4)
              have hset : ExS Gen.prog (⟨l, m, ro⟩ : State) (.set 10 (.cast u8 (.const (.int u32 4)))) .normal (⟨lC, m, ro⟩ : State) :=
                ExS.set (EvE.cast (EvE.const (v := .int u32 4)) (u32_u8_cast 4 (by omega)))
              have hChan : ExS Gen.prog (⟨l, m, ro⟩ : State) tgaChannels .normal (⟨lC, m, ro⟩ : State) :=
                ExS.ite evCh x_tf (ExS.ite evP24 x_tf (ExS.ite evP32 x_tt hset))
              have lC1 : lC 1 = some (.int u64 size) := by simp only [lC, Locals.upd_ne]; exact l1
              have lC2 : lC 2 = some (.ptr 3 0) := by simp only [lC, Locals.upd_ne]; exact l2
              have lC3 : lC 3 = some (.int u8 (byteAt d 0)) := by simp only [lC, Locals.upd_ne]; exact l3
              have lC5 : lC 5 = some (.int u8 (byteAt d 2)) := by simp only [lC, Locals.upd_ne]; exact l5
              have lC6 : lC 6 = some (.int u16 (rd16le d 12)) := by simp only [lC, Locals.upd_ne]; exact l6
              have lC7 : lC 7 = some (.int u16 (rd16le d 14)) := by simp only [lC, Locals.upd_ne]; exact l7
              have lC9 : lC 9 = some (.int u8 (byteAt d 17)) := by simp only [lC, Locals.upd_ne]; exact l9
              have lC10 : lC 10 = some (.int u8 4) := by simp only [lC]; exact Locals.upd_same l 10 _
              obtain ⟨s', hrest, hmem, hblk⟩ := tgaHeader_rest_exs m d size obl hob h32 ro hro 4 (by omega) lC
                lC1 lC2 lC3 lC5 lC6 lC7 lC9 lC10 hww hhh hid hb2 hde (by omega)
                (fun hidg hm1 hm2 => tgaHeader_ok4 d size hsz hdimN hcm hvalid hchan hpd32 hidg hm1 hm2)
                (fun hidg => by
                  unfold tgaHeader
                  simp only [if_neg hsz, if_neg hdimN, if_neg (by simp [hcm] : ¬ (byteAt d 1 ≠ 0)),
                    if_neg hvalid, if_neg hchan, if_neg (by simp [hpd24] : ¬ (byteAt d 16 = 24)),
                    if_pos hpd32, if_pos hidg, Except.bind, Bind.bind, pure, Except.pure, id]
                  rfl)
                (fun hidgN hm1f => by
                  unfold tgaHeader
                  simp only [if_neg hsz, if_neg hdimN, if_neg (by simp [hcm] : ¬ (byteAt d 1 ≠ 0)),
                    if_neg hvalid, if_neg hchan, if_neg (by simp [hpd24] : ¬ (byteAt d 16 = 24)),
                    if_pos hpd32, if_neg hidgN,
                    if_pos (by rw [hm1f]; decide : (! sizeMulOK (rd16le d 12) (rd16le d 14)) = true),
                    Except.bind, Bind.bind, pure, Except.pure, id]
                  rfl)
                (fun hidgN hm1 hm2f => by
                  unfold tgaHeader
                  simp only [if_neg hsz, if_neg hdimN, if_neg (by simp [hcm] : ¬ (byteAt d 1 ≠ 0)),
                    if_neg hvalid, if_neg hchan, if_neg (by simp [hpd24] : ¬ (byteAt d 16 = 24)),
                    if_pos hpd32, if_neg hidgN,
                    if_neg (by rw [hm1]; decide : ¬ ((! sizeMulOK (rd16le d 12) (rd16le d 14)) = true)),
                    if_pos (by rw [hm2f]; decide : (! sizeMulOK (rd16le d 12 * rd16le d 14) 4) = true),
                    Except.bind, Bind.bind, pure, Except.pure, id]
                  rfl)
              exact ⟨s', (by exact ExS.seq hskipD (ExS.seq hskipC (ExS.seq hskipT (ExS.seq hChan hrest)))), hmem, hblk⟩
            case neg =>
              have hB32 : decide (byteAt d 16 = 32) = false := by simp [hpd32]
              rw [hB32] at evP32
              have hiteInner : ExS Gen.prog (⟨l, m, ro⟩ : State) (.ite (.bin .eq (some u32) (.cast u32 (.var 8)) (.const (.int u32 32))) (.set 10 (.cast u8 (.const (.int u32 4)))) (.ret (some (.const (.int i32 5))))) (.ret (some (.int i32 5))) (⟨l, m, ro⟩ : State) :=
                ExS.ite evP32 x_tf (ExS.ret (EvE.const (v := .int i32 5)))
              have hite24 : ExS Gen.prog (⟨l, m, ro⟩ : State) (.ite (.bin .eq (some u32) (.cast u32 (.var 8)) (.const (.int u32 24))) (.set 10 (.cast u8 (.const (.int u32 3)))) _) (.ret (some (.int i32 5))) (⟨l, m, ro⟩ : State) :=
                ExS.ite evP24 x_tf hiteInner
              have hChan : ExS Gen.prog (⟨l, m, ro⟩ : State) tgaChannels (.ret (some (.int i32 5))) (⟨l, m, ro⟩ : State) :=
                ExS.ite evCh x_tf hite24
              exact ⟨⟨l, m, ro⟩, (by rw [tgaCode_depth2 d size hsz hdimN hcm hvalid hchan hpd24 hpd32]; exact ExS.seq hskipD (ExS.seq hskipC (ExS.seq hskipT (ExS.seq_ret hChan)))), (fun j _ => rfl), (by simp [tgaHeader_depth2 d size hsz hdimN hcm hvalid hchan hpd24 hpd32])⟩
    case neg =>
      have hcmn : byteAt d 1 ≠ 0 := hcm
      have hBc : decide (byteAt d 1 ≠ 0) = true := by simp [hcmn]
      rw [hBc] at evC
      have hite : ExS Gen.prog (⟨l, m, ro⟩ : State) tgaCmap (.ret (some (.int i32 3))) (⟨l, m, ro⟩ : State) :=
        ExS.ite evC x_tt (ExS.ret (EvE.const (v := .int i32 3)))
      exact ⟨⟨l, m, ro⟩, (by rw [tgaCode_cmap d size hsz hdimN hcmn]; exact ExS.seq hskipD (ExS.seq_ret hite)), (fun j _ => rfl), (by simp [tgaHeader_cmap d size hsz hdimN hcmn])⟩

end NANO.C.Proofs
