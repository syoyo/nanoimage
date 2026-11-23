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
