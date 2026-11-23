/-
  `ni_tga_header` — the eight info-block stores as a reusable refinement lemma.
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
import NANO.C.Proofs.NiTgaHeader
import NANO.C.Proofs.NiTgaHeaderBody

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 1600000

namespace NANO.C.Proofs
open NANO NANO.C

/-- The eight `ni_tga_header` info-block stores produce `tgaHeaderBlock`. -/
theorem tgaStores_exs (m : Mem) (obl : List UInt8) (hob : m 3 = some obl) (h32 : obl.length = 32)
    (w hh ch rle top right id osz : Nat)
    (hw : w < 65536) (hhh : hh < 65536) (hch : ch < 256) (hrle : rle < 256)
    (htop : top < 256) (hright : right < 256) (hid : id < 256) (hosz : osz < 2 ^ 64)
    (hdv : 18 + id < 2 ^ 64)
    (ro : Bool) (hro : ro = false) (l : Locals)
    (l2 : l 2 = some (.ptr 3 0)) (l6 : l 6 = some (.int u16 w)) (l7 : l 7 = some (.int u16 hh))
    (l10 : l 10 = some (.int u8 ch)) (l11 : l 11 = some (.int u64 osz)) (l3 : l 3 = some (.int u8 id))
    (e16 : ∀ mm, EvE Gen.prog ⟨l, mm, ro⟩ (.cast u32 (.var 6)) (.int u32 w))
    (e20 : ∀ mm, EvE Gen.prog ⟨l, mm, ro⟩ (.cast u32 (.var 7)) (.int u32 hh))
    (e24 : ∀ mm, EvE Gen.prog ⟨l, mm, ro⟩ (.var 10) (.int u8 ch))
    (e25 : ∀ mm, EvE Gen.prog ⟨l, mm, ro⟩ (.cast u8 (.lor
              (.bin .eq (some u32) (.cast u32 (.var 5)) (.const (.int u32 10)))
              (.bin .eq (some u32) (.cast u32 (.var 5)) (.const (.int u32 11))))) (.int u8 rle))
    (e26 : ∀ mm, EvE Gen.prog ⟨l, mm, ro⟩ (.cast u8 (.bin .ne (some u32)
              (.bin .band (some u32) (.cast u32 (.var 9)) (.const (.int u32 32)))
              (.const (.int u32 0)))) (.int u8 top))
    (e27 : ∀ mm, EvE Gen.prog ⟨l, mm, ro⟩ (.cast u8 (.bin .ne (some u32)
              (.bin .band (some u32) (.cast u32 (.var 9)) (.const (.int u32 16)))
              (.const (.int u32 0)))) (.int u8 right))
    (e8 : ∀ mm, EvE Gen.prog ⟨l, mm, ro⟩ (.bin .add (some u64)
              (.cast u64 (.const (.int i32 18))) (.cast u64 (.var 3))) (.int u64 (18 + id)))
    (e0 : ∀ mm, EvE Gen.prog ⟨l, mm, ro⟩ (.var 11) (.int u64 osz)) :
    ∃ s', ExS Gen.prog ⟨l, m, ro⟩ tgaStores (.ret (some (.int i32 0))) s' ∧
      s'.mem 3 = some (tgaHeaderBlock obl
        ({ outputSize := osz, dataOffset := 18 + id, width := w,
           height := hh, channels := ch, rle := rle, topOrigin := top, rightOrigin := right } : TgaInfo)) ∧
      (∀ j, j ≠ 3 → s'.mem j = m j) := by
  let b1 := obl.take 16 ++ encodeLE 4 w ++ obl.drop 20
  let b2 := b1.take 20 ++ encodeLE 4 hh ++ b1.drop 24
  let b3 := b2.take 24 ++ encodeLE 1 ch ++ b2.drop 25
  let b4 := b3.take 25 ++ encodeLE 1 rle ++ b3.drop 26
  let b5 := b4.take 26 ++ encodeLE 1 top ++ b4.drop 27
  let b6 := b5.take 27 ++ encodeLE 1 right ++ b5.drop 28
  let b7 := b6.take 8 ++ encodeLE 8 (18 + id) ++ b6.drop 16
  let b8 := b7.take 0 ++ encodeLE 8 osz ++ b7.drop 8
  let m1 := m.upd 3 b1
  let m2 := m1.upd 3 b2
  let m3 := m2.upd 3 b3
  let m4 := m3.upd 3 b4
  let m5 := m4.upd 3 b5
  let m6 := m5.upd 3 b6
  let m7 := m6.upd 3 b7
  let m8 := m7.upd 3 b8
  have hb1 : b1.length = 32 := by
    dsimp only [b1]
    simp [encodeLE_length, List.length_take, List.length_drop, List.length_append, h32]
  have hb2 : b2.length = 32 := by
    dsimp only [b2]; simp [hb1, encodeLE_length, List.length_take, List.length_drop, List.length_append]
  have hb3 : b3.length = 32 := by
    dsimp only [b3]; simp [hb2, encodeLE_length, List.length_take, List.length_drop, List.length_append]
  have hb4 : b4.length = 32 := by
    dsimp only [b4]; simp [hb3, encodeLE_length, List.length_take, List.length_drop, List.length_append]
  have hb5 : b5.length = 32 := by
    dsimp only [b5]; simp [hb4, encodeLE_length, List.length_take, List.length_drop, List.length_append]
  have hb6 : b6.length = 32 := by
    dsimp only [b6]; simp [hb5, encodeLE_length, List.length_take, List.length_drop, List.length_append]
  have hb7 : b7.length = 32 := by
    dsimp only [b7]; simp [hb6, encodeLE_length, List.length_take, List.length_drop, List.length_append]
  have hm1 : m1 3 = some b1 := by rw [show m1 = m.upd 3 b1 from rfl]; exact Mem.upd_same m 3 b1
  have hm2 : m2 3 = some b2 := by rw [show m2 = m1.upd 3 b2 from rfl]; exact Mem.upd_same m1 3 b2
  have hm3 : m3 3 = some b3 := by rw [show m3 = m2.upd 3 b3 from rfl]; exact Mem.upd_same m2 3 b3
  have hm4 : m4 3 = some b4 := by rw [show m4 = m3.upd 3 b4 from rfl]; exact Mem.upd_same m3 3 b4
  have hm5 : m5 3 = some b5 := by rw [show m5 = m4.upd 3 b5 from rfl]; exact Mem.upd_same m4 3 b5
  have hm6 : m6 3 = some b6 := by rw [show m6 = m5.upd 3 b6 from rfl]; exact Mem.upd_same m5 3 b6
  have hm7 : m7 3 = some b7 := by rw [show m7 = m6.upd 3 b7 from rfl]; exact Mem.upd_same m6 3 b7
  have d16 : EvE Gen.prog (⟨l, m, ro⟩ : State) (.field (.var 2) 16) (.ptr 3 (0 + 16)) := ev_field32 hob l2 (by omega)
  have s16 : ExS Gen.prog (⟨l, m, ro⟩ : State) (.store (.int u32) (.field (.var 2) 16) (.cast u32 (.var 6))) .normal (⟨l, m1, ro⟩ : State) :=
    ExS.store d16 (e16 m) hro (store_field_u32_32 m 3 obl hob h32 16 (by omega) w (by omega))
  have d20 : EvE Gen.prog (⟨l, m1, ro⟩ : State) (.field (.var 2) 20) (.ptr 3 (0 + 20)) := ev_field32 hm1 l2 (by omega)
  have s20 : ExS Gen.prog (⟨l, m1, ro⟩ : State) (.store (.int u32) (.field (.var 2) 20) (.cast u32 (.var 7))) .normal (⟨l, m2, ro⟩ : State) :=
    ExS.store d20 (e20 m1) hro (store_field_u32_32 m1 3 b1 hm1 hb1 20 (by omega) hh (by omega))
  have d24 : EvE Gen.prog (⟨l, m2, ro⟩ : State) (.field (.var 2) 24) (.ptr 3 (0 + 24)) := ev_field32 hm2 l2 (by omega)
  have s24 : ExS Gen.prog (⟨l, m2, ro⟩ : State) (.store (.int u8) (.field (.var 2) 24) (.var 10)) .normal (⟨l, m3, ro⟩ : State) :=
    ExS.store d24 (e24 m2) hro (store_field_u8_32 m2 3 b2 hm2 hb2 24 (by omega) ch (by omega))
  have d25 : EvE Gen.prog (⟨l, m3, ro⟩ : State) (.field (.var 2) 25) (.ptr 3 (0 + 25)) := ev_field32 hm3 l2 (by omega)
  have s25 : ExS Gen.prog (⟨l, m3, ro⟩ : State) (.store (.int u8) (.field (.var 2) 25) (.cast u8 (.lor
              (.bin .eq (some u32) (.cast u32 (.var 5)) (.const (.int u32 10)))
              (.bin .eq (some u32) (.cast u32 (.var 5)) (.const (.int u32 11)))))) .normal (⟨l, m4, ro⟩ : State) :=
    ExS.store d25 (e25 m3) hro (store_field_u8_32 m3 3 b3 hm3 hb3 25 (by omega) rle (by omega))
  have d26 : EvE Gen.prog (⟨l, m4, ro⟩ : State) (.field (.var 2) 26) (.ptr 3 (0 + 26)) := ev_field32 hm4 l2 (by omega)
  have s26 : ExS Gen.prog (⟨l, m4, ro⟩ : State) (.store (.int u8) (.field (.var 2) 26) (.cast u8 (.bin .ne (some u32)
              (.bin .band (some u32) (.cast u32 (.var 9)) (.const (.int u32 32))) (.const (.int u32 0))))) .normal (⟨l, m5, ro⟩ : State) :=
    ExS.store d26 (e26 m4) hro (store_field_u8_32 m4 3 b4 hm4 hb4 26 (by omega) top (by omega))
  have d27 : EvE Gen.prog (⟨l, m5, ro⟩ : State) (.field (.var 2) 27) (.ptr 3 (0 + 27)) := ev_field32 hm5 l2 (by omega)
  have s27 : ExS Gen.prog (⟨l, m5, ro⟩ : State) (.store (.int u8) (.field (.var 2) 27) (.cast u8 (.bin .ne (some u32)
              (.bin .band (some u32) (.cast u32 (.var 9)) (.const (.int u32 16))) (.const (.int u32 0))))) .normal (⟨l, m6, ro⟩ : State) :=
    ExS.store d27 (e27 m5) hro (store_field_u8_32 m5 3 b5 hm5 hb5 27 (by omega) right (by omega))
  have d8 : EvE Gen.prog (⟨l, m6, ro⟩ : State) (.field (.var 2) 8) (.ptr 3 (0 + 8)) := ev_field32 hm6 l2 (by omega)
  have s8 : ExS Gen.prog (⟨l, m6, ro⟩ : State) (.store (.int u64) (.field (.var 2) 8) (.bin .add (some u64)
              (.cast u64 (.const (.int i32 18))) (.cast u64 (.var 3)))) .normal (⟨l, m7, ro⟩ : State) :=
    ExS.store d8 (e8 m6) hro (store_field_u64_32 m6 3 b6 hm6 hb6 8 (by omega) (18 + id) (by omega))
  have d0 : EvE Gen.prog (⟨l, m7, ro⟩ : State) (.field (.var 2) 0) (.ptr 3 (0 + 0)) := ev_field32 hm7 l2 (by omega)
  have s0s : ExS Gen.prog (⟨l, m7, ro⟩ : State) (.store (.int u64) (.field (.var 2) 0) (.var 11)) .normal (⟨l, m8, ro⟩ : State) :=
    ExS.store d0 (e0 m7) hro (store_field_u64_32 m7 3 b7 hm7 hb7 0 (by omega) osz hosz)
  have hret : ExS Gen.prog (⟨l, m8, ro⟩ : State) (.ret (some (.const (.int i32 0)))) (.ret (some (.int i32 0))) (⟨l, m8, ro⟩ : State) :=
    ExS.ret (EvE.const (v := .int i32 0))
  refine ⟨⟨l, m8, ro⟩, ?_, ?_, ?_⟩
  · exact ExS.seq s16 (ExS.seq s20 (ExS.seq s24 (ExS.seq s25 (ExS.seq s26 (ExS.seq s27 (ExS.seq s8 (ExS.seq s0s hret)))))))
  · show m8 3 = some _
    rw [show m8 = m7.upd 3 b8 from rfl, Mem.upd_same,
        show b8 = encodeLE 8 osz ++ encodeLE 8 (18 + id) ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top ++ encodeLE 1 right ++ obl.drop 28 from tgaHeaderBlock_stores obl w hh ch rle top right (18 + id) osz h32]
    rfl
  · intro j hj
    dsimp only [m8, m7, m6, m5, m4, m3, m2, m1]
    simp [Mem.upd, if_neg hj]

end NANO.C.Proofs
