/-
  BMP direct-path decode loop refinement proof — the inner x-loop of
  the 24/32-bit decode path (`ni_bmp_decode_into_loop2`), built on
  `ni_bmp_decode_raw_pixel_exs`.
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Lemmas
import NANO.Spec
import NANO.Bmp
import NANO.C.Proofs.Core
import NANO.C.Proofs.NiGeometryTail
import NANO.C.Proofs.NiBmpHeaderLoads
import NANO.C.Proofs.NiBmpDecode
import NANO.C.Proofs.NiBmpLoop

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 800000

namespace NANO.C.Proofs
open NANO NANO.C

/-- A successful direct pixel expands `bmpPixel`'s expansion list bytewise. -/
theorem bmpPixel_direct_succ (d : List UInt8) (h : BmpInfo) (y x : Nat)
    (hn8 : h.bitCount ≠ 8) (hc : h.channels = 3 ∨ h.channels = 4) :
    bmpPixel d h y x =
      .ok (if h.channels = 4 then
             [d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 2) 0,
              d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 1) 0,
              d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 0) 0,
              d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 3) 0]
           else
             [d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 2) 0,
              d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 1) 0,
              d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 0) 0]) := by
  rw [bmpPixel_direct d h y x hn8]
  by_cases hc4 : h.channels = 4
  · rw [ite_eq_left hc4, ite_eq_left hc4]
  · rw [ite_eq_right hc4, ite_eq_right hc4]

/-- One direct pixel's expansion as a prefix of the next row's bytes. -/
theorem rowOut_direct_succ (d : List UInt8) (h : BmpInfo) (y x : Nat)
    (hn8 : h.bitCount ≠ 8) (hc : h.channels = 3 ∨ h.channels = 4) :
    rowOut d h y (x + 1)
      = rowOut d h y x ++ (if h.channels = 4 then
            [d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 2) 0,
             d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 1) 0,
             d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 0) 0,
             d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 3) 0]
          else
            [d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 2) 0,
             d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 1) 0,
             d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * (if h.bitCount = 32 then 4 else 3) + 0) 0]) := by
  unfold rowOut
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
  rw [bmpPixel_direct_succ d h y x hn8 hc]
/-- Induction principle for the direct-path inner row loop: with the row
    invariant at counter `x`, running the loop stores the remaining pixels
    and ends `.brk`-terminated at `width`. -/
theorem loop2_iter (m : Mem) (d obl : List UInt8)
    (bd ob : Nat) (hm : m bd = some d) (hd : d.length < 2 ^ 64)
    (hob : m ob = some obl) (hd0 : bd ≠ ob) (ho2 : 3 ≠ ob) (bd2 : 3 ≠ bd)
    (info : List UInt8) (hinfo : m 3 = some info) (h48 : info.length = 48)
    (h : BmpInfo) (hn8 : h.bitCount ≠ 8)
    (hc3 : h.channels = 3 ∨ h.channels = 4)
    (hc32 : h.channels = (if h.bitCount = 32 then 4 else 3))
    (hw : (info.drop 24).take 4 = encodeLE 4 h.width) (hwv : h.width < 4294967296)
    (y : Nat)
    (hout : (y + 1) * h.width * h.channels ≤ obl.length)
    (hlen : obl.length < 2 ^ 64)
    (hy : y < h.height)
    (hok_row : ∀ i, i < h.width → ∃ bs, bmpPixel d h y i = .ok bs)
    (hok_rows : ∀ yy i, yy < y → i < h.width → ∃ bs, bmpPixel d h yy i = .ok bs)
    (ro : Bool) (hro : ro = false) :
    ∀ (n : Nat) (x : Nat) (s : State),
      (hsrc : ∀ i, x ≤ i → i < h.width → h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + i * h.channels + h.channels ≤ d.length) →
      h.width - x = n →
      x ≤ h.width →
      s.locals 0 = some (.ptr bd 0) →
      s.locals 2 = some (.ptr 3 0) →
      s.locals 3 = some (.ptr ob 0) →
      s.locals 5 = some (.int ⟨32, false⟩ y) →
      s.locals 6 = some (.int ⟨32, false⟩ x) →
      s.locals 9 = some (.int ⟨64, false⟩ h.channels) →
      s.locals 19 = some (.int ⟨64, false⟩ h.channels) →
      s.locals 21 = some (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) →
      s.locals 22 = some (.int ⟨64, false⟩ (y * h.width * h.channels)) →
      s.ro = false →
      s.mem ob = some (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * h.channels)) →
      s.mem bd = some d →
      s.mem 3 = some info →
      ∃ s', ExS Gen.prog s Gen.ni_bmp_decode_into_loop2 .normal s' ∧
        s'.mem ob = some (bmpRowsBytes d h (y + 1) ++ obl.drop ((y + 1) * (h.width * h.channels))) ∧
        s'.locals 5 = some (.int ⟨32, false⟩ y) ∧
        (∀ j, j ≠ 6 → j ≠ 23 → j ≠ 24 → j ≠ 25 → s'.locals j = s.locals j) ∧
        s'.mem bd = s.mem bd ∧
        s'.mem 3 = s.mem 3 ∧
        s'.ro = s.ro := by
  intro n
  induction n with
  | zero =>
      intro x s hsrc hZero hx hl0 hl2 hl3 hl5 hl6 hl9 hl19 hl21 hl22 hros smem hmem2 smem2
      have hxeq : x = h.width := by omega
      subst hxeq
      have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
      have hField : EvE Gen.prog s (.field (.var 2) 24) (.ptr 3 24) :=
        EvE.field (EvE.var hl2)
          (ptrAddN_ok smem2 (by omega))
      have hLoad : EvE Gen.prog s (.load (.int ⟨32, false⟩) (.field (.var 2) 24)) (.int ⟨32, false⟩ h.width) :=
        EvE.load hField (load_u32_field s.mem 3 info smem2 h48 24 (by omega) h.width hw hwv)
      have hCond : EvE Gen.prog s (.bin .lt (some ⟨32, false⟩) (.var 6) (.load (.int ⟨32, false⟩) (.field (.var 2) 24))) (boolVal false) := by
        have hdec : decide (h.width < h.width) = false := decide_eq_false (by omega)
        exact EvE.bin (EvE.var hl6) hLoad
          (by rw [bin_u32_lt, hdec])
      have hIf : ExS Gen.prog s
          (.ite (.bin .lt (some ⟨32, false⟩) (.var 6) (.load (.int ⟨32, false⟩) (.field (.var 2) 24)))
            (.seq (.set 23 (.bin .add (some ⟨64, false⟩) (.var 21) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.var 19))))
              (.seq (.set 24 (.bin .add (some ⟨64, false⟩) (.var 22) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.var 9))))
                (.seq (.call (some 25) 20 [(.var 0), (.var 3), (.var 23), (.var 24), (.var 9)])
                  (.ite (.bin .ne (some ⟨32, true⟩) (.var 25) (.const (.int ⟨32, true⟩ 0))) (.ret (some (.var 25))) .skip))))
            .brk)
          .brk s :=
        ExS.ite hCond truthy_false ExS.brk
      have hLoop : ExS Gen.prog s Gen.ni_bmp_decode_into_loop2 .normal s := by
        show ExS Gen.prog s (.loop (.ite (.bin .lt (some ⟨32, false⟩) (.var 6) (.load (.int ⟨32, false⟩) (.field (.var 2) 24))) (.seq (.set 23 (.bin .add (some ⟨64, false⟩) (.var 21) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.var 19)))) (.seq (.set 24 (.bin .add (some ⟨64, false⟩) (.var 22) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.var 9)))) (.seq (.call (some 25) 20 [(.var 0), (.var 3), (.var 23), (.var 24), (.var 9)]) (.ite (.bin .ne (some ⟨32, true⟩) (.var 25) (.const (.int ⟨32, true⟩ 0))) (.ret (some (.var 25))) .skip)))) .brk) (.set 6 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 1)))))) .normal s
        exact ExS.loop_brk hIf
      refine ⟨s, hLoop, ?_, ?_, ?_, ?_, ?_, ?_⟩
      have e1 : (y * h.width + h.width) * h.channels = y * h.width * h.channels + h.width * h.channels := Nat.add_mul (y * h.width) h.width h.channels
      have e2 : (y + 1) * (h.width * h.channels) = y * h.width * h.channels + h.width * h.channels := by
        rw [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc]
      rw [smem, rowOut_width, bmpRowsBytes_succ_flat, e1, ← e2]
      exact hl5
      intro j h6 h23 h24 h25; rfl
      rfl
      rfl
      rfl

  | succ k ih =>
      intro x s hsrc hSucc hx hl0 hl2 hl3 hl5 hl6 hl9 hl19 hl21 hl22 hros smem hmem2 smem2
      have hxlt : x < h.width := by omega
      have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
      have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
      -- load width field and evaluate the guard
      have hField : EvE Gen.prog s (.field (.var 2) 24) (.ptr 3 24) :=
        EvE.field (EvE.var hl2)
          (ptrAddN_ok smem2 (by omega))
      have hLoad : EvE Gen.prog s (.load (.int ⟨32, false⟩) (.field (.var 2) 24)) (.int ⟨32, false⟩ h.width) :=
        EvE.load hField (load_u32_field s.mem 3 info smem2 h48 24 (by omega) h.width hw hwv)
      have hCond : EvE Gen.prog s (.bin .lt (some ⟨32, false⟩) (.var 6) (.load (.int ⟨32, false⟩) (.field (.var 2) 24))) (boolVal true) := by
        have hdec : decide (x < h.width) = true := decide_eq_true (by omega)
        exact EvE.bin (EvE.var hl6) hLoad (by rw [bin_u32_lt, hdec])
      -- shared stride arithmetic
      have h1 : y * h.width + x ≤ (y + 1) * h.width := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hM : (y * h.width + x) * h.channels ≤ (y + 1) * h.width * h.channels :=
        Nat.mul_le_mul_right (k := h.channels) h1
      have heb : (y * h.width + x) * h.channels = y * h.width * h.channels + x * h.channels :=
        Nat.add_mul (y * h.width) x h.channels
      -- set 23: s := src_base + x * src_channels
      have hCastX : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ x) = .ok (.int ⟨64, false⟩ x) :=
        u32_u64_cast x (by omega)
      have hMul19 : EvE Gen.prog s (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.var 19)) (.int ⟨64, false⟩ (x * h.channels)) :=
        EvE.bin (EvE.cast (EvE.var hl6) hCastX) (EvE.var hl19) (bin_u64_mul x h.channels (by rw [heb] at hM; omega))
      have hAdd23 : EvE Gen.prog s (.bin .add (some ⟨64, false⟩) (.var 21) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.var 19))) (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) :=
        EvE.bin (EvE.var hl21) hMul19
          (bin_u64_add (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride) (x * h.channels) (by
            have hbound := hsrc x (by omega) hxlt
            omega))
      have hSet23 : ExS Gen.prog s
          (.set 23 (.bin .add (some ⟨64, false⟩) (.var 21) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.var 19))))
          .normal { s with locals := s.locals.upd 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) } :=
        ExS.set hAdd23
      let s1 : State := { s with locals := s.locals.upd 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) }
      -- set 24: d := dst_base + x * channels
      have hMul9 : EvE Gen.prog s1 (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.var 9)) (.int ⟨64, false⟩ (x * h.channels)) :=
        EvE.bin (EvE.cast (EvE.var (locals_upd_extract 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) 6 (by decide : ¬ (6 : Nat) = 23) hl6)) hCastX)
          (EvE.var (locals_upd_extract 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) 9 (by decide : ¬ (9 : Nat) = 23) hl9))
          (bin_u64_mul x h.channels (by rw [heb] at hM; omega))
      have hAdd24 : EvE Gen.prog s1 (.bin .add (some ⟨64, false⟩) (.var 22) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.var 9))) (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) :=
        EvE.bin (EvE.var (locals_upd_extract 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) 22 (by decide : ¬ (22 : Nat) = 23) hl22)) hMul9
          (bin_u64_add (y * h.width * h.channels) (x * h.channels) (by rw [← heb]; omega))
      have hSet24 : ExS Gen.prog s1
          (.set 24 (.bin .add (some ⟨64, false⟩) (.var 22) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.var 9))))
          .normal { s1 with locals := s1.locals.upd 24 (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) } :=
        ExS.set hAdd24
      let s1' : State := { s1 with locals := s1.locals.upd 24 (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) }
      have hMemS1' : s1'.mem = s.mem := rfl
      have hlen_px : ∀ x bs, bmpPixel d h y x = .ok bs → bs.length = bmpPixelSize h :=
        fun x bs hbs => bmpPixel_direct_length d h y x hn8 hc3 bs hbs
      have hlen_px2 : ∀ yy x bs, bmpPixel d h yy x = .ok bs → bs.length = bmpPixelSize h :=
        fun yy x bs hbs => bmpPixel_direct_length d h yy x hn8 hc3 bs hbs
      have hArows : (bmpRowsBytes d h y).length = y * bmpRowSize h :=
        bmpRowsBytes_length d h y (by omega) (fun yy x' hyy hx' => hok_rows yy x' hyy hx')
          (fun yy x' bs hbs => hlen_px2 yy x' bs hbs)
      have hAblen : (bmpRowsBytes d h y ++ rowOut d h y x).length = (y * h.width + x) * h.channels := by
        rw [List.length_append, hArows, rowOut_length d h y x (fun i hi => hok_row i (by omega)) hlen_px]
        simp only [bmpRowSize, bmpPixelSize, hn8, ite_false, Nat.add_mul]
        rw [← Nat.mul_assoc]
      have hdist : (y * h.width + x) * h.channels + h.channels ≤ obl.length := by
        calc (y * h.width + x) * h.channels + h.channels
            = (y * h.width + x + 1) * h.channels := (Nat.succ_mul _ _).symm
          _ ≤ (y + 1) * h.width * h.channels :=
              Nat.mul_le_mul_right (k := h.channels) (by rw [Nat.add_mul, Nat.one_mul]; omega)
          _ ≤ obl.length := hout
      rw [heb] at hdist
      have hMemA_ob : (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * h.channels)).length = obl.length := by
        rw [List.length_append, List.length_drop, hAblen]
        omega
      have hobP : s1'.mem ob = some (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * h.channels)) := by
        rw [hMemS1']; exact smem
      have hbdP : s1'.mem bd = some d := by
        rw [hMemS1']; exact hmem2
      -- bounds for the raw pixel call, per channels case
      have hs1 := hsrc x (by omega) hxlt
      have h1abc : y * h.width * h.channels + x * h.channels = (y * h.width + x) * h.channels := heb.symm
      have hs0 : h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels + 3 ≤ d.length := by
        cases hc3 with
        | inl h3 => rw [h3] at hs1 ⊢; exact hs1
        | inr h4 => rw [h4] at hs1 ⊢; omega
      have hs4 : h.channels = 4 → h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels + 4 ≤ d.length := by
        intro h4
        rw [h4] at hs1 ⊢
        exact hs1
      have hd20 : y * h.width * h.channels + x * h.channels + 3 ≤ (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * h.channels)).length := by
        rw [hMemA_ob]
        cases hc3 with
        | inl h3 => rw [h3] at hdist ⊢; omega
        | inr h4 => rw [h4] at hdist ⊢; omega
      have hd24 : h.channels = 4 → y * h.width * h.channels + x * h.channels + 4 ≤ (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * h.channels)).length := by
        intro h4
        rw [hMemA_ob]
        rw [h4] at hdist ⊢
        omega
      have hclt4 : h.channels ≤ 4 := by
        cases hc3 with | inl h3 => omega | inr h4 => omega
      -- EvArgs for the call
      have h0_2 : s1'.locals 0 = some (.ptr bd 0) :=
        locals_upd_extract 24 (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) 0 (by decide : ¬ (0 : Nat) = 24)
          (locals_upd_extract 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) 0 (by decide : ¬ (0 : Nat) = 23) hl0)
      have hw0 : EvE Gen.prog s1' (.var 0) (.ptr bd 0) := EvE.var h0_2
      have h3_2 : s1'.locals 3 = some (.ptr ob 0) :=
        locals_upd_extract 24 (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) 3 (by decide : ¬ (3 : Nat) = 24)
          (locals_upd_extract 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) 3 (by decide : ¬ (3 : Nat) = 23) hl3)
      have hw3 : EvE Gen.prog s1' (.var 3) (.ptr ob 0) := EvE.var h3_2
      have h9_2 : s1'.locals 9 = some (.int ⟨64, false⟩ h.channels) :=
        locals_upd_extract 24 (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) 9 (by decide : ¬ (9 : Nat) = 24)
          (locals_upd_extract 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) 9 (by decide : ¬ (9 : Nat) = 23) hl9)
      have hw9 : EvE Gen.prog s1' (.var 9) (.int ⟨64, false⟩ h.channels) := EvE.var h9_2
      have h23_1 : s1'.locals 23 = some (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) := by
        rw [show s1'.locals = s1.locals.upd 24 (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) from rfl]
        rw [show s1.locals = s.locals.upd 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) from rfl]
        rw [Locals.upd_ne _ _ (by decide : ¬ (23 : Nat) = 24), Locals.upd_same]
      have hw23 : EvE Gen.prog s1' (.var 23) (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) :=
        EvE.var h23_1
      have h24_1 : s1'.locals 24 = some (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) := by
        rw [show s1'.locals = s1.locals.upd 24 (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) from rfl]
        rw [Locals.upd_same]
      have hw24 : EvE Gen.prog s1' (.var 24) (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) :=
        EvE.var h24_1
      have hCallArgs : EvArgs Gen.prog s1' [.var 0, .var 3, .var 23, .var 24, .var 9]
          [.ptr bd 0, .ptr ob 0, .int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels), .int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels), .int ⟨64, false⟩ h.channels] :=
        EvArgs.cons hw0 (EvArgs.cons hw3 (EvArgs.cons hw23 (EvArgs.cons hw24 (EvArgs.cons hw9 EvArgs.nil))))
      obtain ⟨sP, exP, hMemP, hMemPbd, hMemP2⟩ :=
        ni_bmp_decode_raw_pixel_exs s1'.mem d
          (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * h.channels))
          bd ob hbdP hd hobP
          (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)
          (y * h.width * h.channels + x * h.channels)
          h.channels hs0 hs4 hd20 hd24 hclt4
          (by rw [hMemA_ob]; exact hlen) hd0 ho2
          s1'.ro
          (by rw [show s1'.ro = s.ro from rfl]; exact hros)
      have hCall : ExS Gen.prog s1'
          (.call (some 25) 20 [(.var 0), (.var 3), (.var 23), (.var 24), (.var 9)]) .normal
          { s1' with locals := s1'.locals.upd 25 (.int ⟨32, true⟩ 0), mem := sP.mem, ro := s1'.ro } :=
        ExS.call_dst hCallArgs
          (show Gen.prog 20 = some Gen.ni_bmp_decode_raw_pixel from rfl)
          (show Gen.ni_bmp_decode_raw_pixel.params.length = 5 from rfl)
          exP
      let s2 : State := { s1' with locals := s1'.locals.upd 25 (.int ⟨32, true⟩ 0), mem := sP.mem, ro := s1'.ro }
      -- the code-0 branch skips
      have h25ne : EvE Gen.prog s2 (.bin .ne (some ⟨32, true⟩) (.var 25) (.const (.int ⟨32, true⟩ 0))) (boolVal false) := by
        have hl25 : s2.locals 25 = some (.int ⟨32, true⟩ 0) := rfl
        have e : EvE Gen.prog s2 (.bin .ne (some ⟨32, true⟩) (.var 25) (.const (.int ⟨32, true⟩ 0)))
            (boolVal (decide (IntTy.toInt ⟨32, true⟩ 0 ≠ IntTy.toInt ⟨32, true⟩ 0))) :=
          EvE.bin (EvE.var hl25) (EvE.const _) (bin_i32_ne _ _)
        rw [show (decide (IntTy.toInt ⟨32, true⟩ 0 ≠ IntTy.toInt ⟨32, true⟩ 0)) = false from by decide] at e
        exact e
      have hSkip : ExS Gen.prog s2
          (.ite (.bin .ne (some ⟨32, true⟩) (.var 25) (.const (.int ⟨32, true⟩ 0))) (.ret (some (.var 25))) .skip)
          .normal s2 :=
        ExS.ite h25ne truthy_false ExS.skip
      -- step: x := x + 1
      have h6_2 : s2.locals 6 = some (.int ⟨32, false⟩ x) := by
        rw [show s2.locals 6 = s1'.locals 6 from rfl]
        exact locals_upd_extract 24 (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) 6 (by decide : ¬ (6 : Nat) = 24)
          (locals_upd_extract 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) 6 (by decide : ¬ (6 : Nat) = 23) hl6)
      have hCastX2 : evalCast ⟨32, false⟩ (.int ⟨32, false⟩ x) = .ok (.int ⟨32, false⟩ x) := u32_u32_cast x (by omega)
      have hAdd2 : EvE Gen.prog s2 (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 1))) (.int ⟨32, false⟩ (x + 1)) :=
        EvE.bin (EvE.cast (EvE.var h6_2) hCastX2) (EvE.const _) (bin_u32_add x 1 (by omega))
      have hCastX3 : evalCast ⟨32, false⟩ (.int ⟨32, false⟩ (x + 1)) = .ok (.int ⟨32, false⟩ (x + 1)) := u32_u32_cast (x + 1) (by omega)
      have hSet6 : ExS Gen.prog s2
          (.set 6 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 1)))))
          .normal { s2 with locals := s2.locals.upd 6 (.int ⟨32, false⟩ (x + 1)) } :=
        ExS.set (EvE.cast hAdd2 hCastX3)
      let s3 : State := { s2 with locals := s2.locals.upd 6 (.int ⟨32, false⟩ (x + 1)) }
      -- ==== the block the callee wrote, normalized for the outer invariant ====
      have hAlen2 : (bmpRowsBytes d h y ++ rowOut d h y x).length = y * h.width * h.channels + x * h.channels := by
        rw [hAblen, heb]
      have htakeA : List.take (y * h.width * h.channels + x * h.channels) (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * h.channels))
          = bmpRowsBytes d h y ++ rowOut d h y x := by
        rw [show y * h.width * h.channels + x * h.channels = (bmpRowsBytes d h y ++ rowOut d h y x).length from hAlen2.symm]
        exact List.take_append_length
      have hdropA : List.drop (y * h.width * h.channels + x * h.channels + (if h.channels = 4 then 4 else 3)) (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * h.channels))
          = obl.drop ((y * h.width + (x + 1)) * h.channels) := by
        rw [show y * h.width * h.channels + x * h.channels + (if h.channels = 4 then 4 else 3) = (bmpRowsBytes d h y ++ rowOut d h y x).length + (if h.channels = 4 then 4 else 3) from by rw [hAlen2]]
        rw [drop_append_length (bmpRowsBytes d h y ++ rowOut d h y x) (obl.drop ((y * h.width + x) * h.channels)) (if h.channels = 4 then 4 else 3)]
        rw [List.drop_drop]
        by_cases hc4 : h.channels = 4
        · rw [ite_eq_left hc4]
          rw [show (y * h.width + x) * h.channels + 4 = (y * h.width + (x + 1)) * h.channels from by
            rw [hc4, show y * h.width + (x + 1) = y * h.width + x + 1 from by omega]
            exact (Nat.succ_mul _ _).symm]
        · rw [ite_eq_right hc4]
          have h3 : h.channels = 3 := by
            cases hc3 with
            | inl h3 => exact h3
            | inr h4 => exact absurd h4 hc4
          rw [show (y * h.width + x) * h.channels + 3 = (y * h.width + (x + 1)) * h.channels from by
            rw [h3, show y * h.width + (x + 1) = y * h.width + x + 1 from by omega]
            exact (Nat.succ_mul _ _).symm]
      have hEnc3 : encodeLE 1 (byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels + 2))
          ++ encodeLE 1 (byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels + 1))
          ++ encodeLE 1 (byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels + 0))
          = [d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels + 2) 0,
             d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels + 1) 0,
             d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels) 0] := by
        simp [encodeLE_one_byteAt, List.append_assoc]
      have hRowOut : rowOut d h y (x + 1)
          = rowOut d h y x ++ (if h.channels = 4 then
              [d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels + 2) 0,
               d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels + 1) 0,
               d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels) 0,
               d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels + 3) 0]
            else
              [d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels + 2) 0,
               d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels + 1) 0,
               d.getD (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels) 0]) := by
        unfold rowOut
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
        rw [bmpPixel_direct_succ d h y x hn8 hc3]
        rw [show (if h.bitCount = 32 then 4 else 3) = h.channels from hc32.symm]
        by_cases h4 : h.channels = 4
        · rw [if_pos h4, if_pos h4]
          rfl
        · rw [if_neg h4, if_neg h4]
          rfl
      have hMemP' : sP.mem ob = some (bmpRowsBytes d h y ++ rowOut d h y (x + 1) ++ obl.drop ((y * h.width + (x + 1)) * h.channels)) := by
        rw [hMemP, htakeA, hdropA, hRowOut]
        by_cases hc4 : h.channels = 4
        · rw [ite_eq_left hc4, ite_eq_left hc4]
          simp [encodeLE_one_byteAt, List.append_assoc, List.singleton_append, List.cons_append, List.append_nil]
        · rw [ite_eq_right hc4, ite_eq_right hc4]
          simp [encodeLE_one_byteAt, List.append_assoc, List.singleton_append, List.cons_append, List.append_nil]
      -- ==== the state after the body is done ====
      have hMem3 : s3.mem ob = some (bmpRowsBytes d h y ++ rowOut d h y (x + 1) ++ obl.drop ((y * h.width + (x + 1)) * h.channels)) := by
        show (s2.mem ob) = some _
        rw [show s2.mem = sP.mem from rfl]
        exact hMemP'
      have hMem3bd : s3.mem bd = some d := by
        show (s2.mem bd) = some d
        rw [show s2.mem = sP.mem from rfl]
        exact hMemPbd
      have hMem3_2 : s3.mem 3 = some info := by
        show (s2.mem 3) = some info
        rw [hMemP2]
        show (s1'.mem 3) = some info
        rw [show s1'.mem = s.mem from rfl]
        exact smem2
      have h0a : s1'.locals 0 = some (.ptr bd 0) := h0_2
      have h0b : s2.locals 0 = some (.ptr bd 0) := locals_upd_extract 25 (.int ⟨32, true⟩ 0) 0 (by decide : ¬ (0 : Nat) = 25) h0a
      have hl0_3 : s3.locals 0 = some (.ptr bd 0) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 0 (by decide : ¬ (0 : Nat) = 6) h0b
      have h2a : s1'.locals 2 = some (.ptr 3 0) :=
        locals_upd_extract 24 (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) 2 (by decide : ¬ (2 : Nat) = 24)
          (locals_upd_extract 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) 2 (by decide : ¬ (2 : Nat) = 23) hl2)
      have h2b : s2.locals 2 = some (.ptr 3 0) := locals_upd_extract 25 (.int ⟨32, true⟩ 0) 2 (by decide : ¬ (2 : Nat) = 25) h2a
      have hl2_3 : s3.locals 2 = some (.ptr 3 0) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 2 (by decide : ¬ (2 : Nat) = 6) h2b
      have h3a : s1'.locals 3 = some (.ptr ob 0) := h3_2
      have h3b : s2.locals 3 = some (.ptr ob 0) := locals_upd_extract 25 (.int ⟨32, true⟩ 0) 3 (by decide : ¬ (3 : Nat) = 25) h3a
      have hl3_3 : s3.locals 3 = some (.ptr ob 0) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 3 (by decide : ¬ (3 : Nat) = 6) h3b
      have hl6_3 : s3.locals 6 = some (.int ⟨32, false⟩ (x + 1)) := by
        rw [show s3.locals = s2.locals.upd 6 (.int ⟨32, false⟩ (x + 1)) from rfl]
        rw [Locals.upd_same]
      have h9a : s1'.locals 9 = some (.int ⟨64, false⟩ h.channels) := h9_2
      have h9b : s2.locals 9 = some (.int ⟨64, false⟩ h.channels) := locals_upd_extract 25 (.int ⟨32, true⟩ 0) 9 (by decide : ¬ (9 : Nat) = 25) h9a
      have hl9_3 : s3.locals 9 = some (.int ⟨64, false⟩ h.channels) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 9 (by decide : ¬ (9 : Nat) = 6) h9b
      have h19a : s1'.locals 19 = some (.int ⟨64, false⟩ h.channels) :=
        locals_upd_extract 24 (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) 19 (by decide : ¬ (19 : Nat) = 24)
          (locals_upd_extract 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) 19 (by decide : ¬ (19 : Nat) = 23) hl19)
      have h19b : s2.locals 19 = some (.int ⟨64, false⟩ h.channels) := locals_upd_extract 25 (.int ⟨32, true⟩ 0) 19 (by decide : ¬ (19 : Nat) = 25) h19a
      have hl19_3 : s3.locals 19 = some (.int ⟨64, false⟩ h.channels) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 19 (by decide : ¬ (19 : Nat) = 6) h19b
      have h21a : s1'.locals 21 = some (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) :=
        locals_upd_extract 24 (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) 21 (by decide : ¬ (21 : Nat) = 24)
          (locals_upd_extract 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) 21 (by decide : ¬ (21 : Nat) = 23) hl21)
      have h21b : s2.locals 21 = some (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) := locals_upd_extract 25 (.int ⟨32, true⟩ 0) 21 (by decide : ¬ (21 : Nat) = 25) h21a
      have hl21_3 : s3.locals 21 = some (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 21 (by decide : ¬ (21 : Nat) = 6) h21b
      have h22a : s1'.locals 22 = some (.int ⟨64, false⟩ (y * h.width * h.channels)) :=
        locals_upd_extract 24 (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) 22 (by decide : ¬ (22 : Nat) = 24)
          (locals_upd_extract 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) 22 (by decide : ¬ (22 : Nat) = 23) hl22)
      have h22b : s2.locals 22 = some (.int ⟨64, false⟩ (y * h.width * h.channels)) := locals_upd_extract 25 (.int ⟨32, true⟩ 0) 22 (by decide : ¬ (22 : Nat) = 25) h22a
      have hl22_3 : s3.locals 22 = some (.int ⟨64, false⟩ (y * h.width * h.channels)) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 22 (by decide : ¬ (22 : Nat) = 6) h22b
      have h5_1 : s1'.locals 5 = some (.int ⟨32, false⟩ y) := locals_upd_extract 24 (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) 5 (by decide : ¬ (5 : Nat) = 24)
        (locals_upd_extract 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) 5 (by decide : ¬ (5 : Nat) = 23) hl5)
      have h5_2 : s2.locals 5 = some (.int ⟨32, false⟩ y) := locals_upd_extract 25 (.int ⟨32, true⟩ 0) 5 (by decide : ¬ (5 : Nat) = 25) h5_1
      have hl5_3 : s3.locals 5 = some (.int ⟨32, false⟩ y) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 5 (by decide : ¬ (5 : Nat) = 6) h5_2
      -- ==== step: x := x + 1 ====
      obtain ⟨s', hLoop', hMem', hLoc', hPres', hMem'bd, hMem'2, hRO'⟩ := ih (x + 1) s3
        (fun i h1 h2 => hsrc i (by omega) h2)
        (by omega) (by omega)
        hl0_3 hl2_3 hl3_3 hl5_3 hl6_3 hl9_3 hl19_3 hl21_3 hl22_3
        (by rw [show s3.ro = s.ro from rfl]; exact hros)
        hMem3 hMem3bd hMem3_2
      have hPres : ∀ j, j ≠ 6 → j ≠ 23 → j ≠ 24 → j ≠ 25 → s'.locals j = s.locals j := by
        intro j h6 h23 h24 h25
        have e4 : s1'.locals j = s.locals j := by
          rw [show s1'.locals = s1.locals.upd 24 (.int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels)) from rfl,
              show s1.locals = s.locals.upd 23 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels)) from rfl]
          rw [Locals.upd_ne _ _ h24, Locals.upd_ne _ _ h23]
        have e3 : s2.locals j = s1'.locals j := by
          rw [show s2.locals = s1'.locals.upd 25 (.int ⟨32, true⟩ 0) from rfl]
          rw [Locals.upd_ne _ _ h25]
        have e2 : s3.locals j = s2.locals j := by
          rw [show s3.locals = s2.locals.upd 6 (.int ⟨32, false⟩ (x + 1)) from rfl]
          rw [Locals.upd_ne _ _ h6]
        rw [hPres' j h6 h23 h24 h25, e2, e3, e4]
      have hMem'bdC : s'.mem bd = s.mem bd := by
        have h1 : s'.mem bd = some d := by
          rw [hMem'bd]
          exact hMem3bd
        rw [h1, hmem2]
      have hMem'2C : s'.mem 3 = s.mem 3 := by
        have h1 : s'.mem 3 = some info := by
          rw [hMem'2]
          exact hMem3_2
        rw [h1, smem2]
      refine ⟨s', ?_, hMem', hLoc', hPres, hMem'bdC, hMem'2C, hRO'⟩
      show ExS Gen.prog s Gen.ni_bmp_decode_into_loop2 .normal s'
      have hBody : ExS Gen.prog s
          (.ite (.bin .lt (some ⟨32, false⟩) (.var 6) (.load (.int ⟨32, false⟩) (.field (.var 2) 24)))
            (.seq (.set 23 (.bin .add (some ⟨64, false⟩) (.var 21) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.var 19))))
              (.seq (.set 24 (.bin .add (some ⟨64, false⟩) (.var 22) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.var 9))))
                (.seq (.call (some 25) 20 [(.var 0), (.var 3), (.var 23), (.var 24), (.var 9)])
                  (.ite (.bin .ne (some ⟨32, true⟩) (.var 25) (.const (.int ⟨32, true⟩ 0))) (.ret (some (.var 25))) .skip))))
            .brk)
          .normal s2 :=
        ExS.ite hCond truthy_true (ExS.seq hSet23 (ExS.seq hSet24 (ExS.seq hCall hSkip)))
      exact ExS.loop_next hBody (Or.inl rfl) hSet6 hLoop'


/-- The inner 24/32-bit row loop of `ni_bmp_decode_into`, all-pixels-OK case:
    runs to `.brk` at `width`, leaving the first `y + 1` output rows in `out`.
    Locals: 0=bytes, 1=size, 2=info, 3=out, 4=out_cap, 5=y, 6=x, 7=width,
    8=height, 9=channels, 10=row_stride, 11=pixel_offset, 12=palette_offset,
    13=palette_entries, 14=src_y, 15=src_base, 16=dst_base, 17=code, 18=dst,
    19=src_channels, 20=src_y, 21=src_base, 22=dst_base, 23=s, 24=d, 25=code -/
theorem ni_bmp_decode_into_loop2_ok_exs (m : Mem) (d obl : List UInt8)
    (bd ob : Nat) (hm : m bd = some d) (hd : d.length < 2 ^ 64)
    (hob : m ob = some obl) (hd0 : bd ≠ ob) (ho2 : 3 ≠ ob) (bd2 : 3 ≠ bd)
    (info : List UInt8) (hinfo : m 3 = some info) (h48 : info.length = 48)
    (h : BmpInfo) (hn8 : h.bitCount ≠ 8)
    (hc3 : h.channels = 3 ∨ h.channels = 4) (hc32 : h.channels = (if h.bitCount = 32 then 4 else 3))
    (hw : (info.drop 24).take 4 = encodeLE 4 h.width) (hwv : h.width < 4294967296)
    (y x : Nat) (hx : x ≤ h.width)
    (hout : (y + 1) * h.width * h.channels ≤ obl.length)
    (hlen : obl.length < 2 ^ 64)
    (hsrc : ∀ i, x ≤ i → i < h.width → h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + i * h.channels + h.channels ≤ d.length)
    (hy : y < h.height)
    (hbok : ∀ yy i, yy < y → i < h.width → ∃ bs, bmpPixel d h yy i = .ok bs)
    (hok_row : ∀ i, i < h.width → ∃ bs, bmpPixel d h y i = .ok bs)
    (hmem : m ob = some (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * h.channels)))
    (ro : Bool) (hro : ro = false) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
        ([.ptr bd 0, .int ⟨64, false⟩ d.length, .ptr 3 0, .ptr ob 0, .int ⟨64, false⟩ obl.length,
          .int ⟨32, false⟩ y, .int ⟨32, false⟩ x,
          .int ⟨64, false⟩ h.width, .int ⟨64, false⟩ h.height, .int ⟨64, false⟩ h.channels,
          .int ⟨64, false⟩ h.rowStride, .int ⟨64, false⟩ h.pixelOffset,
          .int ⟨64, false⟩ h.paletteOffset, .int ⟨64, false⟩ h.paletteEntries,
          .int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y),
          .int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride),
          .int ⟨64, false⟩ (y * h.width * h.channels),
          .int ⟨32, true⟩ 0,
          .int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels),
          .int ⟨64, false⟩ h.channels,
          .int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y),
          .int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride),
          .int ⟨64, false⟩ (y * h.width * h.channels),
          .int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels),
          .int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels),
          .int ⟨32, true⟩ 0] : List Val), m, ro⟩
      Gen.ni_bmp_decode_into_loop2
      (.normal) s' ∧
    s'.mem ob = some
      (bmpRowsBytes d h (y + 1) ++ obl.drop ((y + 1) * (h.width * h.channels))) := by
  have hiter := loop2_iter m d obl bd ob hm hd hob hd0 ho2 bd2 info hinfo h48 h hn8 hc3 hc32 hw hwv
    y hout hlen hy hok_row hbok ro hro
    (h.width - x) x
    ⟨frameLocals [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
      ([.ptr bd 0, .int ⟨64, false⟩ d.length, .ptr 3 0, .ptr ob 0, .int ⟨64, false⟩ obl.length,
        .int ⟨32, false⟩ y, .int ⟨32, false⟩ x,
        .int ⟨64, false⟩ h.width, .int ⟨64, false⟩ h.height, .int ⟨64, false⟩ h.channels,
        .int ⟨64, false⟩ h.rowStride, .int ⟨64, false⟩ h.pixelOffset,
        .int ⟨64, false⟩ h.paletteOffset, .int ⟨64, false⟩ h.paletteEntries,
        .int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y),
        .int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride),
        .int ⟨64, false⟩ (y * h.width * h.channels),
        .int ⟨32, true⟩ 0,
        .int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels),
        .int ⟨64, false⟩ h.channels,
        .int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y),
        .int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride),
        .int ⟨64, false⟩ (y * h.width * h.channels),
        .int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x * h.channels),
        .int ⟨64, false⟩ (y * h.width * h.channels + x * h.channels),
        .int ⟨32, true⟩ 0] : List Val), m, ro⟩
    hsrc
    rfl (by omega) rfl rfl rfl rfl rfl rfl rfl rfl rfl hro hmem hm hinfo
  obtain ⟨s5', hLoop5', hMem5', hLoc5', hPres5', hMem5'bd, hMem5'2, hRO5'⟩ := hiter
  exact ⟨s5', hLoop5', hMem5'⟩

end NANO.C.Proofs
