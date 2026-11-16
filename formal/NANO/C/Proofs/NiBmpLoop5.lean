/-
  BMP outer row-loop refinement proof — the y-loop of the 24/32-bit decode path
  (`ni_bmp_decode_into_loop3`), built on `loop2_iter`.
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
import NANO.C.Proofs.NiBmpLoop2

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 800000

namespace NANO.C.Proofs
open NANO NANO.C

/-- The 24/32-bit outer row loop of `ni_bmp_decode_into`: processes rows
    `y = 0 .. height - 1`, leaving the completed output rows in `out`.
    Locals: 0=bytes, 1=size, 2=info, 3=out, 4=out_cap, 5=y, 6=x,
    7=width, 8=height, 9=channels, 10=row_stride, 11=pixel_offset,
    12=palette_offset, 13=palette_entries, 14=src_y, 15=src_base,
    16=dst_base, 19=src_channels, 20=src_y, 21=src_base, 22=dst_base,
    23=s, 24=d, 25=code -/
theorem loop3_iter (m : Mem) (d obl : List UInt8)
    (bd ob : Nat) (hm : m bd = some d) (hd : d.length < 2 ^ 64)
    (hob : m ob = some obl) (hd0 : bd ≠ ob) (ho2 : 2 ≠ ob) (bd2 : 2 ≠ bd)
    (info : List UInt8) (hinfo : m 2 = some info) (h48 : info.length = 48)
    (h : BmpInfo) (hn8 : h.bitCount ≠ 8)
    (hc3 : h.channels = 3 ∨ h.channels = 4)
    (hc32 : h.channels = (if h.bitCount = 32 then 4 else 3))
    (hw : (info.drop 24).take 4 = encodeLE 4 h.width) (hwv : h.width < 4294967296)
    (hht : (info.drop 28).take 4 = encodeLE 4 h.height) (hhtwv : h.height < 4294967296)
    (htop : (info.drop 43).take 1 = encodeLE 1 h.topDown) (htopd : h.topDown = 0 ∨ h.topDown = 1)
    (hout : h.height * (h.width * h.channels) ≤ obl.length)
    (hlen : obl.length < 2 ^ 64)
    (hsrc : ∀ y i, y < h.height → i < h.width → h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + i * h.channels + h.channels ≤ d.length)
    (hok : ∀ y i, y < h.height → i < h.width → ∃ bs, bmpPixel d h y i = .ok bs)
    (hwidth : 1 ≤ h.width)
    (ro : Bool) (hro : ro = false) :
    ∀ (n : Nat) (y : Nat) (s : State),
      h.height - y = n →
      y ≤ h.height →
      s.locals 0 = some (.ptr bd 0) →
      s.locals 2 = some (.ptr 2 0) →
      s.locals 3 = some (.ptr ob 0) →
      s.locals 5 = some (.int ⟨32, false⟩ y) →
      s.locals 7 = some (.int ⟨64, false⟩ h.width) →
      s.locals 8 = some (.int ⟨64, false⟩ h.height) →
      s.locals 9 = some (.int ⟨64, false⟩ h.channels) →
      s.locals 10 = some (.int ⟨64, false⟩ h.rowStride) →
      s.locals 11 = some (.int ⟨64, false⟩ h.pixelOffset) →
      s.locals 12 = some (.int ⟨64, false⟩ h.paletteOffset) →
      s.locals 13 = some (.int ⟨64, false⟩ h.paletteEntries) →
      s.locals 19 = some (.int ⟨64, false⟩ h.channels) →
      s.locals 25 = some (.int ⟨32, true⟩ 0) →
      s.ro = false →
      s.mem ob = some (bmpRowsBytes d h y ++ obl.drop (y * (h.width * h.channels))) →
      s.mem bd = some d →
      s.mem 2 = some info →
      ∃ s', ExS Gen.prog s Gen.ni_bmp_decode_into_loop3 .normal s' ∧
        s'.mem ob = some (bmpRowsBytes d h h.height ++ obl.drop (h.height * (h.width * h.channels))) := by
  intro n
  induction n with
  | zero =>
      intro y s hZero hy hl0 hl2 hl3 hl5 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl19 hl25 hros smem hmem2 smem2
      have hyeq : y = h.height := by omega
      subst hyeq
      have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
      have hField : EvE Gen.prog s (.field (.var 2) 28) (.ptr 2 28) :=
        EvE.field (EvE.var hl2)
          (ptrAddN_ok smem2 (by omega))
      have hLoad : EvE Gen.prog s (.load (.int ⟨32, false⟩) (.field (.var 2) 28)) (.int ⟨32, false⟩ h.height) :=
        EvE.load hField (load_u32_field s.mem 2 info smem2 h48 28 (by omega) h.height hht hhtwv)
      have hCond : EvE Gen.prog s (.bin .lt (some ⟨32, false⟩) (.var 5) (.load (.int ⟨32, false⟩) (.field (.var 2) 28))) (boolVal false) := by
        have hdec : decide (h.height < h.height) = false := decide_eq_false (by omega)
        exact EvE.bin (EvE.var hl5) hLoad (by rw [bin_u32_lt, hdec])
      have hIf : ExS Gen.prog s
          (.ite (.bin .lt (some ⟨32, false⟩) (.var 5) (.load (.int ⟨32, false⟩) (.field (.var 2) 28)))
            (.seq (.set 20 (.cond (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 2) 43))) (.cast ⟨64, false⟩ (.var 5)) (.bin .sub (some ⟨64, false⟩) (.bin .sub (some ⟨64, false⟩) (.var 8) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) (.cast ⟨64, false⟩ (.var 5)))))
              (.seq (.set 21 (.bin .add (some ⟨64, false⟩) (.var 11) (.bin .mul (some ⟨64, false⟩) (.var 20) (.var 10))))
                (.seq (.set 22 (.bin .mul (some ⟨64, false⟩) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 5)) (.var 7)) (.var 9)))
                  (.seq (.set 6 (.const (.int ⟨32, false⟩ 0))) Gen.ni_bmp_decode_into_loop2))))
            .brk)
          .brk s :=
        ExS.ite hCond truthy_false ExS.brk
      have hLoop : ExS Gen.prog s Gen.ni_bmp_decode_into_loop3 .normal s := by
        exact ExS.loop_brk hIf
      refine ⟨s, hLoop, ?_⟩
      show s.mem ob = some (bmpRowsBytes d h h.height ++ obl.drop (h.height * (h.width * h.channels)))
      rw [smem]

  | succ k ih =>
      intro y s hSucc hy hl0 hl2 hl3 hl5 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl19 hl25 hros smem hmem2 smem2
      have hylt : y < h.height := by omega
      have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
      have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
      -- load height field and evaluate the guard
      have hField : EvE Gen.prog s (.field (.var 2) 28) (.ptr 2 28) :=
        EvE.field (EvE.var hl2)
          (ptrAddN_ok smem2 (by omega))
      have hLoad : EvE Gen.prog s (.load (.int ⟨32, false⟩) (.field (.var 2) 28)) (.int ⟨32, false⟩ h.height) :=
        EvE.load hField (load_u32_field s.mem 2 info smem2 h48 28 (by omega) h.height hht hhtwv)
      have hCond : EvE Gen.prog s (.bin .lt (some ⟨32, false⟩) (.var 5) (.load (.int ⟨32, false⟩) (.field (.var 2) 28))) (boolVal true) := by
        have hdec : decide (y < h.height) = true := decide_eq_true (by omega)
        exact EvE.bin (EvE.var hl5) hLoad (by rw [bin_u32_lt, hdec])
      -- ==== set 20: src_y := if topDown then y else height - 1 - y ====
      have hField43 : EvE Gen.prog s (.field (.var 2) 43) (.ptr 2 43) :=
        EvE.field (EvE.var hl2)
          (ptrAddN_ok smem2 (by omega))
      have hLoad43 : EvE Gen.prog s (.load (.int ⟨8, false⟩) (.field (.var 2) 43)) (.int ⟨8, false⟩ h.topDown) :=
        EvE.load hField43 (load_u8_field s.mem 2 info smem2 h48 43 (by omega) h.topDown htop (by omega))
      have hCastTD : EvE Gen.prog s (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 2) 43))) (.int ⟨32, true⟩ h.topDown) := by
        have hE : evalCast ⟨32, true⟩ (.int ⟨8, false⟩ h.topDown) = .ok (.int ⟨32, true⟩ h.topDown) :=
          u8_i32_cast (by omega)
        exact EvE.cast hLoad43 hE
      have hCastYC : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ y) = .ok (.int ⟨64, false⟩ y) :=
        u32_u64_cast y (by omega)
      have hY64 : EvE Gen.prog s (.cast ⟨64, false⟩ (.var 5)) (.int ⟨64, false⟩ y) :=
        EvE.cast (EvE.var hl5) hCastYC
      have hConst1 : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1))) (.int ⟨64, false⟩ 1) :=
        EvE.cast (EvE.const _) (u32_u64_cast 1 (by omega))
      have hSub1 : EvE Gen.prog s (.bin .sub (some ⟨64, false⟩) (.var 8) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) (.int ⟨64, false⟩ (h.height - 1)) :=
        EvE.bin (EvE.var hl8) hConst1 (bin_u64_sub h.height 1 (by omega))
      have hSub2 : EvE Gen.prog s (.bin .sub (some ⟨64, false⟩) (.bin .sub (some ⟨64, false⟩) (.var 8) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) (.cast ⟨64, false⟩ (.var 5))) (.int ⟨64, false⟩ (h.height - 1 - y)) :=
        EvE.bin hSub1 hY64 (bin_u64_sub (h.height - 1) y (by omega))
      have hCondB : EvE Gen.prog s (.cond (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 2) 43))) (.cast ⟨64, false⟩ (.var 5)) (.bin .sub (some ⟨64, false⟩) (.bin .sub (some ⟨64, false⟩) (.var 8) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) (.cast ⟨64, false⟩ (.var 5)))) (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) := by
        by_cases htop1 : h.topDown = 1
        · have hbc : truthy (.int ⟨32, true⟩ h.topDown) = .ok true := by
            rw [htop1]; rfl
          rw [htop1, ite_eq_left rfl]
          exact EvE.cond hCastTD hbc (by rw [ite_eq_left rfl]; exact hY64)
        · have h0 : h.topDown = 0 := by
            cases htopd with
            | inl h0 => exact h0
            | inr h1 => exact absurd h1 htop1
          have hbc : truthy (.int ⟨32, true⟩ h.topDown) = .ok false := by
            rw [h0]; rfl
          rw [h0, ite_eq_right (by decide : ¬ (0 : Nat) = 1)]
          exact EvE.cond hCastTD hbc (by rw [ite_eq_right (by decide : ¬ false = true)]; exact hSub2)
      have hSet20 : ExS Gen.prog s
          (.set 20 (.cond (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 2) 43))) (.cast ⟨64, false⟩ (.var 5)) (.bin .sub (some ⟨64, false⟩) (.bin .sub (some ⟨64, false⟩) (.var 8) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) (.cast ⟨64, false⟩ (.var 5)))))
          .normal { s with locals := s.locals.upd 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) } :=
        ExS.set hCondB
      let s1 : State := { s with locals := s.locals.upd 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) }
      -- ==== set 21: src_base := pixel_offset + src_y * row_stride ====
      have h20_1 : s1.locals 20 = some (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) := by
        rw [show s1.locals = s.locals.upd 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) from rfl]
        rw [Locals.upd_same]
      have hsrc0 : h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + 0 * h.channels + h.channels ≤ d.length :=
        hsrc y 0 hylt hwidth
      have hMul21 : EvE Gen.prog s1 (.bin .mul (some ⟨64, false⟩) (.var 20) (.var 10)) (.int ⟨64, false⟩ ((if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) :=
        EvE.bin (EvE.var h20_1) (EvE.var (locals_upd_extract 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) 10 (by decide : ¬ (10 : Nat) = 20) hl10))
          (bin_u64_mul (if h.topDown = 1 then y else h.height - 1 - y) h.rowStride (by omega))
      have hAdd21 : EvE Gen.prog s1 (.bin .add (some ⟨64, false⟩) (.var 11) (.bin .mul (some ⟨64, false⟩) (.var 20) (.var 10))) (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) :=
        EvE.bin (EvE.var (locals_upd_extract 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) 11 (by decide : ¬ (11 : Nat) = 20) hl11)) hMul21
          (bin_u64_add h.pixelOffset ((if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride) (by omega))
      have hSet21 : ExS Gen.prog s1
          (.set 21 (.bin .add (some ⟨64, false⟩) (.var 11) (.bin .mul (some ⟨64, false⟩) (.var 20) (.var 10))))
          .normal { s1 with locals := s1.locals.upd 21 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) } :=
        ExS.set hAdd21
      let s2 : State := { s1 with locals := s1.locals.upd 21 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) }
      -- ==== set 22: dst_base := y * width * channels ====
      have hyw : y * h.width * h.channels ≤ h.height * (h.width * h.channels) := by
        have h1 : y * h.width ≤ h.height * h.width := Nat.mul_le_mul_right (k := h.width) (by omega)
        calc (y * h.width) * h.channels ≤ (h.height * h.width) * h.channels := Nat.mul_le_mul_right (k := h.channels) h1
          _ = h.height * (h.width * h.channels) := by rw [Nat.mul_assoc]
      have hyw' : h.height * (h.width * h.channels) ≤ obl.length := hout
      have h5_1 : s1.locals 5 = some (.int ⟨32, false⟩ y) :=
        locals_upd_extract 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) 5 (by decide : ¬ (5 : Nat) = 20) hl5
      have h5_2 : s2.locals 5 = some (.int ⟨32, false⟩ y) :=
        locals_upd_extract 21 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) 5 (by decide : ¬ (5 : Nat) = 21) h5_1
      have h7_1 : s1.locals 7 = some (.int ⟨64, false⟩ h.width) :=
        locals_upd_extract 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) 7 (by decide : ¬ (7 : Nat) = 20) hl7
      have h7_2 : s2.locals 7 = some (.int ⟨64, false⟩ h.width) :=
        locals_upd_extract 21 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) 7 (by decide : ¬ (7 : Nat) = 21) h7_1
      have hMul16a : EvE Gen.prog s2 (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 5)) (.var 7)) (.int ⟨64, false⟩ (y * h.width)) :=
        EvE.bin (EvE.cast (EvE.var h5_2) hCastYC) (EvE.var h7_2) (bin_u64_mul y h.width (by
          have ch1 : 1 ≤ h.channels := by
            cases hc3 with
            | inl h3 => omega
            | inr h4 => omega
          have h1 : y * h.width ≤ h.height * h.width := Nat.mul_le_mul_right (k := h.width) (by omega)
          have h2 : h.height * h.width ≤ h.height * (h.width * h.channels) :=
            Nat.mul_le_mul_left (k := h.height) (Nat.le_mul_of_pos_right h.width ch1)
          calc y * h.width ≤ h.height * (h.width * h.channels) := by omega
            _ ≤ obl.length := hout
            _ < 2 ^ 64 := hlen))
      have hMul22b : EvE Gen.prog s2 (.bin .mul (some ⟨64, false⟩) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 5)) (.var 7)) (.var 9)) (.int ⟨64, false⟩ (y * h.width * h.channels)) := by
        have h21_9 : s2.locals 9 = some (.int ⟨64, false⟩ h.channels) :=
          locals_upd_extract 21 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) 9 (by decide : ¬ (9 : Nat) = 21)
            (locals_upd_extract 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) 9 (by decide : ¬ (9 : Nat) = 20) hl9)
        have hbound : (y * h.width) * h.channels < 2 ^ 64 := by
          calc (y * h.width) * h.channels ≤ h.height * (h.width * h.channels) := hyw
            _ ≤ obl.length := hout
            _ < 2 ^ 64 := hlen
        have hCast : EvE Gen.prog s2 (.var 9) (.int ⟨64, false⟩ h.channels) :=
          EvE.var h21_9
        have hMulProof : evalBin .mul (some ⟨64, false⟩) (.int ⟨64, false⟩ (y * h.width)) (.int ⟨64, false⟩ h.channels)
            = .ok (.int ⟨64, false⟩ (y * h.width * h.channels)) := by
          exact bin_u64_mul (y * h.width) h.channels hbound
        exact EvE.bin hMul16a hCast hMulProof
      have hSet22 : ExS Gen.prog s2
          (.set 22 (.bin .mul (some ⟨64, false⟩) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 5)) (.var 7)) (.var 9)))
          .normal { s2 with locals := s2.locals.upd 22 (.int ⟨64, false⟩ (y * h.width * h.channels)) } :=
        ExS.set hMul22b
      let s3 : State := { s2 with locals := s2.locals.upd 22 (.int ⟨64, false⟩ (y * h.width * h.channels)) }
      -- ==== set 6: x := 0 ====
      have hSet6 : ExS Gen.prog s3
          (.set 6 (.const (.int ⟨32, false⟩ 0)))
          .normal { s3 with locals := s3.locals.upd 6 (.int ⟨32, false⟩ 0) } :=
        ExS.set (EvE.const _)
      let s4 : State := { s3 with locals := s3.locals.upd 6 (.int ⟨32, false⟩ 0) }
      -- ==== call the 8-bit inner loop (inline Stmt: ni_bmp_decode_into_loop2) ====
      have hMemS4 : s4.mem = s.mem := rfl
      have hlen_px : ∀ x bs, bmpPixel d h y x = .ok bs → bs.length = bmpPixelSize h :=
        fun x bs hbs => bmpPixel_direct_length d h y x hn8 hc3 bs hbs
      have hlen_px2 : ∀ yy x bs, bmpPixel d h yy x = .ok bs → bs.length = bmpPixelSize h :=
        fun yy x bs hbs => bmpPixel_direct_length d h yy x hn8 hc3 bs hbs
      have hok_row : ∀ i, i < h.width → ∃ bs, bmpPixel d h y i = .ok bs :=
        fun i hi => hok y i hylt hi
      have hbok : ∀ yy i, yy < y → i < h.width → ∃ bs, bmpPixel d h yy i = .ok bs :=
        fun yy i hyy hi => hok yy i (by omega) hi
      have hArows : (bmpRowsBytes d h y).length = y * bmpRowSize h :=
        bmpRowsBytes_length d h y (by omega) (fun yy x' hyy hx' => hok yy x' (by omega) hx')
          (fun yy x' bs hbs => hlen_px2 yy x' bs hbs)
      have hPS : bmpPixelSize h = h.channels := by
        simp [bmpPixelSize, ite_eq_right hn8]
      have hAblen : (bmpRowsBytes d h y).length = y * (h.width * h.channels) := by
        rw [hArows, bmpRowSize, hPS]
      have hout1 : (y + 1) * h.width * h.channels ≤ obl.length := by
        have hsub : (y + 1) * (h.width * h.channels) ≤ h.height * (h.width * h.channels) :=
          Nat.mul_le_mul_right (k := (h.width * h.channels)) (by omega)
        have e : (y + 1) * h.width * h.channels = (y + 1) * (h.width * h.channels) :=
          Nat.mul_assoc _ _ _
        rw [e]; omega
      have hobP : s4.mem ob = some (bmpRowsBytes d h y ++ obl.drop (y * (h.width * h.channels))) := by
        rw [hMemS4]; exact smem
      have hbdP : s4.mem bd = some d := by
        rw [hMemS4]; exact hmem2
      have hbdP2 : s4.mem 2 = some info := by
        rw [hMemS4]; exact smem2
      have hy_w3_le : y * (h.width * h.channels) ≤ obl.length := by
        have hsub : y * (h.width * h.channels) ≤ h.height * (h.width * h.channels) :=
          Nat.mul_le_mul_right (k := (h.width * h.channels)) (by omega)
        omega
      have hout1' : (y + 1) * (h.width * h.channels) ≤ obl.length :=
        Nat.le_trans (Nat.mul_le_mul_right (k := (h.width * h.channels)) (by omega)) hout
      have houtP : (y + 1) * h.width * h.channels ≤ (bmpRowsBytes d h y ++ obl.drop (y * (h.width * h.channels))).length := by
        rw [List.length_append, List.length_drop, hAblen]
        have h1 : (y + 1) * (h.width * h.channels) = y * (h.width * h.channels) + h.width * h.channels := by
          rw [Nat.add_mul, Nat.one_mul]
        have h2 : (y + 1) * h.width * h.channels = (y + 1) * (h.width * h.channels) :=
          Nat.mul_assoc (y + 1) h.width h.channels
        rw [h2, h1]
        omega
      have hlenP : (bmpRowsBytes d h y ++ obl.drop (y * (h.width * h.channels))).length < 2 ^ 64 := by
        rw [List.length_append, List.length_drop, hAblen]
        omega
      have hsrcP : ∀ i, 0 ≤ i → i < h.width → h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + i * h.channels + h.channels ≤ d.length :=
        fun i _ hi => hsrc y i hylt hi
      -- the inner block's take/drop pieces
      have htakeA : List.take (y * (h.width * h.channels)) (bmpRowsBytes d h y ++ obl.drop (y * (h.width * h.channels))) = bmpRowsBytes d h y := by
        rw [show y * (h.width * h.channels) = (bmpRowsBytes d h y).length from hAblen.symm]
        exact List.take_append_length
      have dropB : List.drop ((y + 1) * (h.width * h.channels)) (bmpRowsBytes d h y ++ obl.drop (y * (h.width * h.channels)))
          = obl.drop ((y + 1) * (h.width * h.channels)) := by
        have hlenA : (bmpRowsBytes d h y).length = y * (h.width * h.channels) := hAblen
        have e : (y + 1) * (h.width * h.channels) = (bmpRowsBytes d h y).length + h.width * h.channels := by
          rw [Nat.add_mul, Nat.one_mul, hlenA]
        rw [e, drop_append_length _ _ (h.width * h.channels), List.drop_drop,
          show (y * (h.width * h.channels)) + h.width * h.channels = (bmpRowsBytes d h y).length + h.width * h.channels from by rw [hlenA]]
      -- locals facts for the inner frame
      have h0_1 : s4.locals 0 = some (.ptr bd 0) := locals_upd_extract 6 (.int ⟨32, false⟩ 0) 0 (by decide : ¬ (0 : Nat) = 6)
        (locals_upd_extract 22 (.int ⟨64, false⟩ (y * h.width * h.channels)) 0 (by decide : ¬ (0 : Nat) = 22)
          (locals_upd_extract 21 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) 0 (by decide : ¬ (0 : Nat) = 21)
            (locals_upd_extract 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) 0 (by decide : ¬ (0 : Nat) = 20) hl0)))
      have h2_1 : s4.locals 2 = some (.ptr 2 0) := locals_upd_extract 6 (.int ⟨32, false⟩ 0) 2 (by decide : ¬ (2 : Nat) = 6)
        (locals_upd_extract 22 (.int ⟨64, false⟩ (y * h.width * h.channels)) 2 (by decide : ¬ (2 : Nat) = 22)
          (locals_upd_extract 21 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) 2 (by decide : ¬ (2 : Nat) = 21)
            (locals_upd_extract 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) 2 (by decide : ¬ (2 : Nat) = 20) hl2)))
      have h3_1 : s4.locals 3 = some (.ptr ob 0) := locals_upd_extract 6 (.int ⟨32, false⟩ 0) 3 (by decide : ¬ (3 : Nat) = 6)
        (locals_upd_extract 22 (.int ⟨64, false⟩ (y * h.width * h.channels)) 3 (by decide : ¬ (3 : Nat) = 22)
          (locals_upd_extract 21 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) 3 (by decide : ¬ (3 : Nat) = 21)
            (locals_upd_extract 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) 3 (by decide : ¬ (3 : Nat) = 20) hl3)))
      have h6_1 : s4.locals 6 = some (.int ⟨32, false⟩ 0) := by
        rw [show s4.locals = s3.locals.upd 6 (.int ⟨32, false⟩ 0) from rfl]
        rw [Locals.upd_same]
      have h9_1 : s4.locals 9 = some (.int ⟨64, false⟩ h.channels) := locals_upd_extract 6 (.int ⟨32, false⟩ 0) 9 (by decide : ¬ (9 : Nat) = 6)
        (locals_upd_extract 22 (.int ⟨64, false⟩ (y * h.width * h.channels)) 9 (by decide : ¬ (9 : Nat) = 22)
          (locals_upd_extract 21 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) 9 (by decide : ¬ (9 : Nat) = 21)
            (locals_upd_extract 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) 9 (by decide : ¬ (9 : Nat) = 20) hl9)))
      have h19_1 : s4.locals 19 = some (.int ⟨64, false⟩ h.channels) := locals_upd_extract 6 (.int ⟨32, false⟩ 0) 19 (by decide : ¬ (19 : Nat) = 6)
        (locals_upd_extract 22 (.int ⟨64, false⟩ (y * h.width * h.channels)) 19 (by decide : ¬ (19 : Nat) = 22)
          (locals_upd_extract 21 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) 19 (by decide : ¬ (19 : Nat) = 21)
            (locals_upd_extract 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) 19 (by decide : ¬ (19 : Nat) = 20) hl19)))
      have h25_1 : s4.locals 25 = some (.int ⟨32, true⟩ 0) := locals_upd_extract 6 (.int ⟨32, false⟩ 0) 25 (by decide : ¬ (25 : Nat) = 6)
        (locals_upd_extract 22 (.int ⟨64, false⟩ (y * h.width * h.channels)) 25 (by decide : ¬ (25 : Nat) = 22)
          (locals_upd_extract 21 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) 25 (by decide : ¬ (25 : Nat) = 21)
            (locals_upd_extract 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) 25 (by decide : ¬ (25 : Nat) = 20) hl25)))
      have h12_1 : s4.locals 12 = some (.int ⟨64, false⟩ h.paletteOffset) := locals_upd_extract 6 (.int ⟨32, false⟩ 0) 12 (by decide : ¬ (12 : Nat) = 6)
        (locals_upd_extract 22 (.int ⟨64, false⟩ (y * h.width * h.channels)) 12 (by decide : ¬ (12 : Nat) = 22)
          (locals_upd_extract 21 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) 12 (by decide : ¬ (12 : Nat) = 21)
            (locals_upd_extract 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) 12 (by decide : ¬ (12 : Nat) = 20) hl12)))
      have h13_1 : s4.locals 13 = some (.int ⟨64, false⟩ h.paletteEntries) := locals_upd_extract 6 (.int ⟨32, false⟩ 0) 13 (by decide : ¬ (13 : Nat) = 6)
        (locals_upd_extract 22 (.int ⟨64, false⟩ (y * h.width * h.channels)) 13 (by decide : ¬ (13 : Nat) = 22)
          (locals_upd_extract 21 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) 13 (by decide : ¬ (13 : Nat) = 21)
            (locals_upd_extract 20 (.int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y)) 13 (by decide : ¬ (13 : Nat) = 20) hl13)))
      have h21_1 : s4.locals 21 = some (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) := by
        rw [show s4.locals = s3.locals.upd 6 (.int ⟨32, false⟩ 0) from rfl,
            show s3.locals = s2.locals.upd 22 (.int ⟨64, false⟩ (y * h.width * h.channels)) from rfl,
            show s2.locals = s1.locals.upd 21 (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) from rfl]
        rw [Locals.upd_ne _ _ (by decide : ¬ (21 : Nat) = 6), Locals.upd_ne _ _ (by decide : ¬ (21 : Nat) = 22), Locals.upd_same]
      have h22_1 : s4.locals 22 = some (.int ⟨64, false⟩ (y * h.width * h.channels)) := by
        rw [show s4.locals = s3.locals.upd 6 (.int ⟨32, false⟩ 0) from rfl,
            show s3.locals = s2.locals.upd 22 (.int ⟨64, false⟩ (y * h.width * h.channels)) from rfl]
        rw [Locals.upd_ne _ _ (by decide : ¬ (22 : Nat) = 6), Locals.upd_same]
      -- locals 5 for the inner call
      have h5_3 : s4.locals 5 = some (.int ⟨32, false⟩ y) :=
        locals_upd_extract 6 (.int ⟨32, false⟩ 0) 5 (by decide : ¬ (5 : Nat) = 6) h5_2
      have hmem_inner : s4.mem ob = some (bmpRowsBytes d h y ++ rowOut d h y 0 ++ (bmpRowsBytes d h y ++ obl.drop (y * (h.width * h.channels))).drop ((y * h.width + 0) * h.channels)) := by
        have r0 : rowOut d h y 0 = [] := rfl
        have e : (y * h.width + 0) * h.channels = y * (h.width * h.channels) := by
          rw [Nat.add_zero, Nat.mul_assoc]
        have hlenA : (bmpRowsBytes d h y).length = y * (h.width * h.channels) := hAblen
        rw [r0, List.append_nil]
        rw [e]
        have dropA : List.drop (y * (h.width * h.channels)) (bmpRowsBytes d h y ++ obl.drop (y * (h.width * h.channels)))
            = List.drop 0 (obl.drop (y * (h.width * h.channels))) := by
          rw [show y * (h.width * h.channels) = (bmpRowsBytes d h y).length from hAblen.symm]
          exact drop_append_length _ _ 0
        show ((s.mem) (ob)) = some _
        rw [show s.mem ob = bmpRowsBytes d h y ++ obl.drop (y * (h.width * h.channels)) from smem]
        rw [dropA]
        rfl
      obtain ⟨sI, hLoopI, hMemI, hLocI, hPresI, hMemI_bd, hMemI_2, hRO', hLoc25'⟩ := loop2_iter s4.mem d
        (bmpRowsBytes d h y ++ obl.drop (y * (h.width * h.channels)))
        bd ob (by rw [hMemS4]; exact hmem2) hd hobP
        hd0 ho2 bd2 info (by rw [hMemS4]; exact smem2) h48
        h hn8 hc3 hc32 hw hwv y houtP hlenP
        hylt hok_row hbok ro hro
        (h.width - 0) 0 s4
        (fun i hi1 hi2 => hsrc y i hylt hi2)
        (by omega) (by omega)
        h0_1 h2_1 h3_1 h5_3 h6_1 h9_1 h19_1 h21_1 h22_1 h25_1 hros
        hmem_inner hbdP hbdP2
      have hMemI' : sI.mem ob = some (bmpRowsBytes d h (y + 1) ++ obl.drop ((y + 1) * (h.width * h.channels))) := by
        rw [hMemI, dropB]
      -- ==== step: y := y + 1 ====
      have hCastY' : evalCast ⟨32, false⟩ (.int ⟨32, false⟩ y) = .ok (.int ⟨32, false⟩ y) := u32_u32_cast y (by omega)
      have hAdd5 : EvE Gen.prog sI (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5)) (.const (.int ⟨32, false⟩ 1))) (.int ⟨32, false⟩ (y + 1)) :=
        EvE.bin (EvE.cast (EvE.var hLocI) hCastY') (EvE.const _) (bin_u32_add y 1 (by omega))
      have hCastY2 : evalCast ⟨32, false⟩ (.int ⟨32, false⟩ (y + 1)) = .ok (.int ⟨32, false⟩ (y + 1)) := u32_u32_cast (y + 1) (by omega)
      have hSet5 : ExS Gen.prog sI
          (.set 5 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5)) (.const (.int ⟨32, false⟩ 1)))))
          .normal { sI with locals := sI.locals.upd 5 (.int ⟨32, false⟩ (y + 1)) } :=
        ExS.set (EvE.cast hAdd5 hCastY2)
      let s5 : State := { sI with locals := sI.locals.upd 5 (.int ⟨32, false⟩ (y + 1)) }
      have hMem5 : s5.mem ob = some (bmpRowsBytes d h (y + 1) ++ obl.drop ((y + 1) * (h.width * h.channels))) := by
        show (sI.mem ob) = some _
        exact hMemI' 
      have hMem5bd : s5.mem bd = some d := by
        show (sI.mem bd) = some d
        rw [hMemI_bd]
        rw [show s4.mem = s.mem from rfl]
        exact hmem2
      have hMem5_2 : s5.mem 2 = some info := by
        show (sI.mem 2) = some info
        rw [hMemI_2]
        rw [show s4.mem = s.mem from rfl]
        exact smem2
      -- locals facts for the recursive call
      have hl0_5 : s5.locals 0 = some (.ptr bd 0) := locals_upd_extract 5 (.int ⟨32, false⟩ (y + 1)) 0 (by decide : ¬ (0 : Nat) = 5) (hPresI 0 (by decide : ¬ (0 : Nat) = 6) (by decide : ¬ (0 : Nat) = 23) (by decide : ¬ (0 : Nat) = 24) (by decide : ¬ (0 : Nat) = 25) |>.trans h0_1)
      have hl2_5 : s5.locals 2 = some (.ptr 2 0) := locals_upd_extract 5 (.int ⟨32, false⟩ (y + 1)) 2 (by decide : ¬ (2 : Nat) = 5) (hPresI 2 (by decide : ¬ (2 : Nat) = 6) (by decide : ¬ (2 : Nat) = 23) (by decide : ¬ (2 : Nat) = 24) (by decide : ¬ (2 : Nat) = 25) |>.trans h2_1)
      have hl3_5 : s5.locals 3 = some (.ptr ob 0) := locals_upd_extract 5 (.int ⟨32, false⟩ (y + 1)) 3 (by decide : ¬ (3 : Nat) = 5) (hPresI 3 (by decide : ¬ (3 : Nat) = 6) (by decide : ¬ (3 : Nat) = 23) (by decide : ¬ (3 : Nat) = 24) (by decide : ¬ (3 : Nat) = 25) |>.trans h3_1)
      have hl5_5 : s5.locals 5 = some (.int ⟨32, false⟩ (y + 1)) := by
        rw [show s5.locals = sI.locals.upd 5 (.int ⟨32, false⟩ (y + 1)) from rfl]
        rw [Locals.upd_same]
      have hl7_5 : s5.locals 7 = some (.int ⟨64, false⟩ h.width) := locals_upd_extract 5 (.int ⟨32, false⟩ (y + 1)) 7 (by decide : ¬ (7 : Nat) = 5) (hPresI 7 (by decide : ¬ (7 : Nat) = 6) (by decide : ¬ (7 : Nat) = 23) (by decide : ¬ (7 : Nat) = 24) (by decide : ¬ (7 : Nat) = 25) |>.trans h7_2)
      have hl8_5 : s5.locals 8 = some (.int ⟨64, false⟩ h.height) := locals_upd_extract 5 (.int ⟨32, false⟩ (y + 1)) 8 (by decide : ¬ (8 : Nat) = 5) (hPresI 8 (by decide : ¬ (8 : Nat) = 6) (by decide : ¬ (8 : Nat) = 23) (by decide : ¬ (8 : Nat) = 24) (by decide : ¬ (8 : Nat) = 25) |>.trans hl8)
      have hl9_5 : s5.locals 9 = some (.int ⟨64, false⟩ h.channels) := locals_upd_extract 5 (.int ⟨32, false⟩ (y + 1)) 9 (by decide : ¬ (9 : Nat) = 5) (hPresI 9 (by decide : ¬ (9 : Nat) = 6) (by decide : ¬ (9 : Nat) = 23) (by decide : ¬ (9 : Nat) = 24) (by decide : ¬ (9 : Nat) = 25) |>.trans h9_1)
      have hl10_5 : s5.locals 10 = some (.int ⟨64, false⟩ h.rowStride) := locals_upd_extract 5 (.int ⟨32, false⟩ (y + 1)) 10 (by decide : ¬ (10 : Nat) = 5) (hPresI 10 (by decide : ¬ (10 : Nat) = 6) (by decide : ¬ (10 : Nat) = 23) (by decide : ¬ (10 : Nat) = 24) (by decide : ¬ (10 : Nat) = 25) |>.trans hl10)
      have hl11_5 : s5.locals 11 = some (.int ⟨64, false⟩ h.pixelOffset) := locals_upd_extract 5 (.int ⟨32, false⟩ (y + 1)) 11 (by decide : ¬ (11 : Nat) = 5) (hPresI 11 (by decide : ¬ (11 : Nat) = 6) (by decide : ¬ (11 : Nat) = 23) (by decide : ¬ (11 : Nat) = 24) (by decide : ¬ (11 : Nat) = 25) |>.trans hl11)
      have hl12_5 : s5.locals 12 = some (.int ⟨64, false⟩ h.paletteOffset) := locals_upd_extract 5 (.int ⟨32, false⟩ (y + 1)) 12 (by decide : ¬ (12 : Nat) = 5) (hPresI 12 (by decide : ¬ (12 : Nat) = 6) (by decide : ¬ (12 : Nat) = 23) (by decide : ¬ (12 : Nat) = 24) (by decide : ¬ (12 : Nat) = 25) |>.trans h12_1)
      have hl13_5 : s5.locals 13 = some (.int ⟨64, false⟩ h.paletteEntries) := locals_upd_extract 5 (.int ⟨32, false⟩ (y + 1)) 13 (by decide : ¬ (13 : Nat) = 5) (hPresI 13 (by decide : ¬ (13 : Nat) = 6) (by decide : ¬ (13 : Nat) = 23) (by decide : ¬ (13 : Nat) = 24) (by decide : ¬ (13 : Nat) = 25) |>.trans h13_1)
      have hl19_5 : s5.locals 19 = some (.int ⟨64, false⟩ h.channels) := locals_upd_extract 5 (.int ⟨32, false⟩ (y + 1)) 19 (by decide : ¬ (19 : Nat) = 5) (hPresI 19 (by decide : ¬ (19 : Nat) = 6) (by decide : ¬ (19 : Nat) = 23) (by decide : ¬ (19 : Nat) = 24) (by decide : ¬ (19 : Nat) = 25) |>.trans h19_1)
      have hl21_5 : s5.locals 21 = some (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) := locals_upd_extract 5 (.int ⟨32, false⟩ (y + 1)) 21 (by decide : ¬ (21 : Nat) = 5) (hPresI 21 (by decide : ¬ (21 : Nat) = 6) (by decide : ¬ (21 : Nat) = 23) (by decide : ¬ (21 : Nat) = 24) (by decide : ¬ (21 : Nat) = 25) |>.trans h21_1)
      have hl22_5 : s5.locals 22 = some (.int ⟨64, false⟩ (y * h.width * h.channels)) := locals_upd_extract 5 (.int ⟨32, false⟩ (y + 1)) 22 (by decide : ¬ (22 : Nat) = 5) (hPresI 22 (by decide : ¬ (22 : Nat) = 6) (by decide : ¬ (22 : Nat) = 23) (by decide : ¬ (22 : Nat) = 24) (by decide : ¬ (22 : Nat) = 25) |>.trans h22_1)
      have hl25_5 : s5.locals 25 = some (.int ⟨32, true⟩ 0) := locals_upd_extract 5 (.int ⟨32, false⟩ (y + 1)) 25 (by decide : ¬ (25 : Nat) = 5) hLoc25'
      have hS5ro : s5.ro = s.ro := by
        rw [show s5.ro = sI.ro from rfl, hRO',
            show s4.ro = s3.ro from rfl,
            show s3.ro = s2.ro from rfl,
            show s2.ro = s1.ro from rfl,
            show s1.ro = s.ro from rfl]
      -- ==== recursive call ====
      obtain ⟨s', hLoop', hMem'⟩ := ih (y + 1) s5
        (by omega) (by omega)
        hl0_5 hl2_5 hl3_5 hl5_5 hl7_5 hl8_5 hl9_5 hl10_5 hl11_5 hl12_5 hl13_5 hl19_5 hl25_5
        (by rw [hS5ro]; exact hros)
        (by rw [show s5.mem ob = bmpRowsBytes d h (y + 1) ++ obl.drop ((y + 1) * (h.width * h.channels)) from hMem5])
        hMem5bd hMem5_2
      refine ⟨s', ?_, hMem'⟩
      show ExS Gen.prog s Gen.ni_bmp_decode_into_loop3 .normal s'
      have hBody : ExS Gen.prog s
          (.ite (.bin .lt (some ⟨32, false⟩) (.var 5) (.load (.int ⟨32, false⟩) (.field (.var 2) 28)))
            (.seq (.set 20 (.cond (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 2) 43))) (.cast ⟨64, false⟩ (.var 5)) (.bin .sub (some ⟨64, false⟩) (.bin .sub (some ⟨64, false⟩) (.var 8) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) (.cast ⟨64, false⟩ (.var 5)))))
              (.seq (.set 21 (.bin .add (some ⟨64, false⟩) (.var 11) (.bin .mul (some ⟨64, false⟩) (.var 20) (.var 10))))
                (.seq (.set 22 (.bin .mul (some ⟨64, false⟩) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 5)) (.var 7)) (.var 9)))
                  (.seq (.set 6 (.const (.int ⟨32, false⟩ 0))) Gen.ni_bmp_decode_into_loop2))))
            .brk)
          .normal sI :=
        ExS.ite hCond truthy_true (ExS.seq hSet20 (ExS.seq hSet21 (ExS.seq hSet22 (ExS.seq hSet6
                    (show ExS Gen.prog s4 Gen.ni_bmp_decode_into_loop2 Outcome.normal sI from hLoopI)))))
      show ExS Gen.prog s Gen.ni_bmp_decode_into_loop3 .normal s'
      exact ExS.loop_next hBody (Or.inl rfl) hSet5 hLoop'

/-- The outer 24/32-bit row loop of `ni_bmp_decode_into`, all-pixels-OK case:
    runs through all height rows, leaving the completed output rows in `out`.
    Locals: 0=bytes, 1=size, 2=info, 3=out, 4=out_cap, 5=y, 6=x,
    7=width, 8=height, 9=channels, 10=row_stride, 11=pixel_offset,
    12=palette_offset, 13=palette_entries, 14=src_y, 15=src_base,
    16=dst_base, 17=code, 18=dst, 19=src_channels, 20=src_y,
    21=src_base, 22=dst_base, 23=s, 24=d, 25=code -/
theorem ni_bmp_decode_into_loop3_ok_exs (m : Mem) (d obl : List UInt8)
    (bd ob : Nat) (hm : m bd = some d) (hd : d.length < 2 ^ 64)
    (hob : m ob = some obl) (hd0 : bd ≠ ob) (ho2 : 2 ≠ ob) (bd2 : 2 ≠ bd)
    (info : List UInt8) (hinfo : m 2 = some info) (h48 : info.length = 48)
    (h : BmpInfo) (hn8 : h.bitCount ≠ 8)
    (hc3 : h.channels = 3 ∨ h.channels = 4)
    (hc32 : h.channels = (if h.bitCount = 32 then 4 else 3))
    (hw : (info.drop 24).take 4 = encodeLE 4 h.width) (hwv : h.width < 4294967296)
    (hht : (info.drop 28).take 4 = encodeLE 4 h.height) (hhtwv : h.height < 4294967296)
    (htop : (info.drop 43).take 1 = encodeLE 1 h.topDown)
    (htopd : h.topDown = 0 ∨ h.topDown = 1)
    (hout : h.height * (h.width * h.channels) ≤ obl.length)
    (hlen : obl.length < 2 ^ 64)
    (hsrc : ∀ y i, y < h.height → i < h.width → h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + i * h.channels + h.channels ≤ d.length)
    (hok : ∀ y i, y < h.height → i < h.width → ∃ bs, bmpPixel d h y i = .ok bs)
    (hwidth : 1 ≤ h.width)
    (ro : Bool) (hro : ro = false)
    (hmo : m ob = some obl) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
        ([.ptr bd 0, .int ⟨64, false⟩ d.length, .ptr 2 0, .ptr ob 0, .int ⟨64, false⟩ obl.length,
          .int ⟨32, false⟩ 0, .int ⟨32, false⟩ 0,
          .int ⟨64, false⟩ h.width, .int ⟨64, false⟩ h.height, .int ⟨64, false⟩ h.channels,
          .int ⟨64, false⟩ h.rowStride, .int ⟨64, false⟩ h.pixelOffset,
          .int ⟨64, false⟩ h.paletteOffset, .int ⟨64, false⟩ h.paletteEntries,
          .int ⟨64, false⟩ 0,
          .int ⟨64, false⟩ 0,
          .int ⟨64, false⟩ 0,
          .int ⟨32, true⟩ 0,
          .int ⟨64, false⟩ 0,
          .int ⟨64, false⟩ h.channels,
          .int ⟨64, false⟩ 0,
          .int ⟨64, false⟩ 0,
          .int ⟨64, false⟩ 0,
          .int ⟨64, false⟩ 0,
          .int ⟨64, false⟩ 0,
          .int ⟨32, true⟩ 0] : List Val), m, ro⟩
      Gen.ni_bmp_decode_into_loop3
      (.normal) s' ∧
    s'.mem ob = some
      (bmpRowsBytes d h h.height ++ obl.drop (h.height * (h.width * h.channels))) := by
  have hmem0 : m ob = some (bmpRowsBytes d h 0 ++ obl.drop (0 * (h.width * h.channels))) := by
    simp only [bmpRowsBytes_zero, Nat.zero_mul, List.drop_zero, List.nil_append]
    exact hob
  have hiter := loop3_iter m d obl bd ob hm hd hob hd0 ho2 bd2 info hinfo h48 h hn8 hc3 hc32 hw hwv hht hhtwv htop htopd hout hlen hsrc hok hwidth ro hro
    (h.height) (0 : Nat) ⟨frameLocals [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
        ([.ptr bd 0, .int ⟨64, false⟩ d.length, .ptr 2 0, .ptr ob 0, .int ⟨64, false⟩ obl.length,
          .int ⟨32, false⟩ 0, .int ⟨32, false⟩ 0,
          .int ⟨64, false⟩ h.width, .int ⟨64, false⟩ h.height, .int ⟨64, false⟩ h.channels,
          .int ⟨64, false⟩ h.rowStride, .int ⟨64, false⟩ h.pixelOffset,
          .int ⟨64, false⟩ h.paletteOffset, .int ⟨64, false⟩ h.paletteEntries,
          .int ⟨64, false⟩ 0,
          .int ⟨64, false⟩ 0,
          .int ⟨64, false⟩ 0,
          .int ⟨32, true⟩ 0,
          .int ⟨64, false⟩ 0,
          .int ⟨64, false⟩ h.channels,
          .int ⟨64, false⟩ 0,
          .int ⟨64, false⟩ 0,
          .int ⟨64, false⟩ 0,
          .int ⟨64, false⟩ 0,
          .int ⟨64, false⟩ 0,
          .int ⟨32, true⟩ 0] : List Val), m, ro⟩
    (by omega) (by omega)
    (by simp only [frameLocals_apply]; rfl) (by simp only [frameLocals_apply]; rfl) (by simp only [frameLocals_apply]; rfl)
    (by simp only [frameLocals_apply]; rfl) (by simp only [frameLocals_apply]; rfl) (by simp only [frameLocals_apply]; rfl)
    (by simp only [frameLocals_apply]; rfl) (by simp only [frameLocals_apply]; rfl) (by simp only [frameLocals_apply]; rfl)
    (by simp only [frameLocals_apply]; rfl) (by simp only [frameLocals_apply]; rfl) (by simp only [frameLocals_apply]; rfl) (by simp only [frameLocals_apply]; rfl)
    hro hmem0 hm hinfo
  obtain ⟨s', hLoop', hMem'⟩ := hiter
  exact ⟨s', hLoop', hMem'⟩


end NANO.C.Proofs
