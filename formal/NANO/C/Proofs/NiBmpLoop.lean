/-
  BMP decode-into loop refinement proofs — the nested x/y loops of
  `ni_bmp_decode_into`, built on the per-pixel helper proofs.
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

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 800000

namespace NANO.C.Proofs
open NANO NANO.C

/-- Load u32 at `.ptr b off` from an arbitrary length block. -/
theorem load_u32_field (m : Mem) (b : Nat) (blk : List UInt8) (hm : m b = some blk)
    (len : blk.length = 48) (off : Nat) (hoff : off + 4 ≤ 48)
    (nval : Nat) (slice_eq : (blk.drop off).take 4 = encodeLE 4 nval)
    (hv : nval < 4294967296) :
    load m (.int ⟨32, false⟩) (.ptr b off) = .ok (Val.int ⟨32, false⟩ nval) := by
  simp only [load, Ty.size]
  simp only [readBytes]
  rw [hm]
  have hsz : (Ty.int { width := 32, signed := false }).size = 4 := rfl
  have hBytes : IntTy.bytes { width := 32, signed := false } = 4 := rfl
  simp only [hsz, hBytes]
  rw [if_pos (show off + 4 ≤ blk.length from by rw [len]; omega)]
  rw [slice_eq]
  simp [decodeLE_encodeLE, Nat.mod_eq_of_lt hv]

/-- Load u16 at `.ptr b off` from an arbitrary length block. -/
theorem load_u16_field (m : Mem) (b : Nat) (blk : List UInt8) (hm : m b = some blk)
    (len : blk.length = 48) (off : Nat) (hoff : off + 2 ≤ 48)
    (nval : Nat) (slice_eq : (blk.drop off).take 2 = encodeLE 2 nval)
    (hv : nval < 65536) :
    load m (.int ⟨16, false⟩) (.ptr b off) = .ok (Val.int ⟨16, false⟩ nval) := by
  simp only [load, Ty.size]
  simp only [readBytes]
  rw [hm]
  have hsz : (Ty.int { width := 16, signed := false }).size = 2 := rfl
  have hBytes : IntTy.bytes { width := 16, signed := false } = 2 := rfl
  simp only [hsz, hBytes]
  rw [if_pos (show off + 2 ≤ blk.length from by rw [len]; omega)]
  rw [slice_eq]
  simp [decodeLE_encodeLE, Nat.mod_eq_of_lt hv]

/-- Load u8 at `.ptr b off` from an arbitrary length block. -/
theorem load_u8_field (m : Mem) (b : Nat) (blk : List UInt8) (hm : m b = some blk)
    (len : blk.length = 48) (off : Nat) (hoff : off + 1 ≤ 48)
    (nval : Nat) (slice_eq : (blk.drop off).take 1 = encodeLE 1 nval)
    (hv : nval < 256) :
    load m (.int ⟨8, false⟩) (.ptr b off) = .ok (Val.int ⟨8, false⟩ nval) := by
  simp only [load, Ty.size]
  simp only [readBytes]
  rw [hm]
  have hsz : (Ty.int { width := 8, signed := false }).size = 1 := rfl
  have hBytes : IntTy.bytes { width := 8, signed := false } = 1 := rfl
  simp only [hsz, hBytes]
  rw [if_pos (show off + 1 ≤ blk.length from by rw [len]; omega)]
  rw [slice_eq]
  simp [decodeLE_encodeLE, Nat.mod_eq_of_lt hv]

/-- Load u64 at `.ptr b off` from an arbitrary length block. -/
theorem load_u64_field (m : Mem) (b : Nat) (blk : List UInt8) (hm : m b = some blk)
    (len : blk.length = 48) (off : Nat) (hoff : off + 8 ≤ 48)
    (nval : Nat) (slice_eq : (blk.drop off).take 8 = encodeLE 8 nval)
    (hv : nval < 18446744073709551616) :
    load m (.int ⟨64, false⟩) (.ptr b off) = .ok (Val.int ⟨64, false⟩ nval) := by
  simp only [load, Ty.size]
  simp only [readBytes]
  rw [hm]
  have hsz : (Ty.int { width := 64, signed := false }).size = 8 := rfl
  have hBytes : IntTy.bytes { width := 64, signed := false } = 8 := rfl
  simp only [hsz, hBytes]
  rw [if_pos (show off + 8 ≤ blk.length from by rw [len]; omega)]
  rw [slice_eq]
  simp [decodeLE_encodeLE, Nat.mod_eq_of_lt hv]


/-- One row `y` of finished output bytes equals the row bytes. -/
theorem bmpRowsBytes_succ_flat (d : List UInt8) (h : BmpInfo) (y : Nat) :
    bmpRowsBytes d h y ++ bmpRowBytes d h y = bmpRowsBytes d h (y + 1) :=
  (bmpRowsBytes_succ d h y).symm

theorem bin_u32_add (n k : Nat) (h : n + k < 2 ^ 32) :
    evalBin .add (some ⟨32, false⟩) (.int ⟨32, false⟩ n) (.int ⟨32, false⟩ k)
      = .ok (.int ⟨32, false⟩ (n + k)) := by
  simp [evalBin, evalBinInt, binInt, IntTy.modulus, isPtr, ptrEq, intOf, Int.ofNat_lt, h]

theorem u32_u32_cast (n : Nat) (h : n < 2 ^ 32) :
    evalCast ⟨32, false⟩ (.int ⟨32, false⟩ n) = .ok (.int ⟨32, false⟩ n) := by
  simp [evalCast, IntTy.modulus, IntTy.wrap, Int.ofNat_lt, h]

/-- `encodeLE 1` of a byteAt is the single byte itself. -/
theorem encodeLE_one_byteAt (d : List UInt8) (j : Nat) :
    encodeLE 1 (byteAt d j) = [d.getD j 0] := by
  simp [encodeLE, Nat.mod_eq_of_lt (byteAt_lt d j), byteAt_toUInt8]


/-- A successful 8-bit pixel expands to `bmpPixelSize h` bytes. -/
theorem bmpPixel_ok_len_8bit (d : List UInt8) (h : BmpInfo) (yy x : Nat)
    (hd8 : h.bitCount = 8) (bs : List UInt8)
    (hbs : bmpPixel d h yy x = .ok bs) :
    bs.length = bmpPixelSize h :=
  bmpPixel_8bit_length d h yy x hd8 bs hbs

theorem locals_upd_extract {l : Locals} (i : Nat) (v : Val) (j : Nat) (h : j ≠ i) {u : Val} (hj : l j = some u) :
    (l.upd i v) j = some u := by
  rw [Locals.upd_ne l v h]
  exact hj

/-- Induction principle for the 8-bit inner row loop: with the row invariant
    at counter `x`, running the loop stores the remaining pixels and ends
    `.brk`-terminated at `width`. -/
theorem loop0_iter (m : Mem) (d obl : List UInt8)
    (bd ob : Nat) (hm : m bd = some d) (hd : d.length < 2 ^ 64)
    (hob : m ob = some obl) (hd0 : bd ≠ ob) (ho2 : 3 ≠ ob) (bd2 : 3 ≠ bd)
    (info : List UInt8) (hinfo : m 3 = some info) (h48 : info.length = 48)
    (h : BmpInfo) (hbc : h.bitCount = 8)
    (hw : (info.drop 24).take 4 = encodeLE 4 h.width) (hwv : h.width < 4294967296)
    (y : Nat)
    (hout : (y + 1) * h.width * 3 ≤ obl.length)
    (hlen : obl.length < 2 ^ 64)
    (hy : y < h.height)
    (hok_row : ∀ i, i < h.width → ∃ bs, bmpPixel d h y i = .ok bs)
    (hok_rows : ∀ yy i, yy < y → i < h.width → ∃ bs, bmpPixel d h yy i = .ok bs)
    (ro : Bool) (hro : ro = false) :
    ∀ (n : Nat) (x : Nat) (s : State),
      (hsrc : ∀ i, x ≤ i → i < h.width → h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + i < d.length) →
      (hpal : ∀ i, x ≤ i → i < h.width → h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + i) * 4 + 3 ≤ d.length) →
      (hidx : ∀ i, x ≤ i → i < h.width → byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + i) < h.paletteEntries) →
      h.width - x = n →
      x ≤ h.width →
      s.locals 0 = some (.ptr bd 0) →
      s.locals 2 = some (.ptr 3 0) →
      s.locals 3 = some (.ptr ob 0) →
      s.locals 5 = some (.int ⟨32, false⟩ y) →
      s.locals 6 = some (.int ⟨32, false⟩ x) →
      s.locals 12 = some (.int ⟨64, false⟩ h.paletteOffset) →
      s.locals 13 = some (.int ⟨64, false⟩ h.paletteEntries) →
      s.locals 15 = some (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) →
      s.locals 16 = some (.int ⟨64, false⟩ (y * h.width * 3)) →
      s.ro = false →
      s.mem ob = some (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * 3)) →
      s.mem bd = some d →
      s.mem 3 = some info →
      ∃ s', ExS Gen.prog s Gen.ni_bmp_decode_into_loop0 .normal s' ∧
        s'.mem ob = some (bmpRowsBytes d h (y + 1) ++ obl.drop ((y + 1) * (h.width * 3))) ∧
        s'.locals 5 = some (.int ⟨32, false⟩ y) ∧
        (∀ j, j ≠ 6 → j ≠ 17 → j ≠ 18 → s'.locals j = s.locals j) ∧
        s'.mem bd = s.mem bd ∧
        s'.mem 3 = s.mem 3 ∧
        s'.ro = s.ro := by
  intro n
  induction n with
  | zero =>
      intro x s hsrc hpal hidx hZero hx hl0 hl2 hl3 hl5 hl6 hl12 hl13 hl15 hl16 hros smem hmem2 smem2
      have hxeq : x = h.width := by omega
      subst hxeq
      have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
      have hLoad : EvE Gen.prog s (.load (.int ⟨32, false⟩) (.field (.var 2) 24)) (.int ⟨32, false⟩ h.width) := by
        have hField : EvE Gen.prog s (.field (.var 2) 24) (.ptr 3 24) :=
          EvE.field (EvE.var hl2)
            (ptrAddN_ok smem2 (by omega))
        exact EvE.load hField (load_u32_field s.mem 3 info smem2 h48 24 (by omega) h.width hw hwv)
      have hCond : EvE Gen.prog s (.bin .lt (some ⟨32, false⟩) (.var 6) (.load (.int ⟨32, false⟩) (.field (.var 2) 24))) (boolVal false) := by
        have hdec : decide (h.width < h.width) = false := decide_eq_false (by omega)
        exact EvE.bin (EvE.var hl6) hLoad
          (by rw [bin_u32_lt, hdec])
      have hIf : ExS Gen.prog s
          (.ite (.bin .lt (some ⟨32, false⟩) (.var 6) (.load (.int ⟨32, false⟩) (.field (.var 2) 24)))
            (.seq (.set 18 (.bin .add (some ⟨64, false⟩) (.var 16) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3))))))
              (.seq (.call (some 17) 19 [(.var 0), (.var 3), (.var 15), (.cast ⟨64, false⟩ (.var 6)), (.var 18), (.var 12), (.var 13)])
                (.ite (.bin .ne (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0))) (.ret (some (.var 17))) .skip)))
            .brk)
          .brk s :=
        ExS.ite hCond truthy_false ExS.brk
      have hLoop : ExS Gen.prog s Gen.ni_bmp_decode_into_loop0 .normal s := by
        show ExS Gen.prog s (.loop (.ite (.bin .lt (some ⟨32, false⟩) (.var 6) (.load (.int ⟨32, false⟩) (.field (.var 2) 24))) (.seq (.set 18 (.bin .add (some ⟨64, false⟩) (.var 16) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3)))))) (.seq (.call (some 17) 19 [(.var 0), (.var 3), (.var 15), (.cast ⟨64, false⟩ (.var 6)), (.var 18), (.var 12), (.var 13)]) (.ite (.bin .ne (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0))) (.ret (some (.var 17))) .skip))) .brk) (.set 6 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 1)))))) .normal s
        exact ExS.loop_brk hIf
      refine ⟨s, hLoop, ?_, ?_, ?_, ?_, ?_, ?_⟩
      have e1 : (y * h.width + h.width) * 3 = y * h.width * 3 + h.width * 3 := Nat.add_mul (y * h.width) h.width 3
      have e2 : (y + 1) * (h.width * 3) = y * h.width * 3 + h.width * 3 := by
        rw [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc]
      rw [smem, rowOut_width, bmpRowsBytes_succ_flat, e1, ← e2]
      exact hl5
      intro j h6 h17 h18; rfl
      rfl
      rfl
      rfl

  | succ k ih =>
      intro x s hsrc hpal hidx hSucc hx hl0 hl2 hl3 hl5 hl6 hl12 hl13 hl15 hl16 hros smem hmem2 smem2
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
      -- set 18: dst := dst_base + x * 3
      have hCastX : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ x) = .ok (.int ⟨64, false⟩ x) :=
        u32_u64_cast x (by omega)
      have hMul : EvE Gen.prog s (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3)))) (.int ⟨64, false⟩ (x * 3)) :=
        EvE.bin (EvE.cast (EvE.var hl6) hCastX)
          (EvE.cast (EvE.const _) (u32_u64_cast 3 (by omega))) (bin_u64_mul x 3 (by omega))
      have hAdd : EvE Gen.prog s (.bin .add (some ⟨64, false⟩) (.var 16) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3))))) (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) :=
        EvE.bin (EvE.var hl16) hMul
          (bin_u64_add (y * h.width * 3) (x * 3) (by
            have h1 : y * h.width + x ≤ (y + 1) * h.width := by
              rw [Nat.add_mul, Nat.one_mul]
              omega
            have h2 : (y * h.width + x) * 3 ≤ (y + 1) * h.width * 3 :=
              Nat.mul_le_mul_right (k := 3) h1
            have h3 : (y * h.width + x) * 3 = y * h.width * 3 + x * 3 :=
              Nat.add_mul (y * h.width) x 3
            rw [h3] at h2
            omega))
      have hSet18 : ExS Gen.prog s
          (.set 18 (.bin .add (some ⟨64, false⟩) (.var 16) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3))))))
          .normal { s with locals := s.locals.upd 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) } :=
        ExS.set hAdd
      let s1 : State := { s with locals := s.locals.upd 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) }
      -- ==== call ni_bmp_decode_indexed_pixel(bytes, out, src_base, x, dst, ...) ====
      have hMemS1 : s1.mem = s.mem := rfl
      have hlen_px : ∀ x bs, bmpPixel d h y x = .ok bs → bs.length = bmpPixelSize h :=
        fun x bs hbs => bmpPixel_8bit_length d h y x hbc bs hbs
      have hlen_px2 : ∀ yy x bs, bmpPixel d h yy x = .ok bs → bs.length = bmpPixelSize h :=
        fun yy x bs hbs => bmpPixel_8bit_length d h yy x hbc bs hbs
      have hArows : (bmpRowsBytes d h y).length = y * bmpRowSize h :=
        bmpRowsBytes_length d h y (by omega) (fun yy x' hyy hx' => hok_rows yy x' hyy hx')
          (fun yy x' bs hbs => hlen_px2 yy x' bs hbs)
      have hAblen : (bmpRowsBytes d h y ++ rowOut d h y x).length = (y * h.width + x) * 3 := by
        rw [List.length_append, hArows, rowOut_length d h y x (fun i hi => hok_row i (by omega)) hlen_px]
        simp only [bmpRowSize, bmpPixelSize, hbc, Nat.add_mul, ite_true]
        rw [← Nat.mul_assoc]
      have h3 : (y * h.width + x) * 3 ≤ (y + 1) * h.width * 3 :=
        Nat.mul_le_mul_right (k := 3) (by rw [Nat.add_mul, Nat.one_mul]; omega)
      have hMemA_ob : (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * 3)).length = obl.length := by
        rw [List.length_append, List.length_drop, hAblen]
        omega
      have hobP : s1.mem ob = some (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * 3)) := by
        rw [hMemS1]; exact smem
      have hbdP : s1.mem bd = some d := by
        rw [hMemS1]; exact hmem2
      have hs_src : h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x < d.length :=
        hsrc x (by omega) hxlt
      have hs_pal : h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4 + 3 ≤ d.length :=
        hpal x (by omega) hxlt
      have hs_idx : byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) < h.paletteEntries :=
        hidx x (by omega) hxlt
      -- ==== call ni_bmp_decode_indexed_pixel ====
      have h0_1 : s1.locals 0 = some (.ptr bd 0) := locals_upd_extract 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) 0 (by decide : ¬ (0 : Nat) = 18) hl0
      have hw0 : EvE Gen.prog s1 (.var 0) (.ptr bd 0) := EvE.var h0_1
      have h3_1 : s1.locals 3 = some (.ptr ob 0) := locals_upd_extract 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) 3 (by decide : ¬ (3 : Nat) = 18) hl3
      have hw3 : EvE Gen.prog s1 (.var 3) (.ptr ob 0) := EvE.var h3_1
      have h15_1 : s1.locals 15 = some (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) := locals_upd_extract 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) 15 (by decide : ¬ (15 : Nat) = 18) hl15
      have hw15 : EvE Gen.prog s1 (.var 15) (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) :=
        EvE.var h15_1
      have h6_1 : s1.locals 6 = some (.int ⟨32, false⟩ x) := locals_upd_extract 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) 6 (by decide : ¬ (6 : Nat) = 18) hl6
      have hw6 : EvE Gen.prog s1 (.cast ⟨64, false⟩ (.var 6)) (.int ⟨64, false⟩ x) :=
        EvE.cast (EvE.var h6_1) (u32_u64_cast x (by omega))
      have h18_1 : s1.locals 18 = some (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) := by
        rw [show s1.locals = s.locals.upd 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) from rfl]
        rw [Locals.upd_same]
      have hw18 : EvE Gen.prog s1 (.var 18) (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) :=
        EvE.var h18_1
      have h12_1 : s1.locals 12 = some (.int ⟨64, false⟩ h.paletteOffset) := locals_upd_extract 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) 12 (by decide : ¬ (12 : Nat) = 18) hl12
      have hw12 : EvE Gen.prog s1 (.var 12) (.int ⟨64, false⟩ h.paletteOffset) :=
        EvE.var h12_1
      have h13_1 : s1.locals 13 = some (.int ⟨64, false⟩ h.paletteEntries) := locals_upd_extract 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) 13 (by decide : ¬ (13 : Nat) = 18) hl13
      have hw13 : EvE Gen.prog s1 (.var 13) (.int ⟨64, false⟩ h.paletteEntries) :=
        EvE.var h13_1
      have hCallArgs : EvArgs Gen.prog s1 [.var 0, .var 3, .var 15, .cast ⟨64, false⟩ (.var 6), .var 18, .var 12, .var 13]
          [.ptr bd 0, .ptr ob 0, .int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride), .int ⟨64, false⟩ x, .int ⟨64, false⟩ (y * h.width * 3 + x * 3), .int ⟨64, false⟩ h.paletteOffset, .int ⟨64, false⟩ h.paletteEntries] :=
        EvArgs.cons hw0 (EvArgs.cons hw3 (EvArgs.cons hw15 (EvArgs.cons hw6 (EvArgs.cons hw18 (EvArgs.cons hw12
          (EvArgs.cons hw13 EvArgs.nil))))))
      obtain ⟨sP, exP, hMemP, hMemPbd, hMemP2⟩ :=
        ni_bmp_decode_indexed_pixel_ok_exs s1.mem d
          (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * 3))
          bd ob hbdP hd hobP
          (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)
          x (y * h.width * 3 + x * 3) h.paletteOffset h.paletteEntries
          hd0 ho2 hs_src hs_pal
          (by
            have e : y * h.width * 3 + x * 3 ≤ y * h.width * 3 + h.width * 3 := by
              have hxle : x * 3 ≤ h.width * 3 := by omega
              omega
            have e2 : (y + 1) * h.width * 3 = y * h.width * 3 + h.width * 3 := by
              simp only [Nat.add_mul, Nat.one_mul]
            rw [hMemA_ob]
            have e3 : y * h.width * 3 + x * 3 ≤ (y + 1) * h.width * 3 := by
              rw [e2]
              exact e
            omega)
          hs_idx
          (by rw [hMemA_ob]; exact hlen)
          s.ro
          hros
      have hCall : ExS Gen.prog s1
          (.call (some 17) 19 [(.var 0), (.var 3), (.var 15), (.cast ⟨64, false⟩ (.var 6)), (.var 18), (.var 12), (.var 13)]) .normal
          { s1 with locals := s1.locals.upd 17 (.int ⟨32, true⟩ 0), mem := sP.mem, ro := s1.ro } :=
        ExS.call_dst hCallArgs
          (show Gen.prog 19 = some Gen.ni_bmp_decode_indexed_pixel from rfl)
          (show Gen.ni_bmp_decode_indexed_pixel.params.length = 7 from rfl)
          exP
      let s2 : State := { s1 with locals := s1.locals.upd 17 (.int ⟨32, true⟩ 0), mem := sP.mem, ro := s1.ro }
      -- the code-0 branch skips
      have h17ne : EvE Gen.prog s2 (.bin .ne (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0))) (boolVal false) := by
        have hl17 : s2.locals 17 = some (.int ⟨32, true⟩ 0) := rfl
        have e : EvE Gen.prog s2 (.bin .ne (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0)))
            (boolVal (decide (IntTy.toInt ⟨32, true⟩ 0 ≠ IntTy.toInt ⟨32, true⟩ 0))) :=
          EvE.bin (EvE.var hl17) (EvE.const _) (bin_i32_ne _ _)
        rw [show (decide (IntTy.toInt ⟨32, true⟩ 0 ≠ IntTy.toInt ⟨32, true⟩ 0)) = false from by decide] at e
        exact e
      have hSkip : ExS Gen.prog s2
          (.ite (.bin .ne (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0))) (.ret (some (.var 17))) .skip)
          .normal s2 :=
        ExS.ite h17ne truthy_false ExS.skip
      -- step: x := x + 1
      have hl6_2 : s2.locals 6 = some (.int ⟨32, false⟩ x) := by rw [show s2.locals 6 = s1.locals 6 from rfl]; exact hl6
      have hCastX2 : evalCast ⟨32, false⟩ (.int ⟨32, false⟩ x) = .ok (.int ⟨32, false⟩ x) := u32_u32_cast x (by omega)
      have hAdd2 : EvE Gen.prog s2 (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 1))) (.int ⟨32, false⟩ (x + 1)) :=
        EvE.bin (EvE.cast (EvE.var hl6_2) hCastX2) (EvE.const _) (bin_u32_add x 1 (by omega))
      have hCastX3 : evalCast ⟨32, false⟩ (.int ⟨32, false⟩ (x + 1)) = .ok (.int ⟨32, false⟩ (x + 1)) := u32_u32_cast (x + 1) (by omega)
      have hSet6 : ExS Gen.prog s2
          (.set 6 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 1)))))
          .normal { s2 with locals := s2.locals.upd 6 (.int ⟨32, false⟩ (x + 1)) } :=
        ExS.set (EvE.cast hAdd2 hCastX3)
      let s3 : State := { s2 with locals := s2.locals.upd 6 (.int ⟨32, false⟩ (x + 1)) }
      -- ==== the block the callee wrote, normalized for the outer invariant ====
      have hAlen2 : (bmpRowsBytes d h y ++ rowOut d h y x).length = y * h.width * 3 + x * 3 := by
        rw [hAblen, Nat.add_mul]
      have htakeA : List.take (y * h.width * 3 + x * 3) (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * 3))
          = bmpRowsBytes d h y ++ rowOut d h y x := by
        rw [show y * h.width * 3 + x * 3 = (bmpRowsBytes d h y ++ rowOut d h y x).length from hAlen2.symm]
        exact List.take_append_length
      have hdropA : List.drop (y * h.width * 3 + x * 3 + 3) (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * 3))
          = obl.drop ((y * h.width + (x + 1)) * 3) := by
        rw [show y * h.width * 3 + x * 3 + 3 = (bmpRowsBytes d h y ++ rowOut d h y x).length + 3 from by rw [hAlen2]]
        rw [drop_append_length (bmpRowsBytes d h y ++ rowOut d h y x) (obl.drop ((y * h.width + x) * 3)) 3]
        rw [List.drop_drop]
        rw [show (y * h.width + (x + 1)) * 3 = (y * h.width + x) * 3 + 3 from by
          rw [show y * h.width + (x + 1) = y * h.width + x + 1 from by omega]
          exact Nat.succ_mul _ _]
      have hEnc3 : encodeLE 1 (byteAt d (h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4 + 2))
          ++ encodeLE 1 (byteAt d (h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4 + 1))
          ++ encodeLE 1 (byteAt d (h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4 + 0))
          = [d.getD (h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4 + 2) 0,
             d.getD (h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4 + 1) 0,
             d.getD (h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4 + 0) 0] := by
        simp [encodeLE_one_byteAt, List.append_assoc]
      have hRowOut : rowOut d h y (x + 1)
          = rowOut d h y x ++ [d.getD (h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4 + 2) 0,
                               d.getD (h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4 + 1) 0,
                               d.getD (h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + x) * 4 + 0) 0] := by
        unfold rowOut
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
        rw [bmpPixel_palette d h y x hbc hs_idx]
        rfl
      have hMemP' : sP.mem ob = some (bmpRowsBytes d h y ++ rowOut d h y (x + 1) ++ obl.drop ((y * h.width + (x + 1)) * 3)) := by
        rw [hMemP, htakeA, hdropA, hRowOut]
        simp [encodeLE_one_byteAt, List.append_assoc, List.singleton_append, List.cons_append, List.append_nil]
      have hMem3 : s3.mem ob = some (bmpRowsBytes d h y ++ rowOut d h y (x + 1) ++ obl.drop ((y * h.width + (x + 1)) * 3)) := by
        show (s2.mem ob) = some _
        rw [show s2.mem = sP.mem from rfl]
        exact hMemP'
      have hMem3bd : s3.mem bd = some d := by
        show (s2.mem bd) = some d
        rw [show s2.mem = sP.mem from rfl]
        exact hMemPbd
      have hMem2_2 : s2.mem 3 = some info := by
        show (sP.mem 3) = some info
        rw [hMemP2]
        show (s1.mem 3) = some info
        rw [show s1.mem = s.mem from rfl]
        exact smem2
      have hMem3_2 : s3.mem 3 = some info := by
        show (s2.mem 3) = some info
        exact hMem2_2
      have h0a : s1.locals 0 = some (.ptr bd 0) := locals_upd_extract 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) 0 (by decide : ¬ (0 : Nat) = 18) hl0
      have h0b : s2.locals 0 = some (.ptr bd 0) := locals_upd_extract 17 (.int ⟨32, true⟩ 0) 0 (by decide : ¬ (0 : Nat) = 17) h0a
      have hl0_3 : s3.locals 0 = some (.ptr bd 0) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 0 (by decide : ¬ (0 : Nat) = 6) h0b
      have h2a : s1.locals 2 = some (.ptr 3 0) := locals_upd_extract 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) 2 (by decide : ¬ (2 : Nat) = 18) hl2
      have h2b : s2.locals 2 = some (.ptr 3 0) := locals_upd_extract 17 (.int ⟨32, true⟩ 0) 2 (by decide : ¬ (2 : Nat) = 17) h2a
      have hl2_3 : s3.locals 2 = some (.ptr 3 0) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 2 (by decide : ¬ (2 : Nat) = 6) h2b
      have h3a : s1.locals 3 = some (.ptr ob 0) := locals_upd_extract 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) 3 (by decide : ¬ (3 : Nat) = 18) hl3
      have h3b : s2.locals 3 = some (.ptr ob 0) := locals_upd_extract 17 (.int ⟨32, true⟩ 0) 3 (by decide : ¬ (3 : Nat) = 17) h3a
      have hl3_3 : s3.locals 3 = some (.ptr ob 0) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 3 (by decide : ¬ (3 : Nat) = 6) h3b
      have h12a : s1.locals 12 = some (.int ⟨64, false⟩ h.paletteOffset) := locals_upd_extract 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) 12 (by decide : ¬ (12 : Nat) = 18) hl12
      have h12b : s2.locals 12 = some (.int ⟨64, false⟩ h.paletteOffset) := locals_upd_extract 17 (.int ⟨32, true⟩ 0) 12 (by decide : ¬ (12 : Nat) = 17) h12a
      have hl12_3 : s3.locals 12 = some (.int ⟨64, false⟩ h.paletteOffset) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 12 (by decide : ¬ (12 : Nat) = 6) h12b
      have h13a : s1.locals 13 = some (.int ⟨64, false⟩ h.paletteEntries) := locals_upd_extract 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) 13 (by decide : ¬ (13 : Nat) = 18) hl13
      have h13b : s2.locals 13 = some (.int ⟨64, false⟩ h.paletteEntries) := locals_upd_extract 17 (.int ⟨32, true⟩ 0) 13 (by decide : ¬ (13 : Nat) = 17) h13a
      have hl13_3 : s3.locals 13 = some (.int ⟨64, false⟩ h.paletteEntries) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 13 (by decide : ¬ (13 : Nat) = 6) h13b
      have h15a : s1.locals 15 = some (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) := locals_upd_extract 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) 15 (by decide : ¬ (15 : Nat) = 18) hl15
      have h15b : s2.locals 15 = some (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) := locals_upd_extract 17 (.int ⟨32, true⟩ 0) 15 (by decide : ¬ (15 : Nat) = 17) h15a
      have hl15_3 : s3.locals 15 = some (.int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride)) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 15 (by decide : ¬ (15 : Nat) = 6) h15b
      have h16a : s1.locals 16 = some (.int ⟨64, false⟩ (y * h.width * 3)) := locals_upd_extract 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) 16 (by decide : ¬ (16 : Nat) = 18) hl16
      have h16b : s2.locals 16 = some (.int ⟨64, false⟩ (y * h.width * 3)) := locals_upd_extract 17 (.int ⟨32, true⟩ 0) 16 (by decide : ¬ (16 : Nat) = 17) h16a
      have hl16_3 : s3.locals 16 = some (.int ⟨64, false⟩ (y * h.width * 3)) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 16 (by decide : ¬ (16 : Nat) = 6) h16b
      have hl6_3 : s3.locals 6 = some (.int ⟨32, false⟩ (x + 1)) := by
        rw [show s3.locals = s2.locals.upd 6 (.int ⟨32, false⟩ (x + 1)) from rfl]
        rw [Locals.upd_same]
      have h5_1 : s1.locals 5 = some (.int ⟨32, false⟩ y) := locals_upd_extract 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) 5 (by decide : ¬ (5 : Nat) = 18) hl5
      have h5_2 : s2.locals 5 = some (.int ⟨32, false⟩ y) := locals_upd_extract 17 (.int ⟨32, true⟩ 0) 5 (by decide : ¬ (5 : Nat) = 17) h5_1
      have h5_3 : s3.locals 5 = some (.int ⟨32, false⟩ y) := locals_upd_extract 6 (.int ⟨32, false⟩ (x + 1)) 5 (by decide : ¬ (5 : Nat) = 6) h5_2
      -- ==== step: y := y + 1 ====
      obtain ⟨s', hLoop', hMem', hLoc', hPres', hMem'bd, hMem'2, hRO'⟩ := ih (x + 1) s3
        (fun i h1 h2 => hsrc i (by omega) h2) (fun i h1 h2 => hpal i (by omega) h2) (fun i h1 h2 => hidx i (by omega) h2)
        (by omega) (by omega)
        hl0_3 hl2_3 hl3_3 h5_3 hl6_3 hl12_3 hl13_3 hl15_3 hl16_3
        (by rw [show s3.ro = s.ro from rfl]; exact hros)
        hMem3 hMem3bd hMem3_2
      have hPres : ∀ j, j ≠ 6 → j ≠ 17 → j ≠ 18 → s'.locals j = s.locals j := by
        intro j h6 h17 h18
        have e3 : s1.locals j = s.locals j := by
          rw [show s1.locals = s.locals.upd 18 (.int ⟨64, false⟩ (y * h.width * 3 + x * 3)) from rfl]
          rw [Locals.upd_ne _ _ h18]
        have e2 : s2.locals j = s1.locals j := by
          rw [show s2.locals = s1.locals.upd 17 (.int ⟨32, true⟩ 0) from rfl]
          rw [Locals.upd_ne _ _ h17]
        have e1 : s3.locals j = s2.locals j := by
          rw [show s3.locals = s2.locals.upd 6 (.int ⟨32, false⟩ (x + 1)) from rfl]
          rw [Locals.upd_ne _ _ h6]
        rw [hPres' j h6 h17 h18, e1, e2, e3]
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
      show ExS Gen.prog s Gen.ni_bmp_decode_into_loop0 .normal s'
      have hBody : ExS Gen.prog s
          (.ite (.bin .lt (some ⟨32, false⟩) (.var 6) (.load (.int ⟨32, false⟩) (.field (.var 2) 24)))
            (.seq (.set 18 (.bin .add (some ⟨64, false⟩) (.var 16) (.bin .mul (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 6)) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3))))))
              (.seq (.call (some 17) 19 [(.var 0), (.var 3), (.var 15), (.cast ⟨64, false⟩ (.var 6)), (.var 18), (.var 12), (.var 13)])
                (.ite (.bin .ne (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0))) (.ret (some (.var 17))) .skip)))
            .brk)
          .normal s2 :=
        ExS.ite hCond truthy_true (ExS.seq hSet18 (ExS.seq hCall hSkip))
      show ExS Gen.prog s Gen.ni_bmp_decode_into_loop0 .normal s'
      exact ExS.loop_next hBody (Or.inl rfl) hSet6 hLoop' 
/-- The inner 8-bit (palette) row loop of `ni_bmp_decode_into`, all-pixels-OK
    case: runs to `.brk` at `width`, leaving the first `y + 1` output rows in
    `out`. Locals: 0=bytes, 1=size, 2=info, 3=out, 4=out_cap, 5=y, 6=x,
    7=width, 8=height, 9=channels, 10=row_stride, 11=pixel_offset,
    12=palette_offset, 13=palette_entries, 14=src_y, 15=src_base,
    16=dst_base, 17=code, 18=dst -/
theorem ni_bmp_decode_into_loop0_ok_exs (m : Mem) (d obl : List UInt8)
    (bd ob : Nat) (hm : m bd = some d) (hd : d.length < 2 ^ 64)
    (hob : m ob = some obl) (hd0 : bd ≠ ob) (ho2 : 3 ≠ ob) (bd2 : 3 ≠ bd)
    (info : List UInt8) (hinfo : m 3 = some info) (h48 : info.length = 48)
    (h : BmpInfo) (hbc : h.bitCount = 8)
    (hw : (info.drop 24).take 4 = encodeLE 4 h.width) (hwv : h.width < 4294967296)
    (y x : Nat) (hx : x ≤ h.width)
    (hout : (y + 1) * h.width * 3 ≤ obl.length)
    (hlen : obl.length < 2 ^ 64)
    (hsrc : ∀ i, x ≤ i → i < h.width → h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + i < d.length)
    (hpal : ∀ i, x ≤ i → i < h.width → h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + i) * 4 + 3 ≤ d.length)
    (hidx : ∀ i, x ≤ i → i < h.width → byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + i) < h.paletteEntries)
    (hy : y < h.height)
    (hbok : ∀ yy i, yy < y → i < h.width → ∃ bs, bmpPixel d h yy i = .ok bs)
    (hok_row : ∀ i, i < h.width → ∃ bs, bmpPixel d h y i = .ok bs)
    (hmem : m ob = some (bmpRowsBytes d h y ++ rowOut d h y x ++ obl.drop ((y * h.width + x) * 3)))
    (ro : Bool) (hro : ro = false) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]
        ([.ptr bd 0, .int ⟨64, false⟩ d.length, .ptr 3 0, .ptr ob 0, .int ⟨64, false⟩ obl.length,
          .int ⟨32, false⟩ y, .int ⟨32, false⟩ x,
          .int ⟨64, false⟩ h.width, .int ⟨64, false⟩ h.height, .int ⟨64, false⟩ h.channels,
          .int ⟨64, false⟩ h.rowStride, .int ⟨64, false⟩ h.pixelOffset,
          .int ⟨64, false⟩ h.paletteOffset, .int ⟨64, false⟩ h.paletteEntries,
          .int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y),
          .int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride),
          .int ⟨64, false⟩ (y * h.width * 3),
          .int ⟨32, true⟩ 0,
          .int ⟨64, false⟩ (y * h.width * 3 + x * 3)] : List Val), m, ro⟩
      Gen.ni_bmp_decode_into_loop0
      (.normal) s' ∧
    s'.mem ob = some
      (bmpRowsBytes d h (y + 1) ++ obl.drop ((y + 1) * (h.width * 3))) := by
  have hiter := loop0_iter m d obl bd ob hm hd hob hd0 ho2 bd2 info hinfo h48 h hbc hw hwv
    y hout hlen hy hok_row hbok ro hro
    (h.width - x) x
    ⟨frameLocals [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]
      ([.ptr bd 0, .int ⟨64, false⟩ d.length, .ptr 3 0, .ptr ob 0, .int ⟨64, false⟩ obl.length,
        .int ⟨32, false⟩ y, .int ⟨32, false⟩ x,
        .int ⟨64, false⟩ h.width, .int ⟨64, false⟩ h.height, .int ⟨64, false⟩ h.channels,
        .int ⟨64, false⟩ h.rowStride, .int ⟨64, false⟩ h.pixelOffset,
        .int ⟨64, false⟩ h.paletteOffset, .int ⟨64, false⟩ h.paletteEntries,
        .int ⟨64, false⟩ (if h.topDown = 1 then y else h.height - 1 - y),
        .int ⟨64, false⟩ (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride),
        .int ⟨64, false⟩ (y * h.width * 3),
        .int ⟨32, true⟩ 0,
        .int ⟨64, false⟩ (y * h.width * 3 + x * 3)] : List Val), m, ro⟩
    hsrc hpal hidx
    rfl (by omega) (rfl) (rfl) (rfl) (rfl) (rfl) (rfl) (rfl) (rfl) (rfl) hro hmem hm hinfo
  obtain ⟨s5', hLoop5', hMem5', hLoc5', hPres5', hMem5'bd, hMem5'2, hRO5'⟩ := hiter
  exact ⟨s5', hLoop5', hMem5'⟩


/-- u8 literal cast to i32 (small values). -/
theorem u8_i32_cast {v : Nat} (hv : v < 4294967296) :
    evalCast ⟨32, true⟩ (Val.int ⟨8, false⟩ v) = .ok (Val.int ⟨32, true⟩ v) := by
  simp [evalCast, IntTy.modulus, Int.ofNat_lt, hv]

end NANO.C.Proofs
