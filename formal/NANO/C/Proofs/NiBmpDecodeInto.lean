/-
  BMP decode refinement proof — the whole `ni_bmp_decode_into` function,
  composed from the loop wrappers (`ni_bmp_decode_into_loop1_ok_exs` and
  `ni_bmp_decode_into_loop3_ok_exs`) and the mul-fits lemma.
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
import NANO.C.Proofs.NiBmpLoop4
import NANO.C.Proofs.NiBmpLoop5
import NANO.C.Proofs.Bmp

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 800000

namespace NANO.C.Proofs
open NANO NANO.C

/-- The whole BMP decode function, all-pixels-OK case: given a successful
    header (all `h` binds come from it), `ni_bmp_decode_into` returns 0 and
    writes the flattened `bmpPixels` to `out`. -/
theorem ni_bmp_decode_into_ok_exs (m : Mem) (d obl : List UInt8)
    (bd ob : Nat) (hm : m bd = some d) (hd : d.length < 2 ^ 64)
    (hob : m ob = some obl) (hd0 : bd ≠ ob) (ho2 : 3 ≠ ob) (bd2 : 3 ≠ bd)
    (info : List UInt8) (hinfo : m 3 = some info) (h48 : info.length = 48)
    (h : BmpInfo)
    (hrows : (info.drop 0).take 8 = encodeLE 8 h.rowStride) (hrow64 : h.rowStride < 2 ^ 64)
    (howsz : (info.drop 8).take 8 = encodeLE 8 h.outSize)
    (houtsz : h.outSize = h.width * h.channels * h.height)
    (houtsz64 : h.outSize < 2 ^ 64)
    (hpo : (info.drop 16).take 8 = encodeLE 8 h.paletteOffset) (hpal64 : h.paletteOffset < 2 ^ 64)
    (hw : (info.drop 24).take 4 = encodeLE 4 h.width) (hwv : h.width < 4294967296)
    (hht : (info.drop 28).take 4 = encodeLE 4 h.height) (hhtwv : h.height < 4294967296)
    (hpIc : (info.drop 32).take 4 = encodeLE 4 h.pixelOffset) (hpicv : h.pixelOffset < 4294967296)
    (hpentr : (info.drop 36).take 4 = encodeLE 4 h.paletteEntries) (hpentrv : h.paletteEntries < 4294967296)
    (hbc8 : (info.drop 40).take 2 = encodeLE 2 h.bitCount) (hbcv : h.bitCount < 65536)
    (hbcdisc : h.bitCount = 8 ∨ h.bitCount = 24 ∨ h.bitCount = 32)
    (hch : (info.drop 42).take 1 = encodeLE 1 h.channels) (hchc : h.channels = 3 ∨ h.channels = 4)
    (hc32 : h.channels = (if h.bitCount = 32 then 4 else 3))
    (hrsd : h.bitCount ≠ 8 → h.width * h.channels ≤ h.rowStride)
    (htop : (info.drop 43).take 1 = encodeLE 1 h.topDown) (htopd : h.topDown = 0 ∨ h.topDown = 1)
    (hout : h.outSize ≤ obl.length) (hobl64 : obl.length < 2 ^ 64)
    (hpx : h.pixelOffset + h.rowStride * h.height ≤ d.length)
    (hpx64 : h.pixelOffset + h.rowStride * h.height < 2 ^ 64)
    (hpalok : h.paletteOffset + h.paletteEntries * 4 ≤ h.pixelOffset)
    (hpx8 : ∀ y i, y < h.height → i < h.width → h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + i < d.length)
    (hpos8 : ∀ y i, y < h.height → i < h.width → h.paletteOffset + byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + i) * 4 + 3 ≤ d.length)
    (hidx8 : ∀ y i, y < h.height → i < h.width → byteAt d (h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + i) < h.paletteEntries)
    (hok : ∀ y i, y < h.height → i < h.width → ∃ bs, bmpPixel d h y i = .ok bs)
    (hwidth : 1 ≤ h.width)
    (ro : Bool) (hro : ro = false) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals [0, 1, 2, 3, 4]
        ([.ptr bd 0, .int ⟨64, false⟩ d.length, .ptr 3 0, .ptr ob 0, .int ⟨64, false⟩ obl.length] : List Val), m, ro⟩
      Gen.ni_bmp_decode_into.body
      (.ret (some (.int ⟨32, true⟩ 0))) s' ∧
    s'.mem ob = some
      (bmpRowsBytes d h h.height ++ obl.drop (h.height * bmpRowSize h)) := by
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  let s : State :=
    ⟨frameLocals [0, 1, 2, 3, 4]
      ([.ptr bd 0, .int ⟨64, false⟩ d.length, .ptr 3 0, .ptr ob 0, .int ⟨64, false⟩ obl.length] : List Val), m, ro⟩
  have hl0 : s.locals 0 = some (.ptr bd 0) := rfl
  have hl1 : s.locals 1 = some (.int ⟨64, false⟩ d.length) := rfl
  have hl2 : s.locals 2 = some (.ptr 3 0) := rfl
  have hl3 : s.locals 3 = some (.ptr ob 0) := rfl
  have hl4 : s.locals 4 = some (.int ⟨64, false⟩ obl.length) := rfl
  have hros : s.ro = false := hro
  -- === load output_size field (offset 8, u64) and check the output capacity ===
  have hField8 : EvE Gen.prog s (.field (.var 2) 8) (.ptr 3 8) :=
    EvE.field (EvE.var hl2)
      (ptrAddN_ok hinfo (by omega))
  have hLoad8 : EvE Gen.prog s (.load (.int ⟨64, false⟩) (.field (.var 2) 8)) (.int ⟨64, false⟩ h.outSize) :=
    EvE.load hField8 (load_u64_field s.mem 3 info hinfo h48 8 (by omega) h.outSize howsz houtsz64)
  have hCmp8 : EvE Gen.prog s (.bin .lt (some ⟨64, false⟩) (.var 4) (.load (.int ⟨64, false⟩) (.field (.var 2) 8))) (boolVal false) := by
    have hdec : decide (obl.length < h.outSize) = false := decide_eq_false (by omega)
    exact EvE.bin (EvE.var hl4) hLoad8 (by rw [bin_u64_lt, hdec])
  have hSkipCap : ExS Gen.prog s
      (.ite (.bin .lt (some ⟨64, false⟩) (.var 4) (.load (.int ⟨64, false⟩) (.field (.var 2) 8)))
        (.ret (some (.const (.int ⟨32, true⟩ 12)))) .skip)
      .normal s :=
    ExS.ite hCmp8 truthy_false ExS.skip
  -- ==== set 7: width (u32 → u64) ====
  have hField24 : EvE Gen.prog s (.field (.var 2) 24) (.ptr 3 24) :=
    EvE.field (EvE.var hl2)
      (ptrAddN_ok hinfo (by omega))
  have hLoad24 : EvE Gen.prog s (.load (.int ⟨32, false⟩) (.field (.var 2) 24)) (.int ⟨32, false⟩ h.width) :=
    EvE.load hField24 (load_u32_field s.mem 3 info hinfo h48 24 (by omega) h.width hw hwv)
  have hCast7 : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ h.width) = .ok (.int ⟨64, false⟩ h.width) :=
    u32_u64_cast h.width hwv
  have hSet7 : ExS Gen.prog s
      (.set 7 (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩) (.field (.var 2) 24))))
      .normal { s with locals := s.locals.upd 7 (.int ⟨64, false⟩ h.width) } :=
    ExS.set (EvE.cast hLoad24 hCast7)
  let s1 : State := { s with locals := s.locals.upd 7 (.int ⟨64, false⟩ h.width) }
  have hl2_1 : s1.locals 2 = some (.ptr 3 0) :=
    locals_upd_extract 7 (.int ⟨64, false⟩ h.width) 2 (by decide : ¬ (2 : Nat) = 7) hl2
  have hmem_1 : s1.mem = m := rfl
  -- ==== set 8: height (u32 → u64) ====
  have hField28 : EvE Gen.prog s1 (.field (.var 2) 28) (.ptr 3 28) :=
    EvE.field (EvE.var hl2_1)
      (ptrAddN_ok hinfo (by omega))
  have hLoad28 : EvE Gen.prog s1 (.load (.int ⟨32, false⟩) (.field (.var 2) 28)) (.int ⟨32, false⟩ h.height) :=
    EvE.load hField28 (load_u32_field s1.mem 3 info (by rw [show s1.mem = m from rfl]; exact hinfo) h48 28 (by omega) h.height hht hhtwv)
  have hCast8 : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ h.height) = .ok (.int ⟨64, false⟩ h.height) :=
    u32_u64_cast h.height hhtwv
  have hSet8 : ExS Gen.prog s1
      (.set 8 (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩) (.field (.var 2) 28))))
      .normal { s1 with locals := s1.locals.upd 8 (.int ⟨64, false⟩ h.height) } :=
    ExS.set (EvE.cast hLoad28 hCast8)
  let s2 : State := { s1 with locals := s1.locals.upd 8 (.int ⟨64, false⟩ h.height) }
  have hl2_2 : s2.locals 2 = some (.ptr 3 0) :=
    locals_upd_extract 8 (.int ⟨64, false⟩ h.height) 2 (by decide : ¬ (2 : Nat) = 8) hl2_1
  -- ==== set 9: channels (u8 → u64) ====
  have hField42 : EvE Gen.prog s2 (.field (.var 2) 42) (.ptr 3 42) :=
    EvE.field (EvE.var hl2_2)
      (ptrAddN_ok (show s2.mem 3 = some info from by rw [show s2.mem = m from rfl]; exact hinfo) (by omega))
  have hLoad42 : EvE Gen.prog s2 (.load (.int ⟨8, false⟩) (.field (.var 2) 42)) (.int ⟨8, false⟩ h.channels) :=
    EvE.load hField42 (load_u8_field s2.mem 3 info (by rw [show s2.mem = m from rfl]; exact hinfo) h48 42 (by omega) h.channels hch (by
      cases hchc with
      | inl h3 => rw [h3]; omega
      | inr h4 => rw [h4]; omega))
  have hCast9 : evalCast ⟨64, false⟩ (.int ⟨8, false⟩ h.channels) = .ok (.int ⟨64, false⟩ h.channels) := by
    simp [evalCast, IntTy.modulus, IntTy.wrap, Int.ofNat_lt, show h.channels < 18446744073709551616 from by
      cases hchc with
      | inl h3 => rw [h3]; omega
      | inr h4 => rw [h4]; omega]
  have hSet9 : ExS Gen.prog s2
      (.set 9 (.cast ⟨64, false⟩ (.load (.int ⟨8, false⟩) (.field (.var 2) 42))))
      .normal { s2 with locals := s2.locals.upd 9 (.int ⟨64, false⟩ h.channels) } :=
    ExS.set (EvE.cast hLoad42 hCast9)
  let s3 : State := { s2 with locals := s2.locals.upd 9 (.int ⟨64, false⟩ h.channels) }
  have hl2_3 : s3.locals 2 = some (.ptr 3 0) :=
    locals_upd_extract 9 (.int ⟨64, false⟩ h.channels) 2 (by decide : ¬ (2 : Nat) = 9) hl2_2
  -- ==== set 10: row_stride (u64) ====
  have hField0 : EvE Gen.prog s3 (.field (.var 2) 0) (.ptr 3 0) :=
    EvE.field (EvE.var hl2_3)
      (ptrAddN_ok (show s3.mem 3 = some info from by rw [show s3.mem = m from rfl]; exact hinfo) (by omega))
  have hLoad0 : EvE Gen.prog s3 (.load (.int ⟨64, false⟩) (.field (.var 2) 0)) (.int ⟨64, false⟩ h.rowStride) :=
    EvE.load hField0 (load_u64_field s3.mem 3 info (by rw [show s3.mem = m from rfl]; exact hinfo) h48 0 (by omega) h.rowStride hrows hrow64)
  have hSet10 : ExS Gen.prog s3
      (.set 10 (.load (.int ⟨64, false⟩) (.field (.var 2) 0)))
      .normal { s3 with locals := s3.locals.upd 10 (.int ⟨64, false⟩ h.rowStride) } :=
    ExS.set hLoad0
  let s4 : State := { s3 with locals := s3.locals.upd 10 (.int ⟨64, false⟩ h.rowStride) }
  have hl2_4 : s4.locals 2 = some (.ptr 3 0) :=
    locals_upd_extract 10 (.int ⟨64, false⟩ h.rowStride) 2 (by decide : ¬ (2 : Nat) = 10) hl2_3
  -- ==== set 11: pixel_offset (u32 → u64) ====
  have hField32 : EvE Gen.prog s4 (.field (.var 2) 32) (.ptr 3 32) :=
    EvE.field (EvE.var hl2_4)
      (ptrAddN_ok (show s4.mem 3 = some info from by rw [show s4.mem = m from rfl]; exact hinfo) (by omega))
  have hLoad32 : EvE Gen.prog s4 (.load (.int ⟨32, false⟩) (.field (.var 2) 32)) (.int ⟨32, false⟩ h.pixelOffset) :=
    EvE.load hField32 (load_u32_field s4.mem 3 info (by rw [show s4.mem = m from rfl]; exact hinfo) h48 32 (by omega) h.pixelOffset hpIc hpicv)
  have hCast11 : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ h.pixelOffset) = .ok (.int ⟨64, false⟩ h.pixelOffset) :=
    u32_u64_cast h.pixelOffset hpicv
  have hSet11 : ExS Gen.prog s4
      (.set 11 (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩) (.field (.var 2) 32))))
      .normal { s4 with locals := s4.locals.upd 11 (.int ⟨64, false⟩ h.pixelOffset) } :=
    ExS.set (EvE.cast hLoad32 hCast11)
  let s5 : State := { s4 with locals := s4.locals.upd 11 (.int ⟨64, false⟩ h.pixelOffset) }
  have hl2_5 : s5.locals 2 = some (.ptr 3 0) :=
    locals_upd_extract 11 (.int ⟨64, false⟩ h.pixelOffset) 2 (by decide : ¬ (2 : Nat) = 11) hl2_4
  -- ==== set 12: palette_offset (u64) ====
  have hField16 : EvE Gen.prog s5 (.field (.var 2) 16) (.ptr 3 16) :=
    EvE.field (EvE.var hl2_5)
      (ptrAddN_ok (show s5.mem 3 = some info from by rw [show s5.mem = m from rfl]; exact hinfo) (by omega))
  have hLoad16 : EvE Gen.prog s5 (.load (.int ⟨64, false⟩) (.field (.var 2) 16)) (.int ⟨64, false⟩ h.paletteOffset) :=
    EvE.load hField16 (load_u64_field s5.mem 3 info (by rw [show s5.mem = m from rfl]; exact hinfo) h48 16 (by omega) h.paletteOffset hpo hpal64)
  have hSet12 : ExS Gen.prog s5
      (.set 12 (.load (.int ⟨64, false⟩) (.field (.var 2) 16)))
      .normal { s5 with locals := s5.locals.upd 12 (.int ⟨64, false⟩ h.paletteOffset) } :=
    ExS.set hLoad16
  let s6 : State := { s5 with locals := s5.locals.upd 12 (.int ⟨64, false⟩ h.paletteOffset) }
  have hl2_6 : s6.locals 2 = some (.ptr 3 0) :=
    locals_upd_extract 12 (.int ⟨64, false⟩ h.paletteOffset) 2 (by decide : ¬ (2 : Nat) = 12) hl2_5
  -- ==== set 13: palette_entries (u32 → u64) ====
  have hField36 : EvE Gen.prog s6 (.field (.var 2) 36) (.ptr 3 36) :=
    EvE.field (EvE.var hl2_6)
      (ptrAddN_ok (show s6.mem 3 = some info from by rw [show s6.mem = m from rfl]; exact hinfo) (by omega))
  have hLoad36 : EvE Gen.prog s6 (.load (.int ⟨32, false⟩) (.field (.var 2) 36)) (.int ⟨32, false⟩ h.paletteEntries) :=
    EvE.load hField36 (load_u32_field s6.mem 3 info (by rw [show s6.mem = m from rfl]; exact hinfo) h48 36 (by omega) h.paletteEntries hpentr hpentrv)
  have hCast13 : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ h.paletteEntries) = .ok (.int ⟨64, false⟩ h.paletteEntries) :=
    u32_u64_cast h.paletteEntries hpentrv
  have hSet13 : ExS Gen.prog s6
      (.set 13 (.cast ⟨64, false⟩ (.load (.int ⟨32, false⟩) (.field (.var 2) 36))))
      .normal { s6 with locals := s6.locals.upd 13 (.int ⟨64, false⟩ h.paletteEntries) } :=
    ExS.set (EvE.cast hLoad36 hCast13)
  let s7 : State := { s6 with locals := s6.locals.upd 13 (.int ⟨64, false⟩ h.paletteEntries) }
  have hl2_7 : s7.locals 2 = some (.ptr 3 0) :=
    locals_upd_extract 13 (.int ⟨64, false⟩ h.paletteEntries) 2 (by decide : ¬ (2 : Nat) = 13) hl2_6
  -- ==== fits check the rowStride * height pair, then skip the trunc branch ====
  have h7_7 : s7.locals 7 = some (.int ⟨64, false⟩ h.width) := by
    rw [show s7.locals = s6.locals.upd 13 (.int ⟨64, false⟩ h.paletteEntries) from rfl,
        show s6.locals = s5.locals.upd 12 (.int ⟨64, false⟩ h.paletteOffset) from rfl,
        show s5.locals = s4.locals.upd 11 (.int ⟨64, false⟩ h.pixelOffset) from rfl,
        show s4.locals = s3.locals.upd 10 (.int ⟨64, false⟩ h.rowStride) from rfl,
        show s3.locals = s2.locals.upd 9 (.int ⟨64, false⟩ h.channels) from rfl,
        show s2.locals = s1.locals.upd 8 (.int ⟨64, false⟩ h.height) from rfl,
        show s1.locals = s.locals.upd 7 (.int ⟨64, false⟩ h.width) from rfl]
    rw [Locals.upd_ne _ _ (by decide : ¬ (7 : Nat) = 13), Locals.upd_ne _ _ (by decide : ¬ (7 : Nat) = 12), Locals.upd_ne _ _ (by decide : ¬ (7 : Nat) = 11), Locals.upd_ne _ _ (by decide : ¬ (7 : Nat) = 10), Locals.upd_ne _ _ (by decide : ¬ (7 : Nat) = 9), Locals.upd_ne _ _ (by decide : ¬ (7 : Nat) = 8), Locals.upd_same]
  have h8_7 : s7.locals 8 = some (.int ⟨64, false⟩ h.height) := by
    rw [show s7.locals = s6.locals.upd 13 (.int ⟨64, false⟩ h.paletteEntries) from rfl,
        show s6.locals = s5.locals.upd 12 (.int ⟨64, false⟩ h.paletteOffset) from rfl,
        show s5.locals = s4.locals.upd 11 (.int ⟨64, false⟩ h.pixelOffset) from rfl,
        show s4.locals = s3.locals.upd 10 (.int ⟨64, false⟩ h.rowStride) from rfl,
        show s3.locals = s2.locals.upd 9 (.int ⟨64, false⟩ h.channels) from rfl,
        show s2.locals = s1.locals.upd 8 (.int ⟨64, false⟩ h.height) from rfl]
    rw [Locals.upd_ne _ _ (by decide : ¬ (8 : Nat) = 13), Locals.upd_ne _ _ (by decide : ¬ (8 : Nat) = 12), Locals.upd_ne _ _ (by decide : ¬ (8 : Nat) = 11), Locals.upd_ne _ _ (by decide : ¬ (8 : Nat) = 10), Locals.upd_ne _ _ (by decide : ¬ (8 : Nat) = 9), Locals.upd_same]
  have h9_7 : s7.locals 9 = some (.int ⟨64, false⟩ h.channels) := by
    rw [show s7.locals = s6.locals.upd 13 (.int ⟨64, false⟩ h.paletteEntries) from rfl,
        show s6.locals = s5.locals.upd 12 (.int ⟨64, false⟩ h.paletteOffset) from rfl,
        show s5.locals = s4.locals.upd 11 (.int ⟨64, false⟩ h.pixelOffset) from rfl,
        show s4.locals = s3.locals.upd 10 (.int ⟨64, false⟩ h.rowStride) from rfl,
        show s3.locals = s2.locals.upd 9 (.int ⟨64, false⟩ h.channels) from rfl]
    rw [Locals.upd_ne _ _ (by decide : ¬ (9 : Nat) = 13), Locals.upd_ne _ _ (by decide : ¬ (9 : Nat) = 12), Locals.upd_ne _ _ (by decide : ¬ (9 : Nat) = 11), Locals.upd_ne _ _ (by decide : ¬ (9 : Nat) = 10), Locals.upd_same]
  have h10_7 : s7.locals 10 = some (.int ⟨64, false⟩ h.rowStride) := by
    rw [show s7.locals = s6.locals.upd 13 (.int ⟨64, false⟩ h.paletteEntries) from rfl,
        show s6.locals = s5.locals.upd 12 (.int ⟨64, false⟩ h.paletteOffset) from rfl,
        show s5.locals = s4.locals.upd 11 (.int ⟨64, false⟩ h.pixelOffset) from rfl,
        show s4.locals = s3.locals.upd 10 (.int ⟨64, false⟩ h.rowStride) from rfl]
    rw [Locals.upd_ne _ _ (by decide : ¬ (10 : Nat) = 13), Locals.upd_ne _ _ (by decide : ¬ (10 : Nat) = 12), Locals.upd_ne _ _ (by decide : ¬ (10 : Nat) = 11), Locals.upd_same]
  have hFits : h.rowStride = 0 ∨ h.height ≤ 18446744073709551615 / h.rowStride := by
    by_cases h0 : h.rowStride = 0
    · exact Or.inl h0
    · exact Or.inr (by
        rw [Nat.le_div_iff_mul_le (by omega)]
        calc h.height * h.rowStride = h.rowStride * h.height := by rw [Nat.mul_comm]
          _ ≤ h.pixelOffset + h.rowStride * h.height := Nat.le_add_left _ _
          _ ≤ 18446744073709551615 := by omega)
  obtain ⟨sMF, exMF⟩ := ni_bmp_mul_fits_exs s7.mem h.rowStride h.height hrow64 (by omega) true
  have exCall : EvE Gen.prog s7
      (.call 11 [(.var 10), (.var 8)])
      (.int ⟨32, true⟩ (if h.rowStride = 0 ∨ h.height ≤ 18446744073709551615 / h.rowStride then 1 else 0)) :=
    EvE.call (EvArgs.cons (EvE.var h10_7) (EvArgs.cons (EvE.var h8_7) EvArgs.nil))
      (show Gen.prog 11 = some Gen.ni_bmp_mul_fits from rfl)
      (show Gen.ni_bmp_mul_fits.params.length = 2 from rfl)
      exMF
  rw [if_pos hFits] at exCall
  have he : evalUn .lnot ⟨32, true⟩ (.int ⟨32, true⟩ 1) = .ok (boolVal false) := by
    simp [evalUn, truthy]
  have hfalse : EvE Gen.prog s7
      (.un .lnot ⟨32, true⟩ (.call 11 [(.var 10), (.var 8)]))
      (boolVal false) :=
    EvE.un exCall he
  have hTruncSkip : ExS Gen.prog s7
      (.ite (.un .lnot ⟨32, true⟩ (.call 11 [(.var 10), (.var 8)]))
        (.ret (some (.const (.int ⟨32, true⟩ 9)))) .skip)
      .normal s7 :=
    ExS.ite hfalse truthy_false ExS.skip
  -- ==== trunc check (pixelOffset + rowStride*height <= size) ====
  have h1_7 : s7.locals 1 = some (.int ⟨64, false⟩ d.length) := locals_upd_extract 13 (.int ⟨64, false⟩ h.paletteEntries) 1 (by decide : ¬ (1 : Nat) = 13)
    (locals_upd_extract 12 (.int ⟨64, false⟩ h.paletteOffset) 1 (by decide : ¬ (1 : Nat) = 12)
      (locals_upd_extract 11 (.int ⟨64, false⟩ h.pixelOffset) 1 (by decide : ¬ (1 : Nat) = 11)
        (locals_upd_extract 10 (.int ⟨64, false⟩ h.rowStride) 1 (by decide : ¬ (1 : Nat) = 10)
          (locals_upd_extract 9 (.int ⟨64, false⟩ h.channels) 1 (by decide : ¬ (1 : Nat) = 9)
            (locals_upd_extract 8 (.int ⟨64, false⟩ h.height) 1 (by decide : ¬ (1 : Nat) = 8)
              (locals_upd_extract 7 (.int ⟨64, false⟩ h.width) 1 (by decide : ¬ (1 : Nat) = 7) rfl))))))
  have h11_7 : s7.locals 11 = some (.int ⟨64, false⟩ h.pixelOffset) := by
    rw [show s7.locals = s6.locals.upd 13 (.int ⟨64, false⟩ h.paletteEntries) from rfl,
        show s6.locals = s5.locals.upd 12 (.int ⟨64, false⟩ h.paletteOffset) from rfl,
        show s5.locals = s4.locals.upd 11 (.int ⟨64, false⟩ h.pixelOffset) from rfl]
    rw [Locals.upd_ne _ _ (by decide : ¬ (11 : Nat) = 13), Locals.upd_ne _ _ (by decide : ¬ (11 : Nat) = 12), Locals.upd_same]
  have hMulRS : EvE Gen.prog s7 (.bin .mul (some ⟨64, false⟩) (.var 10) (.var 8)) (.int ⟨64, false⟩ (h.rowStride * h.height)) :=
    EvE.bin (EvE.var h10_7) (EvE.var h8_7) (bin_u64_mul h.rowStride h.height (by omega))
  have hSubLen : EvE Gen.prog s7 (.bin .sub (some ⟨64, false⟩) (.var 1) (.var 11)) (.int ⟨64, false⟩ (d.length - h.pixelOffset)) :=
    EvE.bin (EvE.var h1_7) (EvE.var h11_7) (bin_u64_sub d.length h.pixelOffset (by omega))
  have hGt1 : EvE Gen.prog s7 (.bin .gt (some ⟨64, false⟩) (.var 11) (.var 1)) (boolVal false) := by
    have hdec : decide (h.pixelOffset > d.length) = false := decide_eq_false (by omega)
    exact EvE.bin (EvE.var h11_7) (EvE.var h1_7) (by rw [bin_u64_gt, hdec])
  have hGt2 : EvE Gen.prog s7 (.bin .gt (some ⟨64, false⟩) (.bin .mul (some ⟨64, false⟩) (.var 10) (.var 8)) (.bin .sub (some ⟨64, false⟩) (.var 1) (.var 11))) (boolVal false) := by
    have hdec : decide (h.rowStride * h.height > d.length - h.pixelOffset) = false := decide_eq_false (by omega)
    exact EvE.bin hMulRS hSubLen (by rw [bin_u64_gt, hdec])
  have hTruncOr : EvE Gen.prog s7 (.lor (.bin .gt (some ⟨64, false⟩) (.var 11) (.var 1)) (.bin .gt (some ⟨64, false⟩) (.bin .mul (some ⟨64, false⟩) (.var 10) (.var 8)) (.bin .sub (some ⟨64, false⟩) (.var 1) (.var 11)))) (boolVal false) :=
    EvE.lor_false hGt1 truthy_false hGt2 truthy_false
  have hTruncSkip2 : ExS Gen.prog s7
      (.ite (.lor (.bin .gt (some ⟨64, false⟩) (.var 11) (.var 1))
        (.bin .gt (some ⟨64, false⟩) (.bin .mul (some ⟨64, false⟩) (.var 10) (.var 8)) (.bin .sub (some ⟨64, false⟩) (.var 1) (.var 11))))
        (.ret (some (.const (.int ⟨32, true⟩ 9)))) .skip)
      .normal s7 :=
    ExS.ite hTruncOr truthy_false ExS.skip
  -- ==== the bit_count == 8 branch: palette sloppiness gate ====
  have hField40 : EvE Gen.prog s7 (.field (.var 2) 40) (.ptr 3 40) :=
    EvE.field (EvE.var hl2_7)
      (ptrAddN_ok (show s7.mem 3 = some info from by rw [show s7.mem = m from rfl]; exact hinfo) (by omega))
  have hLoad40 : EvE Gen.prog s7 (.load (.int ⟨16, false⟩) (.field (.var 2) 40)) (.int ⟨16, false⟩ h.bitCount) :=
    EvE.load hField40 (load_u16_field s7.mem 3 info (by rw [show s7.mem = m from rfl]; exact hinfo) h48 40 (by omega) h.bitCount hbc8 hbcv)
  have hCast40 : evalCast ⟨32, false⟩ (.int ⟨16, false⟩ h.bitCount) = .ok (.int ⟨32, false⟩ h.bitCount) := by
    simp [evalCast, IntTy.modulus, IntTy.wrap, Int.ofNat_lt, show h.bitCount < 4294967296 from by omega]
  have hHcast40 : EvE Gen.prog s7 (.cast ⟨32, false⟩ (.load (.int ⟨16, false⟩) (.field (.var 2) 40))) (.int ⟨32, false⟩ h.bitCount) :=
    EvE.cast hLoad40 hCast40
  have h12_7 : s7.locals 12 = some (.int ⟨64, false⟩ h.paletteOffset) := by
    rw [show s7.locals = s6.locals.upd 13 (.int ⟨64, false⟩ h.paletteEntries) from rfl,
        show s6.locals = s5.locals.upd 12 (.int ⟨64, false⟩ h.paletteOffset) from rfl]
    rw [Locals.upd_ne _ _ (by decide : ¬ (12 : Nat) = 13), Locals.upd_same]
  have h13_7 : s7.locals 13 = some (.int ⟨64, false⟩ h.paletteEntries) := by
    rw [show s7.locals = s6.locals.upd 13 (.int ⟨64, false⟩ h.paletteEntries) from rfl]
    rw [Locals.upd_same]
  have h0_7 : s7.locals 0 = some (.ptr bd 0) := locals_upd_extract 13 (.int ⟨64, false⟩ h.paletteEntries) 0 (by decide : ¬ (0 : Nat) = 13)
    (locals_upd_extract 12 (.int ⟨64, false⟩ h.paletteOffset) 0 (by decide : ¬ (0 : Nat) = 12)
      (locals_upd_extract 11 (.int ⟨64, false⟩ h.pixelOffset) 0 (by decide : ¬ (0 : Nat) = 11)
        (locals_upd_extract 10 (.int ⟨64, false⟩ h.rowStride) 0 (by decide : ¬ (0 : Nat) = 10)
          (locals_upd_extract 9 (.int ⟨64, false⟩ h.channels) 0 (by decide : ¬ (0 : Nat) = 9)
            (locals_upd_extract 8 (.int ⟨64, false⟩ h.height) 0 (by decide : ¬ (0 : Nat) = 8)
              (locals_upd_extract 7 (.int ⟨64, false⟩ h.width) 0 (by decide : ¬ (0 : Nat) = 7) rfl))))))
  have h3_7 : s7.locals 3 = some (.ptr ob 0) := locals_upd_extract 13 (.int ⟨64, false⟩ h.paletteEntries) 3 (by decide : ¬ (3 : Nat) = 13)
    (locals_upd_extract 12 (.int ⟨64, false⟩ h.paletteOffset) 3 (by decide : ¬ (3 : Nat) = 12)
      (locals_upd_extract 11 (.int ⟨64, false⟩ h.pixelOffset) 3 (by decide : ¬ (3 : Nat) = 11)
        (locals_upd_extract 10 (.int ⟨64, false⟩ h.rowStride) 3 (by decide : ¬ (3 : Nat) = 10)
          (locals_upd_extract 9 (.int ⟨64, false⟩ h.channels) 3 (by decide : ¬ (3 : Nat) = 9)
            (locals_upd_extract 8 (.int ⟨64, false⟩ h.height) 3 (by decide : ¬ (3 : Nat) = 8)
              (locals_upd_extract 7 (.int ⟨64, false⟩ h.width) 3 (by decide : ¬ (3 : Nat) = 7) rfl))))))
  have hMulEntries : EvE Gen.prog s7 (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))) (.int ⟨64, false⟩ (h.paletteEntries * 4)) :=
    EvE.bin (EvE.var h13_7) (EvE.cast (EvE.const _) (u32_u64_cast 4 (by omega))) (bin_u64_mul h.paletteEntries 4 (by omega))
  have hSubLen12 : EvE Gen.prog s7 (.bin .sub (some ⟨64, false⟩) (.var 1) (.var 12)) (.int ⟨64, false⟩ (d.length - h.paletteOffset)) :=
    EvE.bin (EvE.var h1_7) (EvE.var h12_7) (bin_u64_sub d.length h.paletteOffset (by omega))
  have hGt3 : EvE Gen.prog s7 (.bin .gt (some ⟨64, false⟩) (.var 12) (.var 1)) (boolVal false) := by
    have hdec : decide (h.paletteOffset > d.length) = false := decide_eq_false (by omega)
    exact EvE.bin (EvE.var h12_7) (EvE.var h1_7) (by rw [bin_u64_gt, hdec])
  have hGt4 : EvE Gen.prog s7 (.bin .gt (some ⟨64, false⟩) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))) (.bin .sub (some ⟨64, false⟩) (.var 1) (.var 12))) (boolVal false) := by
    have hdec : decide (h.paletteEntries * 4 > d.length - h.paletteOffset) = false := decide_eq_false (by omega)
    exact EvE.bin hMulEntries hSubLen12 (by rw [bin_u64_gt, hdec])
  have hPalOr : EvE Gen.prog s7 (.lor (.bin .gt (some ⟨64, false⟩) (.var 12) (.var 1)) (.bin .gt (some ⟨64, false⟩) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))) (.bin .sub (some ⟨64, false⟩) (.var 1) (.var 12)))) (boolVal false) :=
    EvE.lor_false hGt3 truthy_false hGt4 truthy_false
  have hPalSkip : ExS Gen.prog s7
      (.ite (.lor (.bin .gt (some ⟨64, false⟩) (.var 12) (.var 1))
        (.bin .gt (some ⟨64, false⟩) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))) (.bin .sub (some ⟨64, false⟩) (.var 1) (.var 12))))
        (.ret (some (.const (.int ⟨32, true⟩ 9)))) .skip)
      .normal s7 :=
    ExS.ite hPalOr truthy_false ExS.skip
  -- ==== dispatch on bitCount ====
  -- Assembler: given an execution of the bit_count split from s7 plus the
  -- final memory, run the proven prologue and the tail `.ret 0`.
  have hFin : ∀ (sI : State),
      ExS Gen.prog s7
        (.ite (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.load (.int ⟨16, false⟩) (.field (.var 2) 40))) (.const (.int ⟨32, false⟩ 8)))
          (.seq (.ite (.lor (.bin .gt (some ⟨64, false⟩) (.var 12) (.var 1)) (.bin .gt (some ⟨64, false⟩) (.bin .mul (some ⟨64, false⟩) (.var 13) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))) (.bin .sub (some ⟨64, false⟩) (.var 1) (.var 12)))) (.ret (some (.const (.int ⟨32, true⟩ 9)))) .skip) (.seq (.set 5 (.const (.int ⟨32, false⟩ 0))) Gen.ni_bmp_decode_into_loop1))
          (.seq (.set 19 (.cast ⟨64, false⟩ (.cond (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.load (.int ⟨16, false⟩) (.field (.var 2) 40))) (.const (.int ⟨32, false⟩ 32))) (.const (.int ⟨32, false⟩ 4)) (.const (.int ⟨32, false⟩ 3))))) (.seq (.set 5 (.const (.int ⟨32, false⟩ 0))) Gen.ni_bmp_decode_into_loop3)))
        .normal sI →
      sI.mem ob = some (bmpRowsBytes d h h.height ++ obl.drop (h.height * bmpRowSize h)) →
      ∃ s', ExS Gen.prog s Gen.ni_bmp_decode_into.body (.ret (some (.int ⟨32, true⟩ 0))) s' ∧
        s'.mem ob = some (bmpRowsBytes d h h.height ++ obl.drop (h.height * bmpRowSize h)) := by
    intro sI hb hmem
    refine ⟨sI, ?_, hmem⟩
    exact ExS.seq hSkipCap (ExS.seq hSet7 (ExS.seq hSet8 (ExS.seq hSet9 (ExS.seq hSet10
      (ExS.seq hSet11 (ExS.seq hSet12 (ExS.seq hSet13 (ExS.seq hTruncSkip (ExS.seq hTruncSkip2
      (ExS.seq hb (ExS.ret (EvE.const _))))))))))))
  by_cases hbc8i : h.bitCount = 8
  · -- ==== 8-bit indexed (palette) path ====
    have hEq8 : EvE Gen.prog s7 (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.load (.int ⟨16, false⟩) (.field (.var 2) 40))) (.const (.int ⟨32, false⟩ 8))) (boolVal true) := by
      have hdec : decide (h.bitCount = 8) := decide_eq_true hbc8i
      exact EvE.bin hHcast40 (EvE.const _) (by rw [bin_u32_eq, hdec])
    have hSet5 : ExS Gen.prog s7 (.set 5 (.const (.int ⟨32, false⟩ 0))) .normal { s7 with locals := s7.locals.upd 5 (.int ⟨32, false⟩ 0) } :=
      ExS.set (EvE.const _)
    let s8 : State := { s7 with locals := s7.locals.upd 5 (.int ⟨32, false⟩ 0) }
    have hmem0 : s8.mem ob = some (bmpRowsBytes d h 0 ++ obl.drop (0 * (h.width * 3))) := by
      rw [show s8.mem = m from rfl, bmpRowsBytes_zero, Nat.zero_mul, List.drop_zero, List.nil_append]
      exact hob
    have hmembd0 : s8.mem bd = some d := by
      rw [show s8.mem = m from rfl]; exact hm
    have hmem20 : s8.mem 3 = some info := by
      rw [show s8.mem = m from rfl]; exact hinfo
    have hl0_8 : s8.locals 0 = some (.ptr bd 0) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 0 (by decide : ¬ (0 : Nat) = 5) h0_7
    have hl2_8 : s8.locals 2 = some (.ptr 3 0) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 2 (by decide : ¬ (2 : Nat) = 5) hl2_7
    have hl3_8 : s8.locals 3 = some (.ptr ob 0) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 3 (by decide : ¬ (3 : Nat) = 5) h3_7
    have hl5_8 : s8.locals 5 = some (.int ⟨32, false⟩ 0) := by
      rw [show s8.locals = s7.locals.upd 5 (.int ⟨32, false⟩ 0) from rfl]
      rw [Locals.upd_same]
    have hl7_8 : s8.locals 7 = some (.int ⟨64, false⟩ h.width) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 7 (by decide : ¬ (7 : Nat) = 5) h7_7
    have hl8_8 : s8.locals 8 = some (.int ⟨64, false⟩ h.height) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 8 (by decide : ¬ (8 : Nat) = 5) h8_7
    have hl9_8 : s8.locals 9 = some (.int ⟨64, false⟩ h.channels) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 9 (by decide : ¬ (9 : Nat) = 5) h9_7
    have hl10_8 : s8.locals 10 = some (.int ⟨64, false⟩ h.rowStride) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 10 (by decide : ¬ (10 : Nat) = 5) h10_7
    have hl11_8 : s8.locals 11 = some (.int ⟨64, false⟩ h.pixelOffset) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 11 (by decide : ¬ (11 : Nat) = 5) h11_7
    have hl12_8 : s8.locals 12 = some (.int ⟨64, false⟩ h.paletteOffset) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 12 (by decide : ¬ (12 : Nat) = 5) h12_7
    have hl13_8 : s8.locals 13 = some (.int ⟨64, false⟩ h.paletteEntries) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 13 (by decide : ¬ (13 : Nat) = 5) h13_7
    obtain ⟨sI, hLoopI, hMemI⟩ :=
      loop1_iter m d obl bd ob hm hd hob hd0 ho2 bd2 info hinfo h48 h hbc8i hw hwv hht hhtwv htop htopd
        (by
          have h3 : h.channels = 3 := by
            rw [hc32, ite_eq_right (show h.bitCount ≠ 32 from by omega)]
          have e : h.outSize = h.height * (h.width * 3) := by
            rw [houtsz, h3, ← Nat.mul_assoc]
            ac_rfl
          rw [← e]
          exact hout)
        hobl64 hpx8 hpos8 hidx8 hok hwidth ro hro
        h.height 0 s8 (by omega) (by omega)
        hl0_8 hl2_8 hl3_8 hl5_8 hl7_8 hl8_8 hl9_8 hl10_8 hl11_8 hl12_8 hl13_8 hros
        hmem0 hmembd0 hmem20
    have hRS8 : bmpRowSize h = h.width * 3 := by
      simp only [bmpRowSize, bmpPixelSize, hbc8i, ite_true]
    refine hFin sI (ExS.ite hEq8 truthy_true (ExS.seq hPalSkip (ExS.seq hSet5 hLoopI))) ?_
    rw [hMemI, hRS8]
  · -- ==== 24/32-bit direct path ====
    have hEqNot8 : EvE Gen.prog s7 (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.load (.int ⟨16, false⟩) (.field (.var 2) 40))) (.const (.int ⟨32, false⟩ 8))) (boolVal false) := by
      have hdec : decide (h.bitCount = 8) = false := decide_eq_false hbc8i
      exact EvE.bin hHcast40 (EvE.const _) (by rw [bin_u32_eq, hdec])
    have hchc64 : h.channels < 4294967296 := by
      cases hchc with
      | inl h3 => rw [h3]; omega
      | inr h4 => rw [h4]; omega
    have hCond : EvE Gen.prog s7 (.cond (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.load (.int ⟨16, false⟩) (.field (.var 2) 40))) (.const (.int ⟨32, false⟩ 32))) (.const (.int ⟨32, false⟩ 4)) (.const (.int ⟨32, false⟩ 3))) (.int ⟨32, false⟩ (if h.bitCount = 32 then 4 else 3)) := by
      by_cases hbc32 : h.bitCount = 32
      · rw [ite_eq_left hbc32]
        have hdec : decide (h.bitCount = 32) := decide_eq_true hbc32
        exact EvE.cond (EvE.bin hHcast40 (EvE.const _) (by rw [bin_u32_eq, hdec])) truthy_true (EvE.const _)
      · rw [ite_eq_right hbc32]
        have hdec : decide (h.bitCount = 32) = false := decide_eq_false hbc32
        exact EvE.cond (EvE.bin hHcast40 (EvE.const _) (by rw [bin_u32_eq, hdec])) truthy_false (EvE.const _)
    have hCastCh : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ (if h.bitCount = 32 then 4 else 3)) = .ok (.int ⟨64, false⟩ h.channels) := by
      rw [← hc32]
      exact u32_u64_cast h.channels hchc64
    have hSet19 : ExS Gen.prog s7
        (.set 19 (.cast ⟨64, false⟩ (.cond (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.load (.int ⟨16, false⟩) (.field (.var 2) 40))) (.const (.int ⟨32, false⟩ 32))) (.const (.int ⟨32, false⟩ 4)) (.const (.int ⟨32, false⟩ 3)))))
        .normal { s7 with locals := s7.locals.upd 19 (.int ⟨64, false⟩ h.channels) } :=
      ExS.set (EvE.cast hCond hCastCh)
    let s8D : State := { s7 with locals := s7.locals.upd 19 (.int ⟨64, false⟩ h.channels) }
    have hSet5D : ExS Gen.prog s8D (.set 5 (.const (.int ⟨32, false⟩ 0))) .normal { s8D with locals := s8D.locals.upd 5 (.int ⟨32, false⟩ 0) } :=
      ExS.set (EvE.const _)
    let s9D : State := { s8D with locals := s8D.locals.upd 5 (.int ⟨32, false⟩ 0) }
    have hmem0D : s9D.mem ob = some (bmpRowsBytes d h 0 ++ obl.drop (0 * (h.width * h.channels))) := by
      rw [show s9D.mem = m from rfl, bmpRowsBytes_zero, Nat.zero_mul, List.drop_zero, List.nil_append]
      exact hob
    have hmembdD : s9D.mem bd = some d := by
      rw [show s9D.mem = m from rfl]; exact hm
    have hmem2D : s9D.mem 3 = some info := by
      rw [show s9D.mem = m from rfl]; exact hinfo
    have hl0_D : s9D.locals 0 = some (.ptr bd 0) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 0 (by decide : ¬ (0 : Nat) = 5)
        (locals_upd_extract 19 (.int ⟨64, false⟩ h.channels) 0 (by decide : ¬ (0 : Nat) = 19) h0_7)
    have hl2_D : s9D.locals 2 = some (.ptr 3 0) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 2 (by decide : ¬ (2 : Nat) = 5)
        (locals_upd_extract 19 (.int ⟨64, false⟩ h.channels) 2 (by decide : ¬ (2 : Nat) = 19) hl2_7)
    have hl3_D : s9D.locals 3 = some (.ptr ob 0) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 3 (by decide : ¬ (3 : Nat) = 5)
        (locals_upd_extract 19 (.int ⟨64, false⟩ h.channels) 3 (by decide : ¬ (3 : Nat) = 19) h3_7)
    have hl5_D : s9D.locals 5 = some (.int ⟨32, false⟩ 0) := by
      rw [show s9D.locals = s8D.locals.upd 5 (.int ⟨32, false⟩ 0) from rfl]
      rw [Locals.upd_same]
    have hl7_D : s9D.locals 7 = some (.int ⟨64, false⟩ h.width) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 7 (by decide : ¬ (7 : Nat) = 5)
        (locals_upd_extract 19 (.int ⟨64, false⟩ h.channels) 7 (by decide : ¬ (7 : Nat) = 19) h7_7)
    have hl8_D : s9D.locals 8 = some (.int ⟨64, false⟩ h.height) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 8 (by decide : ¬ (8 : Nat) = 5)
        (locals_upd_extract 19 (.int ⟨64, false⟩ h.channels) 8 (by decide : ¬ (8 : Nat) = 19) h8_7)
    have hl9_D : s9D.locals 9 = some (.int ⟨64, false⟩ h.channels) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 9 (by decide : ¬ (9 : Nat) = 5)
        (locals_upd_extract 19 (.int ⟨64, false⟩ h.channels) 9 (by decide : ¬ (9 : Nat) = 19) h9_7)
    have hl10_D : s9D.locals 10 = some (.int ⟨64, false⟩ h.rowStride) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 10 (by decide : ¬ (10 : Nat) = 5)
        (locals_upd_extract 19 (.int ⟨64, false⟩ h.channels) 10 (by decide : ¬ (10 : Nat) = 19) h10_7)
    have hl11_D : s9D.locals 11 = some (.int ⟨64, false⟩ h.pixelOffset) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 11 (by decide : ¬ (11 : Nat) = 5)
        (locals_upd_extract 19 (.int ⟨64, false⟩ h.channels) 11 (by decide : ¬ (11 : Nat) = 19) h11_7)
    have hl12_D : s9D.locals 12 = some (.int ⟨64, false⟩ h.paletteOffset) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 12 (by decide : ¬ (12 : Nat) = 5)
        (locals_upd_extract 19 (.int ⟨64, false⟩ h.channels) 12 (by decide : ¬ (12 : Nat) = 19) h12_7)
    have hl13_D : s9D.locals 13 = some (.int ⟨64, false⟩ h.paletteEntries) :=
      locals_upd_extract 5 (.int ⟨32, false⟩ 0) 13 (by decide : ¬ (13 : Nat) = 5)
        (locals_upd_extract 19 (.int ⟨64, false⟩ h.channels) 13 (by decide : ¬ (13 : Nat) = 19) h13_7)
    have hl19_D : s9D.locals 19 = some (.int ⟨64, false⟩ h.channels) := by
      rw [show s9D.locals = s8D.locals.upd 5 (.int ⟨32, false⟩ 0) from rfl,
          show s8D.locals = s7.locals.upd 19 (.int ⟨64, false⟩ h.channels) from rfl]
      rw [Locals.upd_ne _ _ (by decide : ¬ (19 : Nat) = 5), Locals.upd_same]
    have hsrcD : ∀ y i, y < h.height → i < h.width → h.pixelOffset + (if h.topDown = 1 then y else h.height - 1 - y) * h.rowStride + i * h.channels + h.channels ≤ d.length := by
      intro y i hy hi
      have hge : h.width * h.channels ≤ h.rowStride := hrsd hbc8i
      have hiw : i * h.channels + h.channels ≤ h.width * h.channels := by
        have h2 : (i + 1) * h.channels ≤ h.width * h.channels := Nat.mul_le_mul_right (k := h.channels) (by omega)
        have e : (i + 1) * h.channels = i * h.channels + h.channels := by rw [Nat.add_mul, Nat.one_mul]
        omega
      have hrow : h.rowStride * h.height = (h.height - 1) * h.rowStride + h.rowStride := by
        have h1 : 1 ≤ h.height := by omega
        have hD : h.rowStride * 1 ≤ h.rowStride * h.height := Nat.mul_le_mul_left (k := h.rowStride) h1
        have e1 : (h.height - 1) * h.rowStride = h.rowStride * h.height - h.rowStride := by
          rw [Nat.mul_comm (h.height - 1) h.rowStride, Nat.mul_sub, Nat.mul_one]
        omega
      by_cases htd : h.topDown = 1
      · rw [ite_eq_left htd]
        have hsy : y * h.rowStride ≤ (h.height - 1) * h.rowStride := Nat.mul_le_mul_right (k := h.rowStride) (by omega)
        have hpx' : h.pixelOffset + h.rowStride * h.height ≤ d.length := hpx
        omega
      · rw [ite_eq_right htd]
        have hsy : (h.height - 1 - y) * h.rowStride ≤ (h.height - 1) * h.rowStride := Nat.mul_le_mul_right (k := h.rowStride) (by omega)
        have hpx' : h.pixelOffset + h.rowStride * h.height ≤ d.length := hpx
        omega
    obtain ⟨sI, hLoopI, hMemI⟩ :=
      loop3_iter m d obl bd ob hm hd hob hd0 ho2 bd2 info hinfo h48 h hbc8i hchc hc32 hw hwv hht hhtwv htop htopd
        (by
          have hRSch : h.outSize = h.height * (h.width * h.channels) := by
            rw [houtsz, ← Nat.mul_assoc]
            ac_rfl
          rw [← hRSch]
          exact hout)
        hobl64 hsrcD hok hwidth ro hro
        h.height 0 s9D (by omega) (by omega)
        hl0_D hl2_D hl3_D hl5_D hl7_D hl8_D hl9_D hl10_D hl11_D hl12_D hl13_D hl19_D hros
        hmem0D hmembdD hmem2D
    have hRS2 : bmpRowSize h = h.width * h.channels := by
      show h.width * (if h.bitCount = 8 then 3 else h.channels) = h.width * h.channels
      rw [ite_eq_right hbc8i]
    refine hFin sI (ExS.ite hEqNot8 truthy_false (ExS.seq hSet19 (ExS.seq hSet5D hLoopI))) ?_
    rw [hMemI, hRS2]
end NANO.C.Proofs
