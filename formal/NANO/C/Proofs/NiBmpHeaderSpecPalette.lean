/-
  Spec-side fact: in the `bitCount = 8` palette path, `bmpOutputCompose`
  selects palette entries as `if colorsUsed ≠ 0 then colorsUsed else 256`,
  and accepts only entries within bounds.
-/
import NANO.Bmp
import NANO.Spec
import NANO.C.Lemmas
import NANO.C.Proofs.NiGeometryTail
import NANO.C.Proofs.NiBmpHeaderSpec
import NANO.C.Proofs.NiBmpHeaderSpecGeo

open NANO NANO.C NANO.C.Proofs

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000

namespace NANO

/-- In the plan-format boundary: entries chosen by `bmpOutputCompose` for the
    8-bit palette path. -/
def paletteEntriesUsed (colorsUsed : Nat) : Nat :=
  if colorsUsed ≠ 0 then colorsUsed else 256

/-- If colors_used is non-zero, entries equal colors_used; else 256. -/
theorem paletteEntriesUsed_eq_of_ne_zero {c : Nat} (h : c ≠ 0) :
    paletteEntriesUsed c = c := by
  unfold paletteEntriesUsed; rw [if_pos h]

theorem paletteEntriesUsed_eq_of_zero {c : Nat} (h : c = 0) :
    paletteEntriesUsed c = 256 := by
  unfold paletteEntriesUsed; rw [if_neg (by rw [h]; decide)]

/-- Entries are always ≤ 256 when selected by this rule for a rejection-free
    bmp: colors_used=0 → 256; 0 < colors_used → colors_used, and the C bound
    check rejects colors_used > 256. This is the selection half of binding ☆. -/
theorem paletteEntriesUsed_lt_or_eq_256 {c : Nat} :
    paletteEntriesUsed c ≤ 256 ∨ paletteEntriesUsed c = c := by
  unfold paletteEntriesUsed
  by_cases h : c ≠ 0
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl (by decide)

/-- The bound-check threshold used by `bmpOutputCompose`:
    `paletteOffset + entries*4 > pixelOffset` is the rejection. -/
theorem palette_bounds_lemma (paletteOffset entries pixelOffset : Nat) :
    paletteOffset + entries * 4 > pixelOffset ↔
    pixelOffset < paletteOffset + entries * 4 := Iff.rfl

end NANO

namespace NANO

/-- `sizeMulOK W b = true` for in-range dims with `b ≤ 32, W ≤ 2147483647`. -/
theorem sizeMulOK_w_b {W b : Nat} (hW : W ≤ 2147483647) (hb : b ≤ 32) :
    sizeMulOK W b = true := by
  apply sizeMulOK_true_of_mulLE
  have hwb : W * b ≤ 2147483647 * 32 := Nat.mul_le_mul hW hb
  have h32 : 2147483647 * 32 = 68719476704 := by decide
  rw [h32] at hwb
  have heq : sizeMax = 18446744073709551615 := by decide
  rw [heq]
  omega
/-- `sizeMulOK W c = true` given `c ≤ 4, W ≤ 2147483647`. -/
theorem sizeMulOK_w_c {W c : Nat} (hW : W ≤ 2147483647) (hc : c ≤ 4) :
    sizeMulOK W c = true := sizeMulOK_true_of_mulLE (by
  have hwb : W * c ≤ 2147483647 * 4 := Nat.mul_le_mul hW hc
  have h4 : 2147483647 * 4 = 8589934588 := by decide
  rw [h4] at hwb
  have heq : sizeMax = 18446744073709551615 := by decide
  rw [heq]
  omega)

/-- `sizeMulOK (W * c) H = true`. -/
theorem sizeMulOK_wc_h {W c H : Nat} (hW : W ≤ 2147483647) (hc : c ≤ 4) (hH : H ≤ 2147483648) :
    sizeMulOK (W * c) H = true := sizeMulOK_true_of_mulLE (by
  have hwc : W * c ≤ 8589934588 := by
    have hw' : W ≤ 2147483647 := hW
    have hc' : c ≤ 4 := hc
    have h4 : 2147483647 * 4 = 8589934588 := by decide
    have := Nat.mul_le_mul hw' hc'
    omega
  have hOSH : (W * c) * H ≤ 8589934588 * 2147483648 := Nat.mul_le_mul hwc hH
  have hLit : 8589934588 * 2147483648 = 18446744065119617024 := by decide
  rw [hLit] at hOSH
  have heq : sizeMax = 18446744073709551615 := by decide
  rw [heq]
  omega)

/-- `sizeMulOK ((W * b + 31) / 32 * 4) H = true`. -/
theorem sizeMulOK_row_h {W b H : Nat} (hW : W ≤ 2147483647) (hb : b ≤ 32) (hH : H ≤ 2147483648) :
    sizeMulOK ((W * b + 31) / 32 * 4) H = true := sizeMulOK_true_of_mulLE (by
  have hwb : W * b ≤ 2147483647 * 32 := Nat.mul_le_mul hW hb
  have h32 : 2147483647 * 32 = 68719476704 := by decide
  have hrow : (W * b + 31) / 32 * 4 ≤ 8589934588 := by
    omega
  have hOSH : ((W * b + 31) / 32 * 4) * H ≤ 8589934588 * 2147483648 := Nat.mul_le_mul hrow hH
  have hLit : 8589934588 * 2147483648 = 18446744065119617024 := by decide
  rw [hLit] at hOSH
  have heq : sizeMax = 18446744073709551615 := by decide
  rw [heq]
  omega)

/-- `bmpOutputCompose` returns `.error 10` when the 8-bit palette check fails. -/
theorem bmpOutputCompose_ten (size : Nat) (d : List UInt8)
    (W H b c t cU : Nat) (hb : b ≤ 32) (hc : c ≤ 4) (hW : W ≤ 2147483647) (hH : H ≤ 2147483648)
    (hNotTrunc : ¬ (rd32le d 10 > sizeMax - ((W * b + 31) / 32) * 4 * H ∨ rd32le d 10 + ((W * b + 31) / 32) * 4 * H > size))
    (h8 : b = 8)
    (hEntriesBad : (if cU = 0 then 256 else cU) = 0 ∨ (256 < if cU = 0 then 256 else cU)
                   ∨ rd32le d 10 < 14 + rd32le d 14 + (if cU = 0 then 256 else cU) * 4) :
    bmpOutputCompose size d (W, H, b, c, t, cU) = .error 10 := by
  have hMul_wb := sizeMulOK_w_b hW hb
  have hMul_wc := sizeMulOK_w_c hW hc
  have hMul_wH := sizeMulOK_wc_h hW hc hH
  have hMul_row := sizeMulOK_row_h hW hb hH
  have hBad' : ¬ (sizeMax - (W * b + 31) / 32 * 4 * H < rd32le d 10 ∨
      size < rd32le d 10 + (W * b + 31) / 32 * 4 * H) := by
    intro hOr
    rcases hOr with h1 | h2
    · exact hNotTrunc (Or.inl (by omega))
    · exact hNotTrunc (Or.inr (by omega))
  unfold bmpOutputCompose
  simp [hMul_wb, hMul_wc, hMul_wH, hMul_row]
  rw [if_neg hBad']
  rw [if_pos h8]
  rw [if_pos hEntriesBad]
  rfl

/-- `bmpOutputCompose` succeeds when the 8-bit palette check passes. -/
theorem bmpOutputCompose_ok_8 (size : Nat) (d : List UInt8)
    (W H b c t cU : Nat) (hb : b ≤ 32) (hc : c ≤ 4) (hW : W ≤ 2147483647) (hH : H ≤ 2147483648)
    (hNotTrunc : ¬ (rd32le d 10 > sizeMax - ((W * b + 31) / 32) * 4 * H ∨ rd32le d 10 + ((W * b + 31) / 32) * 4 * H > size))
    (h8 : b = 8)
    (hEntriesGood : ¬ ((if cU = 0 then 256 else cU) = 0 ∨ (256 < if cU = 0 then 256 else cU)
                    ∨ rd32le d 10 < 14 + rd32le d 14 + (if cU = 0 then 256 else cU) * 4)) :
    bmpOutputCompose size d (W, H, b, c, t, cU) =
      .ok { rowStride := ((W * b + 31) / 32) * 4,
            outSize := W * c * H, paletteOffset := 14 + rd32le d 14, width := W, height := H,
            pixelOffset := rd32le d 10, paletteEntries := (if cU ≠ 0 then cU else 256),
            bitCount := b, channels := c, topDown := t } := by
  have hMul_wb := sizeMulOK_w_b hW hb
  have hMul_wc := sizeMulOK_w_c hW hc
  have hMul_wH := sizeMulOK_wc_h hW hc hH
  have hMul_row := sizeMulOK_row_h hW hb hH
  have hBad' : ¬ (sizeMax - (W * b + 31) / 32 * 4 * H < rd32le d 10 ∨
      size < rd32le d 10 + (W * b + 31) / 32 * 4 * H) := by
    intro hOr
    rcases hOr with h1 | h2
    · exact hNotTrunc (Or.inl (by omega))
    · exact hNotTrunc (Or.inr (by omega))
  have hE : (if cU ≠ 0 then cU else 256) = (if cU = 0 then 256 else cU) := by
    by_cases h : cU = 0
    · rw [h]; rfl
    · rw [if_neg h, if_pos h]
  unfold bmpOutputCompose
  simp [hMul_wb, hMul_wc, hMul_wH, hMul_row]
  rw [if_neg hBad']
  rw [if_pos h8]
  rw [if_neg hEntriesGood]
  exact instPure_eq _

/-- `bmpOutputCompose` succeeds when `bitCount ≠ 8`. -/
theorem bmpOutputCompose_ok_ne8 (size : Nat) (d : List UInt8)
    (W H b c t cU : Nat) (hb : b ≤ 32) (hc : c ≤ 4) (hW : W ≤ 2147483647) (hH : H ≤ 2147483648)
    (hNotTrunc : ¬ (rd32le d 10 > sizeMax - ((W * b + 31) / 32) * 4 * H ∨ rd32le d 10 + ((W * b + 31) / 32) * 4 * H > size))
    (hB8 : b ≠ 8) :
    bmpOutputCompose size d (W, H, b, c, t, cU) =
      .ok { rowStride := ((W * b + 31) / 32) * 4, outSize := W * c * H,
            paletteOffset := 0, width := W, height := H, pixelOffset := rd32le d 10,
            paletteEntries := 0, bitCount := b, channels := c, topDown := t } := by
  have hMul_wb := sizeMulOK_w_b hW hb
  have hMul_wc := sizeMulOK_w_c hW hc
  have hMul_wH := sizeMulOK_wc_h hW hc hH
  have hMul_row := sizeMulOK_row_h hW hb hH
  have hBad' : ¬ (sizeMax - (W * b + 31) / 32 * 4 * H < rd32le d 10 ∨
      size < rd32le d 10 + (W * b + 31) / 32 * 4 * H) := by
    intro hOr
    rcases hOr with h1 | h2
    · exact hNotTrunc (Or.inl (by omega))
    · exact hNotTrunc (Or.inr (by omega))
  unfold bmpOutputCompose
  simp [hMul_wb, hMul_wc, hMul_wH, hMul_row]
  rw [if_neg hBad']
  rw [if_neg hB8]
  rfl

end NANO

namespace NANO

/-- If geometry passes but the palette check fires (bit_count = 8 and the
    palette bound fails), `bmpHeaderCode = 10`. -/
theorem bmpHeaderCode_ten_of_palette (size : Nat) (d : List UInt8)
    (hSig : sigOk size d = true) (hLay : layoutOk size d = true)
    (hG : bmpGeometryCode d = 0)
    (hNotTrunc : ¬ (rd32le d 10 > sizeMax - specRowStride (rd32le d 18) (rd16le d 28) * (NANO.toInt32 (rd32le d 22)).natAbs
           ∨ rd32le d 10 + specRowStride (rd32le d 18) (rd16le d 28) * (NANO.toInt32 (rd32le d 22)).natAbs > size))
    (h8 : rd16le d 28 = 8)
    (hEntriesBad : (if rd32le d 46 = 0 then 256 else rd32le d 46) = 0 ∨
                   (256 < if rd32le d 46 = 0 then 256 else rd32le d 46) ∨
                   rd32le d 10 < 14 + rd32le d 14 + (if rd32le d 46 = 0 then 256 else rd32le d 46) * 4) :
    bmpHeaderCode size d = 10 := by
  have h1 : ¬ (NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1) := by
    by_cases h1' : NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1
    · have he : bmpGeometryCode d = 3 := by unfold bmpGeometryCode; rw [if_pos h1']
      rw [he] at hG; contradiction
    · exact h1'
  have hgt : 0 < NANO.toInt32 (rd32le d 18) := by
    by_cases hle : NANO.toInt32 (rd32le d 18) ≤ 0
    · exact absurd (Or.inl hle) h1
    · omega
  have hsml : ¬ rd32le d 18 ≥ 2147483648 := by
    by_cases hge : rd32le d 18 ≥ 2147483648
    · have he : NANO.toInt32 (rd32le d 18) ≤ -1 := by
        simp [NANO.toInt32, hge]
        have hmax : rd32le d 18 ≤ 4294967295 := by have := rd32_lt d 18; omega
        omega
      omega
    · exact hge
  have hW : rd32le d 18 ≤ 2147483647 := by omega
  have hb32 : rd16le d 28 ≤ 32 := by
    have hbs := rd16le28_in_set_of_geomOk d hG
    cases hbs with
    | inl h8 => omega
    | inr h => cases h with
      | inl h24 => omega
      | inr h32 => omega
  have h3H : (NANO.toInt32 (rd32le d 22)).natAbs ≤ 2147483648 := height_bound_of_geomOk d hG
  have hwN : NANO.toInt32 (rd32le d 18) = (rd32le d 18 : Int) := by
    unfold NANO.toInt32; rw [if_neg (by omega)]
  have hWnat : (NANO.toInt32 (rd32le d 18)).toNat = rd32le d 18 := by
    rw [hwN]; rfl
  unfold bmpHeaderCode
  have hSigOk := bmpSigGate_ok_of_sigOk size d hSig
  have hLayOk := bmpLayoutGate_ok_of_layoutOk size d hLay
  unfold bmpHeader
  rw [hSigOk, bind_ok_of_ok]
  rw [hLayOk, bind_ok_of_ok]
  -- Both LT and non-LT branches produce a tuple with the same shape
  by_cases hLT : NANO.toInt32 (rd32le d 22) < 0
  · by_cases h2 : NANO.toInt32 (rd32le d 22) = -2147483648
    · have he : bmpGeometryCode d = 4 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_pos h2]
      rw [he] at hG; contradiction
    · by_cases h5 : rd32le d 30 ≠ 0
      · have he : bmpGeometryCode d = 5 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_neg h2, if_pos h5]
        rw [he] at hG; contradiction
      · by_cases h6 : rd16le d 28 ≠ 8 ∧ rd16le d 28 ≠ 24 ∧ rd16le d 28 ≠ 32
        · have he : bmpGeometryCode d = 6 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_neg h2, if_neg h5, if_pos h6]
          rw [he] at hG; contradiction
        · have hStage : bmpGeometryStage size d =
              .ok ((NANO.toInt32 (rd32le d 18)).toNat, (NANO.toInt32 (rd32le d 22)).natAbs, rd16le d 28,
                   if rd16le d 28 = 32 then 4 else 3, 1, rd32le d 46) := by
            unfold bmpGeometryStage; rw [if_neg h1, if_pos hLT, if_neg h2, if_neg h5, if_neg h6]; rfl
          rw [hStage, bind_ok_of_ok]
          have hW' : (NANO.toInt32 (rd32le d 18)).toNat ≤ 2147483647 := by
            rw [hwN]; exact hW
          have hNotTrunc' : ¬ (rd32le d 10 > sizeMax - ((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32 * 4 * (NANO.toInt32 (rd32le d 22)).natAbs ∨ rd32le d 10 + ((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32 * 4 * (NANO.toInt32 (rd32le d 22)).natAbs > size) := by
            intro hOr
            apply hNotTrunc
            rw [hWnat] at hOr
            exact hOr
          have hTen := @bmpOutputCompose_ten size d
            (W := (NANO.toInt32 (rd32le d 18)).toNat)
            (H := (NANO.toInt32 (rd32le d 22)).natAbs)
            (b := rd16le d 28)
            (c := if rd16le d 28 = 32 then 4 else 3)
            (t := 1) (cU := rd32le d 46)
            hb32
            (channels_le_4 (rd16le d 28))
            hW' h3H hNotTrunc' h8 hEntriesBad
          rw [hTen]
  · by_cases h5 : rd32le d 30 ≠ 0
    · have he : bmpGeometryCode d = 5 := by unfold bmpGeometryCode; rw [if_neg h1, if_neg hLT, if_pos h5]
      rw [he] at hG; contradiction
    · by_cases h6 : rd16le d 28 ≠ 8 ∧ rd16le d 28 ≠ 24 ∧ rd16le d 28 ≠ 32
      · have he : bmpGeometryCode d = 6 := by unfold bmpGeometryCode; rw [if_neg h1, if_neg hLT, if_neg h5, if_pos h6]
        rw [he] at hG; contradiction
      · have hStage : bmpGeometryStage size d =
            .ok ((NANO.toInt32 (rd32le d 18)).toNat, (NANO.toInt32 (rd32le d 22)).natAbs, rd16le d 28,
                 if rd16le d 28 = 32 then 4 else 3, 0, rd32le d 46) := by
          unfold bmpGeometryStage; rw [if_neg h1, if_neg hLT, if_neg h5, if_neg h6]; rfl
        rw [hStage, bind_ok_of_ok]
        have hW' : (NANO.toInt32 (rd32le d 18)).toNat ≤ 2147483647 := by
          rw [hwN]; exact hW
        have hNotTrunc' : ¬ (rd32le d 10 > sizeMax - ((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32 * 4 * (NANO.toInt32 (rd32le d 22)).natAbs ∨ rd32le d 10 + ((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32 * 4 * (NANO.toInt32 (rd32le d 22)).natAbs > size) := by
          intro hOr
          apply hNotTrunc
          rw [hWnat] at hOr
          exact hOr
        have hTen := @bmpOutputCompose_ten size d
          (W := (NANO.toInt32 (rd32le d 18)).toNat)
          (H := (NANO.toInt32 (rd32le d 22)).natAbs)
          (b := rd16le d 28)
          (c := if rd16le d 28 = 32 then 4 else 3)
          (t := 0) (cU := rd32le d 46)
          hb32
          (channels_le_4 (rd16le d 28))
          hW' h3H hNotTrunc' h8 hEntriesBad
        rw [hTen]


/-- If geometry passes, the truncation check does not fire, and the palette
    check passes (or bit_count ≠ 8), `bmpHeaderCode = 0`. -/
theorem bmpHeaderCode_zero_of_ok (size : Nat) (d : List UInt8)
    (hSig : sigOk size d = true) (hLay : layoutOk size d = true)
    (hG : bmpGeometryCode d = 0)
    (hNotTrunc : ¬ (rd32le d 10 > sizeMax - specRowStride (rd32le d 18) (rd16le d 28) * (NANO.toInt32 (rd32le d 22)).natAbs
           ∨ rd32le d 10 + specRowStride (rd32le d 18) (rd16le d 28) * (NANO.toInt32 (rd32le d 22)).natAbs > size))
    (hOK : rd16le d 28 ≠ 8 ∨ (rd16le d 28 = 8 ∧
             ¬ ((if rd32le d 46 = 0 then 256 else rd32le d 46) = 0 ∨
                (256 < if rd32le d 46 = 0 then 256 else rd32le d 46) ∨
                rd32le d 10 < 14 + rd32le d 14 + (if rd32le d 46 = 0 then 256 else rd32le d 46) * 4))) :
    bmpHeaderCode size d = 0 := by
  have h1 : ¬ (NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1) := by
    by_cases h1' : NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1
    · have he : bmpGeometryCode d = 3 := by unfold bmpGeometryCode; rw [if_pos h1']
      rw [he] at hG; contradiction
    · exact h1'
  have hgt : 0 < NANO.toInt32 (rd32le d 18) := by
    by_cases hle : NANO.toInt32 (rd32le d 18) ≤ 0
    · exact absurd (Or.inl hle) h1
    · omega
  have hsml : ¬ rd32le d 18 ≥ 2147483648 := by
    by_cases hge : rd32le d 18 ≥ 2147483648
    · have he : NANO.toInt32 (rd32le d 18) ≤ -1 := by
        simp [NANO.toInt32, hge]
        have hmax : rd32le d 18 ≤ 4294967295 := by have := rd32_lt d 18; omega
        omega
      omega
    · exact hge
  have hW : rd32le d 18 ≤ 2147483647 := by omega
  have hb32 : rd16le d 28 ≤ 32 := by
    have hbs := rd16le28_in_set_of_geomOk d hG
    cases hbs with
    | inl h8 => omega
    | inr h => cases h with
      | inl h24 => omega
      | inr h32 => omega
  have h3H : (NANO.toInt32 (rd32le d 22)).natAbs ≤ 2147483648 := height_bound_of_geomOk d hG
  have hwN : NANO.toInt32 (rd32le d 18) = (rd32le d 18 : Int) := by
    unfold NANO.toInt32; rw [if_neg (by omega)]
  have hWnat : (NANO.toInt32 (rd32le d 18)).toNat = rd32le d 18 := by
    rw [hwN]; rfl
  unfold bmpHeaderCode
  have hSigOk := bmpSigGate_ok_of_sigOk size d hSig
  have hLayOk := bmpLayoutGate_ok_of_layoutOk size d hLay
  unfold bmpHeader
  rw [hSigOk, bind_ok_of_ok]
  rw [hLayOk, bind_ok_of_ok]
  -- Both LT and non-LT branches produce a tuple with the same shape
  by_cases hLT : NANO.toInt32 (rd32le d 22) < 0
  · by_cases h2 : NANO.toInt32 (rd32le d 22) = -2147483648
    · have he : bmpGeometryCode d = 4 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_pos h2]
      rw [he] at hG; contradiction
    · by_cases h5 : rd32le d 30 ≠ 0
      · have he : bmpGeometryCode d = 5 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_neg h2, if_pos h5]
        rw [he] at hG; contradiction
      · by_cases h6 : rd16le d 28 ≠ 8 ∧ rd16le d 28 ≠ 24 ∧ rd16le d 28 ≠ 32
        · have he : bmpGeometryCode d = 6 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_neg h2, if_neg h5, if_pos h6]
          rw [he] at hG; contradiction
        · have hStage : bmpGeometryStage size d =
              .ok ((NANO.toInt32 (rd32le d 18)).toNat, (NANO.toInt32 (rd32le d 22)).natAbs, rd16le d 28,
                   if rd16le d 28 = 32 then 4 else 3, 1, rd32le d 46) := by
            unfold bmpGeometryStage; rw [if_neg h1, if_pos hLT, if_neg h2, if_neg h5, if_neg h6]; rfl
          rw [hStage, bind_ok_of_ok]
          have hW' : (NANO.toInt32 (rd32le d 18)).toNat ≤ 2147483647 := by
            rw [hwN]; exact hW
          have hNotTrunc' : ¬ (rd32le d 10 > sizeMax - ((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32 * 4 * (NANO.toInt32 (rd32le d 22)).natAbs ∨ rd32le d 10 + ((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32 * 4 * (NANO.toInt32 (rd32le d 22)).natAbs > size) := by
            intro hOr
            apply hNotTrunc
            rw [hWnat] at hOr
            exact hOr
          by_cases hB8 : rd16le d 28 ≠ 8
          · have hOk := @bmpOutputCompose_ok_ne8 size d
              (W := (NANO.toInt32 (rd32le d 18)).toNat)
              (H := (NANO.toInt32 (rd32le d 22)).natAbs)
              (b := rd16le d 28)
              (c := if rd16le d 28 = 32 then 4 else 3)
              (t := 1) (cU := rd32le d 46)
              hb32
              (channels_le_4 (rd16le d 28))
              hW' h3H hNotTrunc' hB8
            rw [hOk]
          · have hOK' := hOK.resolve_left hB8
            have hOk := @bmpOutputCompose_ok_8 size d
              (W := (NANO.toInt32 (rd32le d 18)).toNat)
              (H := (NANO.toInt32 (rd32le d 22)).natAbs)
              (b := rd16le d 28)
              (c := if rd16le d 28 = 32 then 4 else 3)
              (t := 1) (cU := rd32le d 46)
              hb32
              (channels_le_4 (rd16le d 28))
              hW' h3H hNotTrunc' hOK'.1 hOK'.2
            rw [hOk]
  · by_cases h5 : rd32le d 30 ≠ 0
    · have he : bmpGeometryCode d = 5 := by unfold bmpGeometryCode; rw [if_neg h1, if_neg hLT, if_pos h5]
      rw [he] at hG; contradiction
    · by_cases h6 : rd16le d 28 ≠ 8 ∧ rd16le d 28 ≠ 24 ∧ rd16le d 28 ≠ 32
      · have he : bmpGeometryCode d = 6 := by unfold bmpGeometryCode; rw [if_neg h1, if_neg hLT, if_neg h5, if_pos h6]
        rw [he] at hG; contradiction
      · have hStage : bmpGeometryStage size d =
            .ok ((NANO.toInt32 (rd32le d 18)).toNat, (NANO.toInt32 (rd32le d 22)).natAbs, rd16le d 28,
                 if rd16le d 28 = 32 then 4 else 3, 0, rd32le d 46) := by
          unfold bmpGeometryStage; rw [if_neg h1, if_neg hLT, if_neg h5, if_neg h6]; rfl
        rw [hStage, bind_ok_of_ok]
        have hW' : (NANO.toInt32 (rd32le d 18)).toNat ≤ 2147483647 := by
          rw [hwN]; exact hW
        have hNotTrunc' : ¬ (rd32le d 10 > sizeMax - ((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32 * 4 * (NANO.toInt32 (rd32le d 22)).natAbs ∨ rd32le d 10 + ((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32 * 4 * (NANO.toInt32 (rd32le d 22)).natAbs > size) := by
          intro hOr
          apply hNotTrunc
          rw [hWnat] at hOr
          exact hOr
        by_cases hB8 : rd16le d 28 ≠ 8
        · have hOk := @bmpOutputCompose_ok_ne8 size d
            (W := (NANO.toInt32 (rd32le d 18)).toNat)
            (H := (NANO.toInt32 (rd32le d 22)).natAbs)
            (b := rd16le d 28)
            (c := if rd16le d 28 = 32 then 4 else 3)
            (t := 0) (cU := rd32le d 46)
            hb32
            (channels_le_4 (rd16le d 28))
            hW' h3H hNotTrunc' hB8
          rw [hOk]
        · have hOK' := hOK.resolve_left hB8
          have hOk := @bmpOutputCompose_ok_8 size d
            (W := (NANO.toInt32 (rd32le d 18)).toNat)
            (H := (NANO.toInt32 (rd32le d 22)).natAbs)
            (b := rd16le d 28)
            (c := if rd16le d 28 = 32 then 4 else 3)
            (t := 0) (cU := rd32le d 46)
            hb32
            (channels_le_4 (rd16le d 28))
            hW' h3H hNotTrunc' hOK'.1 hOK'.2
          rw [hOk]


end NANO
