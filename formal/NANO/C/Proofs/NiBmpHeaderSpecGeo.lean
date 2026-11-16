/-
  Spec-side fact: if the geometry check `bmpGeometryStage` rejects with a
  non-zero code, `bmpHeader` throws that same code (and symmetrically).
-/
import NANO.Bmp
import NANO.Spec
import NANO.C.Lemmas
import NANO.C.Proofs.NiGeometryTail
import NANO.C.Proofs.NiBmpHeaderSpec

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000

open NANO NANO.C NANO.C.Proofs

namespace NANO


/-- If the geometry check rejects with a non-zero code, `bmpGeometryStage`
    throws it. -/
theorem bmpGeometryStage_eq_of_ne_zero (size : Nat) (d : List UInt8)
    (hG : bmpGeometryCode d ≠ 0) : bmpGeometryStage size d = .error (bmpGeometryCode d) := by
  by_cases h1 : NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1
  · have h3 : bmpGeometryCode d = 3 := by unfold bmpGeometryCode; rw [if_pos h1]
    unfold bmpGeometryStage
    simp only [if_pos h1, instMonad_bind_eq, throw_eq_error, bind_err_of_err]
    rw [h3]
  · by_cases hLT : NANO.toInt32 (rd32le d 22) < 0
    · by_cases h2 : NANO.toInt32 (rd32le d 22) = -2147483648
      · have h4 : bmpGeometryCode d = 4 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_pos h2]
        unfold bmpGeometryStage
        simp only [if_neg h1, if_pos hLT, if_pos h2, instMonad_bind_eq, throw_eq_error, bind_err_of_err]
        rw [h4]
      · by_cases h5 : rd32le d 30 ≠ 0
        · have h5' : bmpGeometryCode d = 5 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_neg h2, if_pos h5]
          unfold bmpGeometryStage
          simp only [if_neg h1, if_pos hLT, if_neg h2, if_pos h5, instMonad_bind_eq, throw_eq_error, bind_err_of_err]
          rw [h5']
        · by_cases h6 : rd16le d 28 ≠ 8 ∧ rd16le d 28 ≠ 24 ∧ rd16le d 28 ≠ 32
          · have h6' : bmpGeometryCode d = 6 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_neg h2, if_neg h5, if_pos h6]
            unfold bmpGeometryStage
            simp only [if_neg h1, if_pos hLT, if_neg h2, if_neg h5, if_pos h6, instMonad_bind_eq, throw_eq_error, bind_err_of_err]
            rw [h6']
          · exfalso
            have heq : bmpGeometryCode d = 0 := by
              simp [bmpGeometryCode, h1, hLT, h2, h5, h6]
            exact hG heq
    · by_cases h2 : NANO.toInt32 (rd32le d 22) = -2147483648
      · exfalso
        rw [h2] at hLT
        exact hLT (by decide)
      · by_cases h5 : rd32le d 30 ≠ 0
        · have h5' : bmpGeometryCode d = 5 := by unfold bmpGeometryCode; rw [if_neg h1, if_neg hLT, if_pos h5]
          unfold bmpGeometryStage
          simp only [if_neg h1, if_neg hLT, if_neg h2, if_pos h5, instMonad_bind_eq, throw_eq_error, bind_err_of_err]
          rw [h5']
        · by_cases h6 : rd16le d 28 ≠ 8 ∧ rd16le d 28 ≠ 24 ∧ rd16le d 28 ≠ 32
          · have h6' : bmpGeometryCode d = 6 := by unfold bmpGeometryCode; rw [if_neg h1, if_neg hLT, if_neg h5, if_pos h6]
            unfold bmpGeometryStage
            simp only [if_neg h1, if_neg hLT, if_neg h5, if_pos h6, instMonad_bind_eq, throw_eq_error, bind_err_of_err]
            rw [h6']
          · exfalso
            have heq : bmpGeometryCode d = 0 := by
              simp [bmpGeometryCode, h1, hLT, h2, h5, h6]
            exact hG heq

/-- If the geometry check passes, `bmpGeometryStage` succeeds. -/
theorem bmpGeometryStage_ok_of_zero (size : Nat) (d : List UInt8)
    (hG : bmpGeometryCode d = 0) :
    ∃ h, bmpGeometryStage size d = .ok h := by
  by_cases h1 : NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1
  · simp [bmpGeometryCode, h1] at hG
  · by_cases hLT : NANO.toInt32 (rd32le d 22) < 0
    · by_cases h2 : NANO.toInt32 (rd32le d 22) = -2147483648
      · have h4 : bmpGeometryCode d = 4 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_pos h2]
        simp [h4] at hG
      · by_cases h3' : rd32le d 30 ≠ 0
        · simp [bmpGeometryCode, h1, hLT, h2, h3'] at hG
        · by_cases h6 : rd16le d 28 ≠ 8 ∧ rd16le d 28 ≠ 24 ∧ rd16le d 28 ≠ 32
          · simp [bmpGeometryCode, h1, hLT, h2, h3', h6] at hG
          · refine ⟨((NANO.toInt32 (rd32le d 18)).toNat, (NANO.toInt32 (rd32le d 22)).natAbs, rd16le d 28,
              if rd16le d 28 = 32 then 4 else 3, if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0,
              rd32le d 46), ?_⟩
            simp [bmpGeometryStage, h1, hLT, h2, h3', h6]
            rfl
    · by_cases h3' : rd32le d 30 ≠ 0
      · simp [bmpGeometryCode, h1, hLT, h3'] at hG
      · by_cases h6 : rd16le d 28 ≠ 8 ∧ rd16le d 28 ≠ 24 ∧ rd16le d 28 ≠ 32
        · simp [bmpGeometryCode, h1, hLT, h3', h6] at hG
        · refine ⟨((NANO.toInt32 (rd32le d 18)).toNat, (NANO.toInt32 (rd32le d 22)).natAbs, rd16le d 28,
            if rd16le d 28 = 32 then 4 else 3, if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0,
            rd32le d 46), ?_⟩
          simp [bmpGeometryStage, h1, hLT, h3', h6]
          rfl



/-- `bmpGeometryCode` is always ≥ 0 and ≤ 6. -/
theorem bmpGeometryCode_bound (d : List UInt8) : bmpGeometryCode d ≤ 6 := by
  simp only [bmpGeometryCode]
  by_cases h1 : NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1
  · simp [h1]
  · by_cases hLT : NANO.toInt32 (rd32le d 22) < 0
    · by_cases h2 : NANO.toInt32 (rd32le d 22) = -2147483648
      · rw [if_neg h1, if_pos hLT, if_pos h2]; decide
      · by_cases h5 : rd32le d 30 ≠ 0
        · rw [if_neg h1, if_pos hLT, if_neg h2, if_pos h5]; decide
        · by_cases h6 : rd16le d 28 ≠ 8 ∧ rd16le d 28 ≠ 24 ∧ rd16le d 28 ≠ 32
          · rw [if_neg h1, if_pos hLT, if_neg h2, if_neg h5, if_pos h6]; decide
          · rw [if_neg h1, if_pos hLT, if_neg h2, if_neg h5, if_neg h6]; decide
    · by_cases h5 : rd32le d 30 ≠ 0
      · rw [if_neg h1, if_neg hLT, if_pos h5]; decide
      · by_cases h6 : rd16le d 28 ≠ 8 ∧ rd16le d 28 ≠ 24 ∧ rd16le d 28 ≠ 32
        · rw [if_neg h1, if_neg hLT, if_neg h5, if_pos h6]; decide
        · rw [if_neg h1, if_neg hLT, if_neg h5, if_neg h6]; decide



/-- The geometry-success width as a Nat is non-zero. -/
theorem width_pos_of_geomOk (d : List UInt8)
    (h1 : ¬ (NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1)) :
    1 ≤ (NANO.toInt32 (rd32le d 18)).toNat := by
  have hgt : 0 < NANO.toInt32 (rd32le d 18) := by
    by_cases hle : NANO.toInt32 (rd32le d 18) ≤ 0
    · exfalso; exact h1 (Or.inl hle)
    · omega
  have hsml : ¬ rd32le d 18 ≥ 2147483648 := by
    by_cases hge : rd32le d 18 ≥ 2147483648
    · have he : NANO.toInt32 (rd32le d 18) ≤ -1 := by
        unfold NANO.toInt32
        rw [if_pos (show rd32le d 18 ≥ 2 ^ 31 from by omega)]
        have hmax : rd32le d 18 ≤ 4294967295 := by have := rd32_lt d 18; omega
        omega
      omega
    · exact hge
  have hpos : (0 : Int) ≤ (rd32le d 18 : Int) := by omega
  have hw : NANO.toInt32 (rd32le d 18) = (rd32le d 18 : Int) := by
    unfold NANO.toInt32; rw [if_neg (by omega)]
  rw [hw]
  omega

/-- Spec-side fact: if the geometry check passes but `width × bitCount`
    overflows (`¬ sizeMulOK`), `bmpHeaderCode` is `7`. -/
theorem bmpHeaderCode_seven_of_geomOk (size : Nat) (d : List UInt8)
    (hSig : sigOk size d = true) (hLay : layoutOk size d = true)
    (hG : bmpGeometryCode d = 0)
    (hbad : ¬ rd16le d 28 ≤ sizeMax / rd32le d 18) :
    bmpHeaderCode size d = 7 := by
  have h1 : ¬ (NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1) := by
    by_cases h1' : NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1
    · have he : bmpGeometryCode d = 3 := by unfold bmpGeometryCode; rw [if_pos h1']
      rw [he] at hG; contradiction
    · exact h1'
  have hgt : 0 < NANO.toInt32 (rd32le d 18) := by
    by_cases hle : NANO.toInt32 (rd32le d 18) ≤ 0
    · exfalso; exact h1 (Or.inl hle)
    · omega
  have hsml : ¬ rd32le d 18 ≥ 2147483648 := by
    by_cases hge : rd32le d 18 ≥ 2147483648
    · have he : NANO.toInt32 (rd32le d 18) ≤ -1 := by
        unfold NANO.toInt32
        rw [if_pos (show rd32le d 18 ≥ 2 ^ 31 from by omega)]
        have hmax : rd32le d 18 ≤ 4294967295 := by have := rd32_lt d 18; omega
        omega
      omega
    · exact hge
  have hWpos : 1 ≤ (NANO.toInt32 (rd32le d 18)).toNat := width_pos_of_geomOk d h1
  have hwN : NANO.toInt32 (rd32le d 18) = (rd32le d 18 : Int) := by
    unfold NANO.toInt32; rw [if_neg (by omega)]
  have hWnat : (NANO.toInt32 (rd32le d 18)).toNat = rd32le d 18 := by
    rw [hwN]; rfl
  unfold bmpHeaderCode
  have hSigOk : bmpSigGate size d = .ok () := bmpSigGate_ok_of_sigOk size d hSig
  have hLayOk : bmpLayoutGate size d = .ok () := bmpLayoutGate_ok_of_layoutOk size d hLay
  -- Geometry: produce the tuple by inverting both LT branches
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
          unfold bmpHeader
          rw [hSigOk, bind_ok_of_ok]
          rw [hLayOk, bind_ok_of_ok]
          rw [hStage, bind_ok_of_ok]
          have hfail : bmpOutputCompose size d
              ((NANO.toInt32 (rd32le d 18)).toNat, (NANO.toInt32 (rd32le d 22)).natAbs, rd16le d 28,
               if rd16le d 28 = 32 then 4 else 3, 1, rd32le d 46) = .error 7 :=
            bmpOutputCompose_seven hWpos (by rw [hWnat]; exact hbad)
          rw [hfail]
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
        unfold bmpHeader
        rw [hSigOk, bind_ok_of_ok]
        rw [hLayOk, bind_ok_of_ok]
        rw [hStage, bind_ok_of_ok]
        have hfail : bmpOutputCompose size d
            ((NANO.toInt32 (rd32le d 18)).toNat, (NANO.toInt32 (rd32le d 22)).natAbs, rd16le d 28,
             if rd16le d 28 = 32 then 4 else 3, 0, rd32le d 46) = .error 7 :=
          bmpOutputCompose_seven hWpos (by rw [hWnat]; exact hbad)
        rw [hfail]



/-- If geometry passes, `bit_count` is one of 8/24/32. -/
theorem rd16le28_in_set_of_geomOk (d : List UInt8) (hG0 : bmpGeometryCode d = 0) :
    rd16le d 28 = 8 ∨ rd16le d 28 = 24 ∨ rd16le d 28 = 32 := by
  by_cases hDisj : (rd16le d 28 = 8 ∨ rd16le d 28 = 24 ∨ rd16le d 28 = 32)
  · exact hDisj
  · exfalso
    have h6 : rd16le d 28 ≠ 8 ∧ rd16le d 28 ≠ 24 ∧ rd16le d 28 ≠ 32 :=
      ⟨fun hcon => hDisj (Or.inl hcon), fun hcon => hDisj (Or.inr (Or.inl hcon)), fun hcon => hDisj (Or.inr (Or.inr hcon))⟩
    by_cases h1 : NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1
    · have he : bmpGeometryCode d = 3 := by unfold bmpGeometryCode; rw [if_pos h1]
      rw [he] at hG0; contradiction
    · by_cases hLT : NANO.toInt32 (rd32le d 22) < 0
      · by_cases h2 : NANO.toInt32 (rd32le d 22) = -2147483648
        · have he : bmpGeometryCode d = 4 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_pos h2]
          rw [he] at hG0; contradiction
        · by_cases h5 : rd32le d 30 ≠ 0
          · have he : bmpGeometryCode d = 5 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_neg h2, if_pos h5]
            rw [he] at hG0; contradiction
          · have he : bmpGeometryCode d = 6 := by unfold bmpGeometryCode; rw [if_neg h1, if_pos hLT, if_neg h2, if_neg h5, if_pos h6]
            rw [he] at hG0; contradiction
      · by_cases h5 : rd32le d 30 ≠ 0
        · have he : bmpGeometryCode d = 5 := by unfold bmpGeometryCode; rw [if_neg h1, if_neg hLT, if_pos h5]
          rw [he] at hG0; contradiction
        · have he : bmpGeometryCode d = 6 := by unfold bmpGeometryCode; rw [if_neg h1, if_neg hLT, if_neg h5, if_pos h6]
          rw [he] at hG0; contradiction

/-- If geometry passes, `width` is non-zero. -/
theorem rd32le18_ge1_of_geomOk (d : List UInt8) (hG0 : bmpGeometryCode d = 0) :
    1 ≤ rd32le d 18 := by
  by_cases h1 : NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1
  · have he : bmpGeometryCode d = 3 := by unfold bmpGeometryCode; rw [if_pos h1]
    rw [he] at hG0; contradiction
  · by_cases h : rd32le d 18 = 0
    · have he : NANO.toInt32 (rd32le d 18) = 0 := by rw [h]; rfl
      have hdisj : NANO.toInt32 (rd32le d 18) ≤ 0 := by rw [he]; decide
      have he3 : bmpGeometryCode d = 3 := by unfold bmpGeometryCode; rw [if_pos (Or.inl hdisj)]
      rw [he3] at hG0; contradiction
    · exact Nat.pos_iff_ne_zero.mpr h



/-- Height value bounded by 2147483648 (Int31 range incl. -2^31 edge). -/
theorem height_bound_of_geomOk (d : List UInt8) (hG0 : bmpGeometryCode d = 0) :
    (NANO.toInt32 (rd32le d 22)).natAbs ≤ 2147483648 := by
  unfold NANO.toInt32
  by_cases h : rd32le d 22 ≥ 2147483648
  · have hmax : rd32le d 22 ≤ 4294967295 := by have := rd32_lt d 22; omega
    rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

/-- RowStride bound: heights times widths stay below 2^64. -/
theorem rowStride_height_le_sizeMax (d : List UInt8) (hG0 : bmpGeometryCode d = 0) :
    ((((rd32le d 18 * rd16le d 28 + 31) / 32) * 4)) * (NANO.toInt32 (rd32le d 22)).natAbs ≤ sizeMax := by
  have hW : rd32le d 18 ≤ 2147483647 := by
    by_cases hge : rd32le d 18 ≥ 2147483648
    · have he : NANO.toInt32 (rd32le d 18) = (rd32le d 18 : Int) - 4294967296 := by
        simp [NANO.toInt32, hge]
      by_cases hle : NANO.toInt32 (rd32le d 18) ≤ 0
      · have hdisj : (NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1) := Or.inl hle
        have he3 : bmpGeometryCode d = 3 := by simp [bmpGeometryCode, hdisj]
        rw [he3] at hG0; contradiction
      · have he2 : NANO.toInt32 (rd32le d 18) = (rd32le d 18 : Int) - 4294967296 := by simp [NANO.toInt32, hge]
        have hmax : rd32le d 18 ≤ 4294967295 := by have := rd32_lt d 18; omega
        omega
    · omega
  have hb32 : rd16le d 28 ≤ 32 := by
    have hbs := rd16le28_in_set_of_geomOk d hG0
    cases hbs with
    | inl h8 => omega
    | inr h => cases h with
      | inl h24 => omega
      | inr h32 => omega
  have hwb : rd32le d 18 * rd16le d 28 ≤ 2147483647 * 32 := Nat.mul_le_mul hW hb32
  have hz : 2147483647 * 32 = 68719476704 := by decide
  rw [hz] at hwb
  have h32 : (rd32le d 18 * rd16le d 28 + 31) / 32 ≤ 2147483647 := by
    rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)]
    have : rd32le d 18 * rd16le d 28 + 31 ≤ 68719476704 + 31 := by omega
    have hLam : 2147483647 * 32 = 68719476704 := by decide
    omega
  have h6 : (((rd32le d 18 * rd16le d 28 + 31) / 32) * 4) ≤ 8589934588 := by
    omega
  have h3 : (NANO.toInt32 (rd32le d 22)).natAbs ≤ 2147483648 := height_bound_of_geomOk d hG0
  have hOSH : (((rd32le d 18 * rd16le d 28 + 31) / 32) * 4) * (NANO.toInt32 (rd32le d 22)).natAbs
      ≤ 8589934588 * 2147483648 := Nat.mul_le_mul h6 h3
  have hLit : 8589934588 * 2147483648 = 18446744065119617024 := by decide
  rw [hLit] at hOSH
  unfold sizeMax
  omega

end NANO

namespace NANO

/-- RowStride (spec) as a Nat. -/
def specRowStride (W b : Nat) : Nat := ((W * b + 31) / 32) * 4

/-- If `a * b ≤ sizeMax` then `sizeMulOK a b = true`. -/
theorem sizeMulOK_true_of_mulLE {a b : Nat} (hab : a * b ≤ sizeMax) :
    sizeMulOK a b = true := by
  unfold sizeMulOK
  by_cases ha : a = 0
  · rw [ha]; rfl
  · have hdiv : b ≤ sizeMax / a := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      have hcomm : a * b = b * a := Nat.mul_comm _ _
      omega
    rw [show (a == 0) = false from decide_eq_false ha]
    exact decide_eq_true_eq.mpr hdiv

theorem sizeMulOK_false_of_notFit {a b : Nat} (ha : a > 0)
    (hbad : ¬ b ≤ sizeMax / a) : sizeMulOK a b = false := by
  unfold sizeMulOK
  have h1 : (a == 0) = false := decide_eq_false (by omega)
  have h2 : decide (b ≤ sizeMax / a) = false := decide_eq_false_iff_not.mpr hbad
  simp [h1, h2]

end NANO

namespace NANO

/-- `bmpOutputCompose` returns `.error 9` when the truncation formula fires. -/
theorem bmpOutputCompose_nine (size : Nat) (d : List UInt8)
    (W H b c t cU : Nat) (hb : b ≤ 32) (hc : c ≤ 4) (hW : W ≤ 2147483647) (hH : H ≤ 2147483648)
    (hBad : (rd32le d 10 > sizeMax - ((W * b + 31) / 32) * 4 * H ∨ rd32le d 10 + ((W * b + 31) / 32) * 4 * H > size)) :
    bmpOutputCompose size d (W, H, b, c, t, cU) = .error 9 := by
  have hMul_wb : sizeMulOK W b = true := by
    apply sizeMulOK_true_of_mulLE
    have hwb : W * b ≤ 2147483647 * 32 := Nat.mul_le_mul hW hb
    have h32 : 2147483647 * 32 = 68719476704 := by decide
    rw [h32] at hwb
    unfold sizeMax
    omega
  have hMul_wc : sizeMulOK W c = true := by
    apply sizeMulOK_true_of_mulLE
    have hwb : W * c ≤ 2147483647 * 4 := Nat.mul_le_mul hW hc
    have h4 : 2147483647 * 4 = 8589934588 := by decide
    rw [h4] at hwb
    unfold sizeMax
    omega
  have hMul_wH : sizeMulOK (W * c) H = true := by
    apply sizeMulOK_true_of_mulLE
    have hwc : W * c ≤ 8589934588 := by
      have hwb : W ≤ 2147483647 := hW
      have hc0 : c ≤ 4 := hc
      have h4 : 2147483647 * 4 = 8589934588 := by decide
      have := Nat.mul_le_mul hW hc0
      omega
    have hOSH : (W * c) * H ≤ 8589934588 * 2147483648 := Nat.mul_le_mul hwc hH
    have hLit : 8589934588 * 2147483648 = 18446744065119617024 := by decide
    rw [hLit] at hOSH
    unfold sizeMax
    omega
  have hMul_row : sizeMulOK ((W * b + 31) / 32 * 4) H = true := by
    apply sizeMulOK_true_of_mulLE
    have hwb : W * b ≤ 2147483647 * 32 := Nat.mul_le_mul hW hb
    have h32 : 2147483647 * 32 = 68719476704 := by decide
    rw [h32] at hwb
    have hrow : (W * b + 31) / 32 * 4 ≤ 8589934588 := by
      omega
    have hOSH : ((W * b + 31) / 32 * 4) * H ≤ 8589934588 * 2147483648 := Nat.mul_le_mul hrow hH
    have hLit : 8589934588 * 2147483648 = 18446744065119617024 := by decide
    rw [hLit] at hOSH
    unfold sizeMax
    omega
  unfold bmpOutputCompose
  simp [hMul_wb, hMul_wc, hMul_wH, hMul_row]
  have hBad' : (sizeMax - (W * b + 31) / 32 * 4 * H < rd32le d 10 ∨ size < rd32le d 10 + (W * b + 31) / 32 * 4 * H) := by
    rcases hBad with h1 | h2
    · left; omega
    · right; omega
  rw [ite_eq_left hBad']
  rfl

end NANO

namespace NANO

/-- If geometry passes but the truncation check fires, `bmpHeaderCode = 9`. -/
theorem bmpHeaderCode_nine_of_trunc (size : Nat) (d : List UInt8)
    (hSig : sigOk size d = true) (hLay : layoutOk size d = true)
    (hG : bmpGeometryCode d = 0)
    (hBad : (rd32le d 10 > sizeMax - specRowStride (rd32le d 18) (rd16le d 28) * (NANO.toInt32 (rd32le d 22)).natAbs
           ∨ rd32le d 10 + specRowStride (rd32le d 18) (rd16le d 28) * (NANO.toInt32 (rd32le d 22)).natAbs > size)) :
    bmpHeaderCode size d = 9 := by
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
          have hNine := @bmpOutputCompose_nine size d
            (W := (NANO.toInt32 (rd32le d 18)).toNat)
            (H := (NANO.toInt32 (rd32le d 22)).natAbs)
            (b := rd16le d 28)
            (c := if rd16le d 28 = 32 then 4 else 3)
            (t := 1) (cU := rd32le d 46)
            hb32
            (channels_le_4 (rd16le d 28))
            hW' h3H
            (show (rd32le d 10 > sizeMax - ((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32 * 4 * (NANO.toInt32 (rd32le d 22)).natAbs ∨ rd32le d 10 + ((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32 * 4 * (NANO.toInt32 (rd32le d 22)).natAbs > size) from by
              have hBad' := hBad
              unfold specRowStride at hBad'
              rw [← hWnat] at hBad'
              exact hBad')
          rw [hNine]
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
        have hNine := @bmpOutputCompose_nine size d
          (W := (NANO.toInt32 (rd32le d 18)).toNat)
          (H := (NANO.toInt32 (rd32le d 22)).natAbs)
          (b := rd16le d 28)
          (c := if rd16le d 28 = 32 then 4 else 3)
          (t := 0) (cU := rd32le d 46)
          hb32
          (channels_le_4 (rd16le d 28))
          hW' h3H
          (show (rd32le d 10 > sizeMax - ((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32 * 4 * (NANO.toInt32 (rd32le d 22)).natAbs ∨ rd32le d 10 + ((NANO.toInt32 (rd32le d 18)).toNat * rd16le d 28 + 31) / 32 * 4 * (NANO.toInt32 (rd32le d 22)).natAbs > size) from by
            have hBad' := hBad
            unfold specRowStride at hBad'
            rw [← hWnat] at hBad'
            exact hBad')
        rw [hNine]


end NANO
