/-
  Spec-side short facts for the `ni_bmp_header` rejects: signature failure
  short-circuits to `1`.
-/
import NANO.Bmp
import NANO.Spec
import NANO.C.Proofs.NiBmpHeaderSpecSig1

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000

namespace NANO

/-- `bind` of an error is the error. -/
theorem bind_error_of_error {α β : Type} (e : Nat) (f : α → Except Nat β) :
    Except.bind (Except.error e : Except Nat α) f = Except.error e := by
  rfl

/-- `bmpSigGate` throws `1` iff `sigOk` is false. -/
theorem bmpSigGate_one_of_not_sigOk (size : Nat) (d : List UInt8)
    (h : sigOk size d = false) : bmpSigGate size d = .error 1 := by
  by_cases h54_ : 54 ≤ size
  · by_cases h0_ : byteAt d 0 = 66
    · by_cases h1_ : byteAt d 1 = 77
      · simp [sigOk, h54_, h0_, h1_] at h
      · have hg : size < 54 ∨ byteAt d 0 ≠ 66 ∨ byteAt d 1 ≠ 77 :=
          Or.inr (Or.inr h1_)
        unfold bmpSigGate; rw [if_pos hg]; rfl
    · have hg : size < 54 ∨ byteAt d 0 ≠ 66 ∨ byteAt d 1 ≠ 77 :=
        Or.inr (Or.inl h0_)
      unfold bmpSigGate; rw [if_pos hg]; rfl
  · have hg : size < 54 ∨ byteAt d 0 ≠ 66 ∨ byteAt d 1 ≠ 77 :=
      Or.inl (by omega)
    unfold bmpSigGate; rw [if_pos hg]; rfl

/-- If the signature check fails, `bmpHeader` throws `1` first. -/
theorem bmpHeaderCode_one_of_not_sigOk (size : Nat) (d : List UInt8)
    (h : sigOk size d = false) : bmpHeaderCode size d = 1 := by
  unfold bmpHeaderCode
  have hSig : bmpSigGate size d = .error 1 := bmpSigGate_one_of_not_sigOk size d h
  unfold bmpHeader
  rw [hSig]
  rfl

end NANO

namespace NANO

/-- The monad bind of the Except instance is `Except.bind`. -/
theorem instMonad_bind_eq {α β : Type} (m : Except Nat α) (f : α → Except Nat β) :
    @Bind.bind (Except Nat) (@Monad.toBind (Except Nat) (@Except.instMonad Nat)) α β m f =
    Except.bind m f := rfl

/-- `throw e` reduces to `Except.error e`. -/
theorem throw_eq_error {α : Type} (e : Nat) : (throw e : Except Nat α) = Except.error e := rfl

/-- `bind` of an error is the error. -/
@[simp] theorem bind_err_of_err {α β : Type} (e : Nat) (f : α → Except Nat β) :
    Except.bind (Except.error e : Except Nat α) f = Except.error e := by
  unfold Except.bind
  rfl

/-- `bind` of `ok` evaluates the continuation (via the `Except` instance). -/
theorem bind_ok_of_ok {α β : Type} (v : α) (f : α → Except Nat β) :
    Bind.bind (Except.ok v : Except Nat α) f = f v := by
  rfl

/-- `bind` of an error is the error (via the `Except` instance). -/
theorem bind_error_of_error_l {α β : Type} (e : Nat) (f : α → Except Nat β) :
    Bind.bind (Except.error e : Except Nat α) f = Except.error e := by
  rfl

/-- `bmpLayoutGate` throws `2` iff `layoutOk` is false. -/
theorem bmpLayoutGate_two_of_not_layoutOk (size : Nat) (d : List UInt8)
    (h : layoutOk size d = false) : bmpLayoutGate size d = .error 2 := by
  by_cases d1 : rd32le d 14 < 40
  · have c1 : rd32le d 14 < 40 := d1
    unfold bmpLayoutGate
    rw [if_pos (Or.inl c1)]; rfl
  · by_cases d2 : 14 + rd32le d 14 > size
    · have c2 : 14 + rd32le d 14 > size := d2
      unfold bmpLayoutGate
      rw [if_pos (Or.inr (Or.inl c2))]; rfl
    · by_cases d3 : rd32le d 10 < 14 + rd32le d 14
      · have c3 : rd32le d 10 < 14 + rd32le d 14 := d3
        unfold bmpLayoutGate
        rw [if_pos (Or.inr (Or.inr (Or.inl c3)))]; rfl
      · by_cases d4 : rd32le d 10 > size
        · have c4 : rd32le d 10 > size := d4
          unfold bmpLayoutGate
          rw [if_pos (Or.inr (Or.inr (Or.inr c4)))]; rfl
        · exfalso
          have hLTrue : layoutOk size d = true := by
            have hAB : decide (rd32le d 14 < 40) = false :=
              decide_eq_false_iff_not.mpr d1
            have hAC : decide (14 + rd32le d 14 > size) = false :=
              decide_eq_false_iff_not.mpr d2
            have hAD : decide (rd32le d 10 < 14 + rd32le d 14) = false :=
              decide_eq_false_iff_not.mpr d3
            have hAE : decide (rd32le d 10 > size) = false :=
              decide_eq_false_iff_not.mpr d4
            simp [layoutOk, hAB, hAC, hAD, hAE]
          rw [hLTrue] at h; exact Bool.noConfusion h

/-- If `sigOk` passes but `layoutOk` fails, `bmpHeader` throws `2`. -/
theorem bmpHeaderCode_two_of_not_layoutOk (size : Nat) (d : List UInt8)
    (hSig : sigOk size d = true) (h : layoutOk size d = false) :
    bmpHeaderCode size d = 2 := by
  unfold bmpHeaderCode
  have hSigOk : bmpSigGate size d = .ok () := by
    have hA : 54 ≤ size := by
      by_cases h54_ : 54 ≤ size
      · exact h54_
      · have hElse : sigOk size d = false := by simp [sigOk, h54_]
        rw [hElse] at hSig; exact Bool.noConfusion hSig
    have hB : byteAt d 0 = 66 := by
      by_cases h0_ : byteAt d 0 = 66
      · exact h0_
      · have hElse : sigOk size d = false := by simp [sigOk, h0_]
        rw [hElse] at hSig; exact Bool.noConfusion hSig
    have hC : byteAt d 1 = 77 := by
      by_cases h1_ : byteAt d 1 = 77
      · exact h1_
      · have hElse : sigOk size d = false := by simp [sigOk, h1_]
        rw [hElse] at hSig; exact Bool.noConfusion hSig
    have hg : ¬ (size < 54 ∨ byteAt d 0 ≠ 66 ∨ byteAt d 1 ≠ 77) := by
      intro hIf
      rcases hIf with h1 | h2 | h1'
      · exact absurd h1 (by omega)
      · exact h2 hB
      · exact h1' hC
    unfold bmpSigGate; rw [if_neg hg]; rfl
  have hLay : bmpLayoutGate size d = .error 2 := bmpLayoutGate_two_of_not_layoutOk size d h
  unfold bmpHeader
  rw [hSigOk]
  simp only [bind_ok_of_ok]
  rw [hLay]
  simp only [bind_error_of_error_l]

end NANO

namespace NANO

/-- If `sigOk` is true, `bmpSigGate` succeeds. -/
theorem bmpSigGate_ok_of_sigOk (size : Nat) (d : List UInt8) (hSig : sigOk size d = true) :
    bmpSigGate size d = .ok () := by
  have hg : ¬ (size < 54 ∨ byteAt d 0 ≠ 66 ∨ byteAt d 1 ≠ 77) :=
    sigOk_guard_false_of_sigOk size d hSig
  unfold bmpSigGate; rw [if_neg hg]; rfl

/-- If `layoutOk` is true, `bmpLayoutGate` succeeds. -/
theorem bmpLayoutGate_ok_of_layoutOk (size : Nat) (d : List UInt8) (hLay : layoutOk size d = true) :
    bmpLayoutGate size d = .ok () := by
  by_cases d1 : rd32le d 14 < 40
  · have hElse : layoutOk size d = false := by simp [layoutOk, d1]
    rw [hElse] at hLay; exact Bool.noConfusion hLay
  · by_cases d2 : 14 + rd32le d 14 > size
    · have hElse : layoutOk size d = false := by simp [layoutOk, d2]
      rw [hElse] at hLay; exact Bool.noConfusion hLay
    · by_cases d3 : rd32le d 10 < 14 + rd32le d 14
      · have hElse : layoutOk size d = false := by simp [layoutOk, d3]
        rw [hElse] at hLay; exact Bool.noConfusion hLay
      · by_cases d4 : rd32le d 10 > size
        · have hElse : layoutOk size d = false := by simp [layoutOk, d4]
          rw [hElse] at hLay; exact Bool.noConfusion hLay
        · have hg : ¬ (rd32le d 14 < 40 ∨ 14 + rd32le d 14 > size ∨
              rd32le d 10 < 14 + rd32le d 14 ∨ rd32le d 10 > size) := by
            intro hIf
            rcases hIf with h | h | h | h
            · exact d1 h
            · exact d2 h
            · exact d3 h
            · exact d4 h
          unfold bmpLayoutGate; rw [if_neg hg]; rfl

end NANO

namespace NANO

/-- Spec-side fact: `sizeMulOK a b = false` when `a ≥ 1` and `b > sizeMax / a`. -/
theorem sizeMulOK_false_of_bad {w b : Nat} (hw : w ≥ 1)
    (hbad : ¬ b ≤ sizeMax / w) : sizeMulOK w b = false := by
  unfold sizeMulOK
  have h1 : (w == 0) = false := decide_eq_false (by omega)
  have h2 : decide (b ≤ sizeMax / w) = false := decide_eq_false_iff_not.mpr hbad
  rw [h1, h2]; rfl

/-- Spec-side fact: `bmpOutputCompose` throws `7` when width × bitCount overflows. -/
theorem bmpOutputCompose_seven {size : Nat} {d : List UInt8}
    {width height bitCount channels topDown colorsUsed : Nat}
    (hw : width ≥ 1) (hbad : ¬ bitCount ≤ sizeMax / width) :
    bmpOutputCompose size d (width, height, bitCount, channels, topDown, colorsUsed) = .error 7 := by
  have hMul : sizeMulOK width bitCount = false := sizeMulOK_false_of_bad hw hbad
  have hnot : (!sizeMulOK width bitCount) = true := by rw [hMul]; rfl
  unfold bmpOutputCompose
  show (if !sizeMulOK width bitCount then (Except.error 7) else _) = .error 7
  rw [if_pos hnot]

end NANO

namespace NANO

theorem instPure_eq {α : Type} (a : α) :
    (pure a : Except Nat α) = .ok a := rfl

end NANO
