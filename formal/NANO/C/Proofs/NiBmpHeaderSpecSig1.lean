/-
  Spec-side fact: when the signature check passes, the signature guard of
  `bmpHeader` is false.
-/
import NANO.Bmp
import NANO.Spec

set_option maxRecDepth 8000000
set_option maxHeartbeats 200000

namespace NANO

theorem sigOk_guard_false_of_sigOk (size : Nat) (d : List UInt8)
    (hSig : sigOk size d = true) :
    ¬ (size < 54 ∨ byteAt d 0 ≠ 66 ∨ byteAt d 1 ≠ 77) := by
  intro hIf
  cases hIf with
  | inl h1b =>
    have hne : ¬ 54 ≤ size := by omega
    have hElse : sigOk size d = false := by simp [sigOk, hne]
    rw [hElse] at hSig; exact Bool.noConfusion hSig
  | inr h2 =>
    cases h2 with
    | inl h2 =>
      have hElse : sigOk size d = false := by simp [sigOk, h2]
      rw [hElse] at hSig; exact Bool.noConfusion hSig
    | inr h1' =>
      have hElse : sigOk size d = false := by simp [sigOk, h1']
      rw [hElse] at hSig; exact Bool.noConfusion hSig

end NANO
