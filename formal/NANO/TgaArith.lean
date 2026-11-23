/-
  Extra integer-arithmetic evaluation lemmas for the TGA decode loop.
-/
import NANO.C.Lemmas

namespace NANO.C.Proofs
open NANO NANO.C

theorem bin_u64_mod (n k : Nat) (hk : k ≠ 0) (hn : n < 2 ^ 64) :
    evalBin .mod (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ k)
      = .ok (.int ⟨64, false⟩ (n % k)) := by
  simp [evalBin, evalBinInt, binInt, intOf, IntTy.modulus, isPtr, hk, hn]

theorem bin_u32_sub (n k : Nat) (h : k ≤ n) :
    evalBin .sub (some ⟨32, false⟩) (.int ⟨32, false⟩ n) (.int ⟨32, false⟩ k)
      = .ok (.int ⟨32, false⟩ (n - k)) := by
  simp [evalBin, evalBinInt, binInt, intOf, IntTy.modulus, isPtr, h]

theorem bin_u32_add' (n k : Nat) (h : n + k < 2 ^ 32) :
    evalBin .add (some ⟨32, false⟩) (.int ⟨32, false⟩ n) (.int ⟨32, false⟩ k)
      = .ok (.int ⟨32, false⟩ (n + k)) := by
  simp [evalBin, evalBinInt, binInt, intOf, IntTy.modulus, isPtr, h, Nat.mod_eq_of_lt h]

end NANO.C.Proofs
