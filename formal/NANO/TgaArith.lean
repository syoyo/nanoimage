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

theorem u64_u64_cast (n : Nat) (h : n < 2 ^ 64) :
    evalCast ⟨64, false⟩ (.int ⟨64, false⟩ n) = .ok (.int ⟨64, false⟩ n) := by
  simp [evalCast, IntTy.modulus, Nat.mod_eq_of_lt h]

theorem Locals.upd_of_eq (l : Locals) (i : Nat) (v : Val) (h : l i = some v) :
    l.upd i v = l := by
  funext j
  rw [Locals.upd]
  by_cases hj : j = i
  · rw [if_pos hj, hj]; exact h.symm
  · rw [if_neg hj]

theorem bin_u32_gt (n k : Nat) : evalBin .gt (some ⟨32, false⟩) (.int ⟨32, false⟩ n) (.int ⟨32, false⟩ k)
    = .ok (boolVal (decide (n > k))) := rfl

/-- Loading from a pointer block depends only on that block's contents. -/
theorem load_ptr_congr (m m' : Mem) (b o : Nat) (ty : Ty) (h : m b = m' b) :
    load m ty (.ptr b o) = load m' ty (.ptr b o) := by
  simp only [load]
  rw [show readBytes m b o ty.size = readBytes m' b o ty.size from by
    simp only [readBytes]; rw [h]]

end NANO.C.Proofs
