/-
  Standalone arithmetic facts used by the BMP header proofs. Kept separate so
  the heavyweight `omega`/`simp` calls do not run inside the kernel-critical
  path of the composed header theorem.
-/
import NANO.Bmp
import NANO.Spec
import NANO.C.Semantics
import NANO.C.Lemmas
import NANO.C.Gen
import NANO.C.Proofs.Core

set_option maxRecDepth 8000000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

open NANO NANO.C

namespace NANO.C.Proofs

theorem heightU_of_neg {n : Nat} (h1 : n ≥ 2147483648) (h2 : n ≤ 4294967295) :
    Int.natAbs ((n : Int) - 4294967296) = 4294967296 - n := by
  have h3 : (n : Int) - 4294967296 ≤ 0 := by omega
  rw [Int.eq_neg_natAbs_of_nonpos h3]
  omega

theorem toInt_ge_of_ge {n : Nat} (h : n ≥ 2147483648) :
    IntTy.toInt ⟨32, true⟩ n = (n : Int) - 4294967296 := by
  simp [IntTy.toInt, IntTy.modulus, h]

theorem wrap_of_pos {n : Nat} (h1 : n ≥ 2147483648) (h2 : n ≤ 4294967295) :
    IntTy.wrap ⟨32, true⟩ ((4294967296 : Int) - (n : Int)) = 4294967296 - n := by
  have hm : (⟨32, true⟩ : IntTy).modulus = 4294967296 := rfl
  show (((4294967296 : Int) - (n : Int)) % ((⟨32, true⟩ : IntTy).modulus : Int)).toNat =
    4294967296 - n
  rw [hm, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem wrap_neg_eq_neg {n : Nat} (h1 : n ≥ 2147483648) (h2 : n ≤ 4294967295) :
    IntTy.wrap ⟨32, true⟩ (- IntTy.toInt ⟨32, true⟩ n) =
      Int.natAbs (IntTy.toInt ⟨32, true⟩ n) := by
  rw [toInt_ge_of_ge h1, heightU_of_neg h1 h2]
  rw [show - (↑n - 4294967296) = (4294967296 : Int) - (n : Int) by omega]
  rw [wrap_of_pos h1 h2]

end NANO.C.Proofs
