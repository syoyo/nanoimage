/-
  `tgaHeader`/`tgaHeaderCode` reductions per validation stage.
-/
import NANO.C.Gen
import NANO.Spec
import NANO.Tga

set_option linter.unusedVariables false
set_option maxRecDepth 8000000

namespace NANO.C.Proofs
open NANO NANO.C

theorem tgaHeader_lt18 (d : List UInt8) (size : Nat) (h : size < 18) :
    tgaHeader size d = .error 1 := by
  unfold tgaHeader; rw [if_pos h]; rfl

theorem tgaHeader_dims (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : rd16le d 12 = 0 ∨ rd16le d 14 = 0) : tgaHeader size d = .error 2 := by
  unfold tgaHeader
  simp only [if_neg hsz, if_pos hdim, Except.bind, Bind.bind, pure, Except.pure, id]
  rfl

theorem tgaHeader_cmap (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : ¬ (rd16le d 12 = 0 ∨ rd16le d 14 = 0)) (hcm : byteAt d 1 ≠ 0) :
    tgaHeader size d = .error 3 := by
  unfold tgaHeader
  simp only [if_neg hsz, if_neg hdim, if_pos hcm, Except.bind, Bind.bind, pure, Except.pure, id]
  rfl

theorem tgaHeader_badtype (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : ¬ (rd16le d 12 = 0 ∨ rd16le d 14 = 0)) (hcm : byteAt d 1 = 0)
    (hb : ¬ byteAt d 2 = 2 ∧ ¬ byteAt d 2 = 3 ∧ ¬ byteAt d 2 = 10 ∧ ¬ byteAt d 2 = 11) :
    tgaHeader size d = .error 4 := by
  unfold tgaHeader
  simp only [if_neg hsz, if_neg hdim, if_neg (by simp [hcm] : ¬ (byteAt d 1 ≠ 0)),
    if_pos hb, Except.bind, Bind.bind, pure, Except.pure, id]
  rfl

theorem tgaCode_lt18 (d : List UInt8) (size : Nat) (h : size < 18) : tgaHeaderCode size d = 1 := by
  unfold tgaHeaderCode; rw [tgaHeader_lt18 d size h]
theorem tgaCode_dims (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : rd16le d 12 = 0 ∨ rd16le d 14 = 0) : tgaHeaderCode size d = 2 := by
  unfold tgaHeaderCode; rw [tgaHeader_dims d size hsz hdim]
theorem tgaCode_cmap (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : ¬ (rd16le d 12 = 0 ∨ rd16le d 14 = 0)) (hcm : byteAt d 1 ≠ 0) :
    tgaHeaderCode size d = 3 := by
  unfold tgaHeaderCode; rw [tgaHeader_cmap d size hsz hdim hcm]
theorem tgaCode_badtype (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : ¬ (rd16le d 12 = 0 ∨ rd16le d 14 = 0)) (hcm : byteAt d 1 = 0)
    (hb : ¬ byteAt d 2 = 2 ∧ ¬ byteAt d 2 = 3 ∧ ¬ byteAt d 2 = 10 ∧ ¬ byteAt d 2 = 11) :
    tgaHeaderCode size d = 4 := by
  unfold tgaHeaderCode; rw [tgaHeader_badtype d size hsz hdim hcm hb]

end NANO.C.Proofs
