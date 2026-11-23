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

namespace NANO.C.Proofs
open NANO NANO.C

/-- All gates pass with type∉{3,11}, depth 24 (channels 3) ⇒ `.ok`. -/
theorem tgaHeader_ok3 (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : ¬ (rd16le d 12 = 0 ∨ rd16le d 14 = 0)) (hcm : byteAt d 1 = 0)
    (hvalid : ¬ (¬ byteAt d 2 = 2 ∧ ¬ byteAt d 2 = 3 ∧ ¬ byteAt d 2 = 10 ∧ ¬ byteAt d 2 = 11))
    (hchan : ¬ (byteAt d 2 = 3 ∨ byteAt d 2 = 11)) (hpd : byteAt d 16 = 24)
    (hid : ¬ 18 + byteAt d 0 > size)
    (hm1 : sizeMulOK (rd16le d 12) (rd16le d 14) = true)
    (hm2 : sizeMulOK (rd16le d 12 * rd16le d 14) 3 = true) :
    tgaHeader size d = .ok
      { outputSize := rd16le d 12 * rd16le d 14 * 3, dataOffset := 18 + byteAt d 0,
        width := rd16le d 12, height := rd16le d 14, channels := 3,
        rle := if byteAt d 2 = 10 ∨ byteAt d 2 = 11 then 1 else 0,
        topOrigin := if byteAt d 17 &&& 0x20 ≠ 0 then 1 else 0,
        rightOrigin := if byteAt d 17 &&& 0x10 ≠ 0 then 1 else 0 } := by
  unfold tgaHeader
  simp only [if_neg hsz, if_neg hdim, if_neg (by simp [hcm] : ¬ (byteAt d 1 ≠ 0)),
    if_neg hvalid, if_neg hchan, if_pos hpd, if_neg hid,
    if_neg (by rw [hm1]; decide : ¬ ((! sizeMulOK (rd16le d 12) (rd16le d 14)) = true)),
    if_neg (by rw [hm2]; decide : ¬ ((! sizeMulOK (rd16le d 12 * rd16le d 14) 3) = true)),
    Except.bind, Bind.bind, pure, Except.pure, id]

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem tgaHeader_ok1 (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : ¬ (rd16le d 12 = 0 ∨ rd16le d 14 = 0)) (hcm : byteAt d 1 = 0)
    (hvalid : ¬ (¬ byteAt d 2 = 2 ∧ ¬ byteAt d 2 = 3 ∧ ¬ byteAt d 2 = 10 ∧ ¬ byteAt d 2 = 11))
    (hchan : byteAt d 2 = 3 ∨ byteAt d 2 = 11) (hpd : byteAt d 16 = 8)
    (hid : ¬ 18 + byteAt d 0 > size)
    (hm1 : sizeMulOK (rd16le d 12) (rd16le d 14) = true)
    (hm2 : sizeMulOK (rd16le d 12 * rd16le d 14) 1 = true) :
    tgaHeader size d = .ok
      { outputSize := rd16le d 12 * rd16le d 14 * 1, dataOffset := 18 + byteAt d 0,
        width := rd16le d 12, height := rd16le d 14, channels := 1,
        rle := if byteAt d 2 = 10 ∨ byteAt d 2 = 11 then 1 else 0,
        topOrigin := if byteAt d 17 &&& 0x20 ≠ 0 then 1 else 0,
        rightOrigin := if byteAt d 17 &&& 0x10 ≠ 0 then 1 else 0 } := by
  unfold tgaHeader
  simp only [if_neg hsz, if_neg hdim, if_neg (by simp [hcm] : ¬ (byteAt d 1 ≠ 0)),
    if_neg hvalid, if_pos hchan, if_neg (by simp [hpd] : ¬ (byteAt d 16 ≠ 8)),
    if_neg hid,
    if_neg (by rw [hm1]; decide : ¬ ((! sizeMulOK (rd16le d 12) (rd16le d 14)) = true)),
    if_neg (by rw [hm2]; decide : ¬ ((! sizeMulOK (rd16le d 12 * rd16le d 14) 1) = true)),
    Except.bind, Bind.bind, pure, Except.pure, id]

theorem tgaHeader_ok4 (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : ¬ (rd16le d 12 = 0 ∨ rd16le d 14 = 0)) (hcm : byteAt d 1 = 0)
    (hvalid : ¬ (¬ byteAt d 2 = 2 ∧ ¬ byteAt d 2 = 3 ∧ ¬ byteAt d 2 = 10 ∧ ¬ byteAt d 2 = 11))
    (hchan : ¬ (byteAt d 2 = 3 ∨ byteAt d 2 = 11)) (hpd : byteAt d 16 = 32)
    (hid : ¬ 18 + byteAt d 0 > size)
    (hm1 : sizeMulOK (rd16le d 12) (rd16le d 14) = true)
    (hm2 : sizeMulOK (rd16le d 12 * rd16le d 14) 4 = true) :
    tgaHeader size d = .ok
      { outputSize := rd16le d 12 * rd16le d 14 * 4, dataOffset := 18 + byteAt d 0,
        width := rd16le d 12, height := rd16le d 14, channels := 4,
        rle := if byteAt d 2 = 10 ∨ byteAt d 2 = 11 then 1 else 0,
        topOrigin := if byteAt d 17 &&& 0x20 ≠ 0 then 1 else 0,
        rightOrigin := if byteAt d 17 &&& 0x10 ≠ 0 then 1 else 0 } := by
  unfold tgaHeader
  simp only [if_neg hsz, if_neg hdim, if_neg (by simp [hcm] : ¬ (byteAt d 1 ≠ 0)),
    if_neg hvalid, if_neg hchan,
    if_neg (by simp [hpd] : ¬ (byteAt d 16 = 24)),
    if_pos hpd, if_neg hid,
    if_neg (by rw [hm1]; decide : ¬ ((! sizeMulOK (rd16le d 12) (rd16le d 14)) = true)),
    if_neg (by rw [hm2]; decide : ¬ ((! sizeMulOK (rd16le d 12 * rd16le d 14) 4) = true)),
    Except.bind, Bind.bind, pure, Except.pure, id]

theorem tgaCode_ok1 (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : ¬ (rd16le d 12 = 0 ∨ rd16le d 14 = 0)) (hcm : byteAt d 1 = 0)
    (hvalid : ¬ (¬ byteAt d 2 = 2 ∧ ¬ byteAt d 2 = 3 ∧ ¬ byteAt d 2 = 10 ∧ ¬ byteAt d 2 = 11))
    (hchan : byteAt d 2 = 3 ∨ byteAt d 2 = 11) (hpd : byteAt d 16 = 8)
    (hid : ¬ 18 + byteAt d 0 > size)
    (hm1 : sizeMulOK (rd16le d 12) (rd16le d 14) = true)
    (hm2 : sizeMulOK (rd16le d 12 * rd16le d 14) 1 = true) : tgaHeaderCode size d = 0 := by
  unfold tgaHeaderCode; rw [tgaHeader_ok1 d size hsz hdim hcm hvalid hchan hpd hid hm1 hm2]
theorem tgaCode_ok3 (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : ¬ (rd16le d 12 = 0 ∨ rd16le d 14 = 0)) (hcm : byteAt d 1 = 0)
    (hvalid : ¬ (¬ byteAt d 2 = 2 ∧ ¬ byteAt d 2 = 3 ∧ ¬ byteAt d 2 = 10 ∧ ¬ byteAt d 2 = 11))
    (hchan : ¬ (byteAt d 2 = 3 ∨ byteAt d 2 = 11)) (hpd : byteAt d 16 = 24)
    (hid : ¬ 18 + byteAt d 0 > size)
    (hm1 : sizeMulOK (rd16le d 12) (rd16le d 14) = true)
    (hm2 : sizeMulOK (rd16le d 12 * rd16le d 14) 3 = true) : tgaHeaderCode size d = 0 := by
  unfold tgaHeaderCode; rw [tgaHeader_ok3 d size hsz hdim hcm hvalid hchan hpd hid hm1 hm2]
theorem tgaCode_ok4 (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : ¬ (rd16le d 12 = 0 ∨ rd16le d 14 = 0)) (hcm : byteAt d 1 = 0)
    (hvalid : ¬ (¬ byteAt d 2 = 2 ∧ ¬ byteAt d 2 = 3 ∧ ¬ byteAt d 2 = 10 ∧ ¬ byteAt d 2 = 11))
    (hchan : ¬ (byteAt d 2 = 3 ∨ byteAt d 2 = 11)) (hpd : byteAt d 16 = 32)
    (hid : ¬ 18 + byteAt d 0 > size)
    (hm1 : sizeMulOK (rd16le d 12) (rd16le d 14) = true)
    (hm2 : sizeMulOK (rd16le d 12 * rd16le d 14) 4 = true) : tgaHeaderCode size d = 0 := by
  unfold tgaHeaderCode; rw [tgaHeader_ok4 d size hsz hdim hcm hvalid hchan hpd hid hm1 hm2]

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem tgaHeader_depth1 (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : ¬ (rd16le d 12 = 0 ∨ rd16le d 14 = 0)) (hcm : byteAt d 1 = 0)
    (hvalid : ¬ (¬ byteAt d 2 = 2 ∧ ¬ byteAt d 2 = 3 ∧ ¬ byteAt d 2 = 10 ∧ ¬ byteAt d 2 = 11))
    (hchan : byteAt d 2 = 3 ∨ byteAt d 2 = 11) (hpd : byteAt d 16 ≠ 8) :
    tgaHeader size d = .error 5 := by
  unfold tgaHeader
  simp only [if_neg hsz, if_neg hdim, if_neg (by simp [hcm] : ¬ (byteAt d 1 ≠ 0)),
    if_neg hvalid, if_pos hchan, if_pos hpd, Except.bind, Bind.bind, pure, Except.pure, id]
  rfl

theorem tgaHeader_depth2 (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : ¬ (rd16le d 12 = 0 ∨ rd16le d 14 = 0)) (hcm : byteAt d 1 = 0)
    (hvalid : ¬ (¬ byteAt d 2 = 2 ∧ ¬ byteAt d 2 = 3 ∧ ¬ byteAt d 2 = 10 ∧ ¬ byteAt d 2 = 11))
    (hchan : ¬ (byteAt d 2 = 3 ∨ byteAt d 2 = 11))
    (hpd24 : byteAt d 16 ≠ 24) (hpd32 : byteAt d 16 ≠ 32) :
    tgaHeader size d = .error 5 := by
  unfold tgaHeader
  simp only [if_neg hsz, if_neg hdim, if_neg (by simp [hcm] : ¬ (byteAt d 1 ≠ 0)),
    if_neg hvalid, if_neg hchan,
    if_neg (by simp [hpd24] : ¬ (byteAt d 16 = 24)),
    if_neg (by simp [hpd32] : ¬ (byteAt d 16 = 32)),
    Except.bind, Bind.bind, pure, Except.pure, id]
  rfl

theorem tgaCode_depth1 (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : ¬ (rd16le d 12 = 0 ∨ rd16le d 14 = 0)) (hcm : byteAt d 1 = 0)
    (hvalid : ¬ (¬ byteAt d 2 = 2 ∧ ¬ byteAt d 2 = 3 ∧ ¬ byteAt d 2 = 10 ∧ ¬ byteAt d 2 = 11))
    (hchan : byteAt d 2 = 3 ∨ byteAt d 2 = 11) (hpd : byteAt d 16 ≠ 8) :
    tgaHeaderCode size d = 5 := by
  unfold tgaHeaderCode; rw [tgaHeader_depth1 d size hsz hdim hcm hvalid hchan hpd]
theorem tgaCode_depth2 (d : List UInt8) (size : Nat) (hsz : ¬ size < 18)
    (hdim : ¬ (rd16le d 12 = 0 ∨ rd16le d 14 = 0)) (hcm : byteAt d 1 = 0)
    (hvalid : ¬ (¬ byteAt d 2 = 2 ∧ ¬ byteAt d 2 = 3 ∧ ¬ byteAt d 2 = 10 ∧ ¬ byteAt d 2 = 11))
    (hchan : ¬ (byteAt d 2 = 3 ∨ byteAt d 2 = 11))
    (hpd24 : byteAt d 16 ≠ 24) (hpd32 : byteAt d 16 ≠ 32) :
    tgaHeaderCode size d = 5 := by
  unfold tgaHeaderCode; rw [tgaHeader_depth2 d size hsz hdim hcm hvalid hchan hpd24 hpd32]

end NANO.C.Proofs
