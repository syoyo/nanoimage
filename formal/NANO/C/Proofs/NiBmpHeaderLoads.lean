/-
  Load-field helpers for ni_bmp_header: generic `load` on a memory block,
  for blocks of exactly 48 bytes, whose content is given by
  `bmpTailBlock obl …` (writes at offsets 24/28/40/42/43).
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Lemmas
import NANO.Spec
import NANO.Bmp
import NANO.C.Proofs.Core
import NANO.C.Proofs.NiGeometryTail

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 400000

namespace NANO.C.Proofs
open NANO NANO.C

/-- `readBytes m b o n` with a pre-proven slice. -/
theorem readBytes_drop_ok (m : Mem) (b : Nat) (blk : List UInt8) (hm : m b = some blk)
    (len : blk.length = 48) (o : Nat) (ho : o ≤ 48) (n : Nat) (hn : o + n ≤ 48) :
    readBytes m b o n = .ok ((blk.drop o).take n) := by
  simp only [readBytes, hm]
  rw [if_pos (show o + n ≤ blk.length from by rw [len]; exact hn)]

/-- Load u32 at `.ptr 3 off` from a 48-byte block. -/
theorem load_u32_field_of_geom (m : Mem) (o : Nat) (blk : List UInt8) (hm : m 3 = some blk)
    (len : blk.length = 48) (ho : o ≤ 44)
    (nval : Nat) (slice_eq : (blk.drop o).take 4 = encodeLE 4 nval)
    (hv : nval < 4294967296) :
    load m (.int ⟨32, false⟩) (.ptr 3 o) = .ok (Val.int ⟨32, false⟩ nval) := by
  simp only [load, Ty.size]
  simp only [readBytes]
  rw [hm]
  have hsz : (Ty.int { width := 32, signed := false }).size = 4 := rfl
  have hBytes : IntTy.bytes { width := 32, signed := false } = 4 := rfl
  simp only [hsz, hBytes]
  rw [if_pos (show o + 4 ≤ blk.length from by omega)]
  rw [slice_eq]
  simp [decodeLE_encodeLE, Nat.mod_eq_of_lt hv]

/-- Load u16 at `.ptr 3 off` from a 48-byte block. -/
theorem load_u16_field_of_geom (m : Mem) (o : Nat) (blk : List UInt8) (hm : m 3 = some blk)
    (len : blk.length = 48) (ho : o ≤ 46)
    (nval : Nat) (slice_eq : (blk.drop o).take 2 = encodeLE 2 nval)
    (hv : nval < 65536) :
    load m (.int ⟨16, false⟩) (.ptr 3 o) = .ok (Val.int ⟨16, false⟩ nval) := by
  simp only [load, Ty.size]
  simp only [readBytes]
  rw [hm]
  have hsz : (Ty.int { width := 16, signed := false }).size = 2 := rfl
  have hBytes : IntTy.bytes { width := 16, signed := false } = 2 := rfl
  simp only [hsz, hBytes]
  rw [if_pos (show o + 2 ≤ blk.length from by omega)]
  rw [slice_eq]
  simp [decodeLE_encodeLE, Nat.mod_eq_of_lt hv]

/-- Load u8 at `.ptr 3 off` from a 48-byte block. -/
theorem load_u8_field_of_geom (m : Mem) (o : Nat) (blk : List UInt8) (hm : m 3 = some blk)
    (len : blk.length = 48) (ho : o ≤ 47)
    (nval : Nat) (slice_eq : (blk.drop o).take 1 = encodeLE 1 nval)
    (hv : nval < 256) :
    load m (.int ⟨8, false⟩) (.ptr 3 o) = .ok (Val.int ⟨8, false⟩ nval) := by
  simp only [load, Ty.size]
  simp only [readBytes]
  rw [hm]
  have hsz : (Ty.int { width := 8, signed := false }).size = 1 := rfl
  have hBytes : IntTy.bytes { width := 8, signed := false } = 1 := rfl
  simp only [hsz, hBytes]
  rw [if_pos (show o + 1 ≤ blk.length from by omega)]
  rw [slice_eq]
  simp [decodeLE_encodeLE, Nat.mod_eq_of_lt hv]

/-- `decodeLE` against a known encode. -/
theorem decodeLE_of_lt (k v : Nat) (hk : v < 256 ^ k) : decodeLE (encodeLE k v) = v := by
  rw [decodeLE_encodeLE, Nat.mod_eq_of_lt hk]

end NANO.C.Proofs
