/-
  Specifications for the nanoimage verified core (Phase 1 leaves).

  Sizes/addresses are `Nat` with the `< 2^64` bound recorded as an
  explicit hypothesis where needed, mirroring the reference
  formalization's `u64Bound` discipline.
-/
import NANO.Basic

namespace NANO

/-- `ni_read_u16le(p)`: little-endian 16-bit load at `off`. -/
abbrev le16 (d : List UInt8) (off : Nat) : Nat := rd16le d off
/-- `ni_read_u32le(p)`: little-endian 32-bit load at `off`. -/
abbrev le32 (d : List UInt8) (off : Nat) : Nat := rd32le d off
/-- `ni_read_u32be(p)`: big-endian 32-bit load at `off`. -/
abbrev be32 (d : List UInt8) (off : Nat) : Nat := rd32be d off
/-- `ni_read_u16be(p)`: big-endian 16-bit load at `off`. -/
abbrev be16 (d : List UInt8) (off : Nat) : Nat := rd16be d off

/-- `SIZE_MAX` on LP64. -/
def sizeMax : Nat := 2 ^ 64 - 1

/-- `ni_size_mul` success condition and result: `a * b` no wrap-around. -/
def sizeMulOK (a b : Nat) : Bool := (a == 0) || (b <= sizeMax / a)

/-- `ni_size_add` success condition and result. -/
def sizeAddOK (a b : Nat) : Bool := decide (a <= sizeMax - b)

/-- `ni_clamp_u8(v)`: `v` clamped to `[0, 255]`, re-interpreted as a byte. -/
def clampU8 (v : Int) : Nat := (min 255 (max 0 v)).toNat

theorem clampU8_neg {v : Int} (h : v < 0) : clampU8 v = 0 := by
  unfold clampU8; omega

theorem clampU8_big {v : Int} (h : 255 < v) : clampU8 v = 255 := by
  unfold clampU8; omega

theorem clampU8_mid {v : Int} (h0 : 0 ≤ v) (h1 : v ≤ 255) : clampU8 v = v.toNat := by
  unfold clampU8; omega

/-- `ni_scale_to_8bit`: `bit_depth ∈ [1, 8]` guard; u32-wrapped arithmetic,
    exactly as in C; result truncated to a byte. -/
def scaleTo8 (v : Nat) (bitDepth : Nat) : Option Nat :=
  if bitDepth = 0 || bitDepth > 8 then none else
    let maxv := 2 ^ bitDepth - 1
    some ((((v % 4294967296 * 255) % 4294967296 + maxv / 2) % 4294967296) / maxv % 256)

/-- `ni_read_packed_bits`: extract `bitDepth` bits at `pixelIndex * bitDepth`.
    Requires the caller's row to hold the requested bits (out-of-row reads are
    UB in C and are excluded by the hypothesis). -/
def packedBits (row : List UInt8) (pixelIndex bitDepth : Nat) : Nat :=
  let bitIndex := pixelIndex * bitDepth
  let byteIndex := bitIndex / 8
  let shift := 8 - bitDepth - (bitIndex % 8)
  ((byteAt row byteIndex) / 2 ^ shift) &&& (2 ^ bitDepth - 1)

/-- `ni_paeth(a, b, c)`. -/
def paeth (a b c : Nat) : Nat :=
  let p := (a : Int) + (b : Int) - (c : Int)
  let pa := if p > (a : Int) then p - (a : Int) else (a : Int) - p
  let pb := if p > (b : Int) then p - (b : Int) else (b : Int) - p
  let pc := if p > (c : Int) then p - (c : Int) else (c : Int) - p
  if pa <= pb && pa <= pc then a else if pb <= pc then b else c

end NANO
