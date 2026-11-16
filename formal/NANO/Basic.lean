/-
  Basic types shared by the nanoimage formalization.

  Byte strings are `List UInt8`. Out-of-range reads yield 0 in the
  specification (never happens under the guards proved for each decoder,
  exactly as in the GLB framing of the reference formalization).
-/
namespace NANO

/-- Byte strings (untrusted input). -/
abbrev Bytes := List UInt8

/-- Byte at `i`, or 0 past the end. -/
def byteAt (d : List UInt8) (i : Nat) : Nat := (d.getD i 0).toNat

/-- Little-endian 16-bit read. -/
def rd16le (d : List UInt8) (off : Nat) : Nat :=
  byteAt d off + byteAt d (off + 1) * 2 ^ 8

/-- Little-endian 32-bit read. -/
def rd32le (d : List UInt8) (off : Nat) : Nat :=
  byteAt d off + byteAt d (off + 1) * 2 ^ 8 + byteAt d (off + 2) * 2 ^ 16 +
    byteAt d (off + 3) * 2 ^ 24

/-- Little-endian 64-bit read. -/
def rd64le (d : List UInt8) (off : Nat) : Nat :=
  rd32le d off + rd32le d (off + 4) * 2 ^ 32

/-- Big-endian 16-bit read. -/
def rd16be (d : List UInt8) (off : Nat) : Nat :=
  byteAt d off * 2 ^ 8 + byteAt d (off + 1)

/-- Big-endian 32-bit read. -/
def rd32be (d : List UInt8) (off : Nat) : Nat :=
  byteAt d off * 2 ^ 24 + byteAt d (off + 1) * 2 ^ 16 + byteAt d (off + 2) * 2 ^ 8 +
    byteAt d (off + 3)

/-- Big-endian 64-bit read. -/
def rd64be (d : List UInt8) (off : Nat) : Nat :=
  rd32be d off * 2 ^ 32 + rd32be d (off + 4)

end NANO
