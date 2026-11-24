/-
  Byte-level helpers for composing the TGA header (fid 21) with the decoder
  (fid 23): reading integer fields out of an encoded `ni_tga_info` block.
-/
import NANO.C.Proofs.Core
import NANO.C.Proofs.NiTgaHeader
import NANO.C.Proofs.NiTgaHeaderExs

open NANO NANO.C NANO.C.Proofs
set_option maxHeartbeats 4000000 in

/-- Reading `n` bytes of a block that is present and long enough. -/
theorem readBytes_some (m : Mem) (b o n : Nat) (blk : List UInt8)
    (hm : m b = some blk) (hl : o + n ≤ blk.length) :
    readBytes m b o n = .ok ((blk.drop o).take n) := by
  unfold readBytes
  rw [hm]
  simp only [hl, if_true]

/-- An integer load from a present, long-enough block, as raw byte decoding. -/
theorem load_int_some (m : Mem) (t : IntTy) (b o : Nat) (blk : List UInt8)
    (hm : m b = some blk) (hl : o + t.bytes ≤ blk.length) :
    load m (.int t) (.ptr b o)
      = .ok (.int t (decodeLE ((blk.drop o).take (Ty.size (.int t))))) := by
  unfold load
  dsimp only
  simp only [Ty.size]
  rw [readBytes_some m b o t.bytes blk hm hl]
  rfl

/-- Extract a contiguous sub-block `B` at offset `P.length` from `P ++ B ++ S`. -/
theorem slice_mid (P B S : List UInt8) (o k : Nat) (hp : P.length = o) (hk : B.length = k) :
    ((P ++ (B ++ S)).drop o).take k = B := by
  rw [← hp, List.drop_left, ← hk, List.take_left]

/-- `decodeLE` of a one-byte little-endian encoding. -/
theorem decodeLE_enc1 (n : Nat) (hn : n < 256) : decodeLE (encodeLE 1 n) = n := by
  rw [decodeLE_encodeLE, show (256 : Nat) ^ 1 = 256 from by decide]
  exact Nat.mod_eq_of_lt hn

/-- `decodeLE` of a four-byte little-endian encoding. -/
theorem decodeLE_enc4 (n : Nat) (hn : n < 2 ^ 32) : decodeLE (encodeLE 4 n) = n := by
  rw [decodeLE_encodeLE, show (256 : Nat) ^ 4 = 2 ^ 32 from by decide]
  exact Nat.mod_eq_of_lt hn

/-- `decodeLE` of an eight-byte little-endian encoding. -/
theorem decodeLE_enc8 (n : Nat) (hn : n < 2 ^ 64) : decodeLE (encodeLE 8 n) = n := by
  rw [decodeLE_encodeLE, show (256 : Nat) ^ 8 = 2 ^ 64 from by decide]
  exact Nat.mod_eq_of_lt hn
