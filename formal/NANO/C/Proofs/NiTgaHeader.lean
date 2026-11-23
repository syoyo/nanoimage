/-
  `ni_tga_header` refinement — reusable foundation.

  This module provides the info-block canonical form and the 32-byte
  field-store / address lemmas that the staged header proof composes.
  All lemmas here are fully proven (no `sorry`).
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Lemmas
import NANO.Spec
import NANO.Tga
import NANO.C.Proofs.Core
import NANO.C.Proofs.NiGeometryTail
import NANO.C.Proofs.NiBmpDecode

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 1600000

namespace NANO.C.Proofs
open NANO NANO.C

/-- Canonical 32-byte `ni_tga_info` block after `ni_tga_header` succeeds.
    Fields occupy `[0,28)`; bytes `[28,32)` (unwritten by the C) are carried
    over from the incoming block `obl`. -/
def tgaHeaderBlock (obl : List UInt8) (h : TgaInfo) : List UInt8 :=
  encodeLE 8 h.outputSize ++ encodeLE 8 h.dataOffset ++ encodeLE 4 h.width ++
  encodeLE 4 h.height ++ encodeLE 1 h.channels ++ encodeLE 1 h.rle ++
  encodeLE 1 h.topOrigin ++ encodeLE 1 h.rightOrigin ++ obl.drop 28

/-- Zero-initialised variant: the block when the caller zeroes the struct. -/
def tgaHeadBlock (h : TgaInfo) : List UInt8 :=
  tgaHeaderBlock (List.replicate 32 0) h

theorem tgaHeaderBlock_length (obl : List UInt8) (h : TgaInfo) (hl : obl.length = 32) :
    (tgaHeaderBlock obl h).length = 32 := by
  simp [tgaHeaderBlock, encodeLE_length, List.length_append, List.length_drop, hl]

theorem tgaHeadBlock_length (h : TgaInfo) : (tgaHeadBlock h).length = 32 := by
  simpa [tgaHeadBlock] using tgaHeaderBlock_length (List.replicate 32 0) h (by simp)

theorem tgaHeadBlock_eq (h : TgaInfo) :
    tgaHeadBlock h =
      encodeLE 8 h.outputSize ++ encodeLE 8 h.dataOffset ++ encodeLE 4 h.width ++
      encodeLE 4 h.height ++ encodeLE 1 h.channels ++ encodeLE 1 h.rle ++
      encodeLE 1 h.topOrigin ++ encodeLE 1 h.rightOrigin ++ [0, 0, 0, 0] := by
  simp [tgaHeadBlock, tgaHeaderBlock, List.replicate_succ]

/-- `&info[off]` when local 2 holds the info pointer (`<block> 0`). -/
theorem ev_field32 {s : State} {ob : Nat} {obl : List UInt8} {off : Nat}
    (hm : s.mem ob = some obl) (hl2 : s.locals 2 = some (.ptr ob 0)) (hoff : off ≤ obl.length) :
    EvE Gen.prog s (.field (.var 2) off) (.ptr ob (0 + off)) :=
  EvE.field (EvE.var hl2) (ptrAddN_ok hm (by omega))

/-- Byte store into a 32-byte info block. -/
theorem store_field_u8_32 (m : Mem) (ob : Nat) (obl : List UInt8) (hm : m ob = some obl)
    (hl : obl.length = 32) (off : Nat) (hoff : off + 1 ≤ 32) (v : Nat) (hv : v < 256) :
    store m (.int u8) (.ptr ob off) (.int u8 v)
      = .ok (m.upd ob (obl.take off ++ encodeLE 1 v ++ obl.drop (off + 1))) := by
  have hbytes : IntTy.bytes ⟨8, false⟩ = 1 := rfl
  have hlen : (encodeLE 1 v).length = 1 := encodeLE_length 1 v
  simp only [store, writeBytes, hm, hbytes, hlen]
  rw [ite_true, if_pos (by rw [hl]; omega)]

/-- 16-bit store into a 32-byte info block. -/
theorem store_field_u16_32 (m : Mem) (ob : Nat) (obl : List UInt8) (hm : m ob = some obl)
    (hl : obl.length = 32) (off : Nat) (hoff : off + 2 ≤ 32) (v : Nat) (hv : v < 65536) :
    store m (.int u16) (.ptr ob off) (.int u16 v)
      = .ok (m.upd ob (obl.take off ++ encodeLE 2 v ++ obl.drop (off + 2))) := by
  have hbytes : IntTy.bytes ⟨16, false⟩ = 2 := rfl
  have hlen : (encodeLE 2 v).length = 2 := encodeLE_length 2 v
  simp only [store, writeBytes, hm, hbytes, hlen]
  rw [ite_true, if_pos (by rw [hl]; omega)]

/-- 32-bit store into a 32-byte info block. -/
theorem store_field_u32_32 (m : Mem) (ob : Nat) (obl : List UInt8) (hm : m ob = some obl)
    (hl : obl.length = 32) (off : Nat) (hoff : off + 4 ≤ 32) (v : Nat) (hv : v < 2 ^ 32) :
    store m (.int u32) (.ptr ob off) (.int u32 v)
      = .ok (m.upd ob (obl.take off ++ encodeLE 4 v ++ obl.drop (off + 4))) := by
  have hbytes : IntTy.bytes ⟨32, false⟩ = 4 := rfl
  have hlen : (encodeLE 4 v).length = 4 := encodeLE_length 4 v
  simp only [store, writeBytes, hm, hbytes, hlen]
  rw [ite_true, if_pos (by rw [hl]; omega)]

/-- 64-bit store into a 32-byte info block. -/
theorem store_field_u64_32 (m : Mem) (ob : Nat) (obl : List UInt8) (hm : m ob = some obl)
    (hl : obl.length = 32) (off : Nat) (hoff : off + 8 ≤ 32) (v : Nat) (hv : v < 2 ^ 64) :
    store m (.int u64) (.ptr ob off) (.int u64 v)
      = .ok (m.upd ob (obl.take off ++ encodeLE 8 v ++ obl.drop (off + 8))) := by
  have hbytes : IntTy.bytes ⟨64, false⟩ = 8 := rfl
  have hlen : (encodeLE 8 v).length = 8 := encodeLE_length 8 v
  simp only [store, writeBytes, hm, hbytes, hlen]
  rw [ite_true, if_pos (by rw [hl]; omega)]

end NANO.C.Proofs
