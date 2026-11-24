import NANO.C.Proofs.NiTgaLoad

/-!
  Reading TGA header fields back out of the `ni_tga_info` block, for the
  composed load (`ni_load_tga`): after `ni_tga_header` succeeds it writes
  `tgaHeaderBlock`; the decoder then re-loads width/height/channels/rle/origins/
  dataOffset from that block.
-/

open NANO NANO.C NANO.C.Proofs

namespace NANO.C.Proofs

set_option maxHeartbeats 2000000

/-- Read `h.dataOffset` from the info block the TGA header writes. -/
theorem tgaHeaderBlock_load8 (m : Mem) (obl : List UInt8) (h : TgaInfo)
    (hm : m 3 = some (tgaHeaderBlock obl h)) (hl : obl.length = 32) (hval : h.dataOffset < 2 ^ 64) :
    load m (.int u64) (.ptr 3 8) = .ok (.int u64 h.dataOffset) := by
  have hlen : 8 + u64.bytes ≤ (tgaHeaderBlock obl h).length := by
    rw [tgaHeaderBlock_length obl h hl]; simp only [IntTy.bytes]; omega
  rw [load_int_some m u64 3 8 (tgaHeaderBlock obl h) hm hlen]
  simp only [Ty.size, IntTy.bytes]
  rw [show ((tgaHeaderBlock obl h).drop 8).take 8 = encodeLE 8 h.dataOffset from by
    simp only [tgaHeaderBlock, List.drop_append_of_le_length, List.take_append_of_le_length,
      List.length_append, List.length_drop, encodeLE_length, List.drop_eq_nil_of_le,
      Nat.reduceLeDiff, Nat.sub_self, List.nil_append]
    exact List.take_of_length_le (by simp [encodeLE_length])]
  rw [decodeLE_enc8 h.dataOffset hval]

/-- Read `h.width` from the info block the TGA header writes. -/
theorem tgaHeaderBlock_load16 (m : Mem) (obl : List UInt8) (h : TgaInfo)
    (hm : m 3 = some (tgaHeaderBlock obl h)) (hl : obl.length = 32) (hval : h.width < 2 ^ 32) :
    load m (.int u32) (.ptr 3 16) = .ok (.int u32 h.width) := by
  have hlen : 16 + u32.bytes ≤ (tgaHeaderBlock obl h).length := by
    rw [tgaHeaderBlock_length obl h hl]; simp only [IntTy.bytes]; omega
  rw [load_int_some m u32 3 16 (tgaHeaderBlock obl h) hm hlen]
  simp only [Ty.size, IntTy.bytes]
  rw [show ((tgaHeaderBlock obl h).drop 16).take 4 = encodeLE 4 h.width from by
    simp only [tgaHeaderBlock, List.drop_append_of_le_length, List.take_append_of_le_length,
      List.length_append, List.length_drop, encodeLE_length, List.drop_eq_nil_of_le,
      Nat.reduceLeDiff, Nat.sub_self, List.nil_append]
    exact List.take_of_length_le (by simp [encodeLE_length])]
  rw [decodeLE_enc4 h.width hval]

/-- Read `h.height` from the info block the TGA header writes. -/
theorem tgaHeaderBlock_load20 (m : Mem) (obl : List UInt8) (h : TgaInfo)
    (hm : m 3 = some (tgaHeaderBlock obl h)) (hl : obl.length = 32) (hval : h.height < 2 ^ 32) :
    load m (.int u32) (.ptr 3 20) = .ok (.int u32 h.height) := by
  have hlen : 20 + u32.bytes ≤ (tgaHeaderBlock obl h).length := by
    rw [tgaHeaderBlock_length obl h hl]; simp only [IntTy.bytes]; omega
  rw [load_int_some m u32 3 20 (tgaHeaderBlock obl h) hm hlen]
  simp only [Ty.size, IntTy.bytes]
  rw [show ((tgaHeaderBlock obl h).drop 20).take 4 = encodeLE 4 h.height from by
    simp only [tgaHeaderBlock, List.drop_append_of_le_length, List.take_append_of_le_length,
      List.length_append, List.length_drop, encodeLE_length, List.drop_eq_nil_of_le,
      Nat.reduceLeDiff, Nat.sub_self, List.nil_append]
    exact List.take_of_length_le (by simp [encodeLE_length])]
  rw [decodeLE_enc4 h.height hval]

/-- Read `h.channels` from the info block the TGA header writes. -/
theorem tgaHeaderBlock_load24 (m : Mem) (obl : List UInt8) (h : TgaInfo)
    (hm : m 3 = some (tgaHeaderBlock obl h)) (hl : obl.length = 32) (hval : h.channels < 256) :
    load m (.int u8) (.ptr 3 24) = .ok (.int u8 h.channels) := by
  have hlen : 24 + u8.bytes ≤ (tgaHeaderBlock obl h).length := by
    rw [tgaHeaderBlock_length obl h hl]; simp only [IntTy.bytes]; omega
  rw [load_int_some m u8 3 24 (tgaHeaderBlock obl h) hm hlen]
  simp only [Ty.size, IntTy.bytes]
  rw [show ((tgaHeaderBlock obl h).drop 24).take 1 = encodeLE 1 h.channels from by
    simp only [tgaHeaderBlock, List.drop_append_of_le_length, List.take_append_of_le_length,
      List.length_append, List.length_drop, encodeLE_length, List.drop_eq_nil_of_le,
      Nat.reduceLeDiff, Nat.sub_self, List.nil_append]
    exact List.take_of_length_le (by simp [encodeLE_length])]
  rw [decodeLE_enc1 h.channels hval]

/-- Read `h.rle` from the info block the TGA header writes. -/
theorem tgaHeaderBlock_load25 (m : Mem) (obl : List UInt8) (h : TgaInfo)
    (hm : m 3 = some (tgaHeaderBlock obl h)) (hl : obl.length = 32) (hval : h.rle < 256) :
    load m (.int u8) (.ptr 3 25) = .ok (.int u8 h.rle) := by
  have hlen : 25 + u8.bytes ≤ (tgaHeaderBlock obl h).length := by
    rw [tgaHeaderBlock_length obl h hl]; simp only [IntTy.bytes]; omega
  rw [load_int_some m u8 3 25 (tgaHeaderBlock obl h) hm hlen]
  simp only [Ty.size, IntTy.bytes]
  rw [show ((tgaHeaderBlock obl h).drop 25).take 1 = encodeLE 1 h.rle from by
    simp only [tgaHeaderBlock, List.drop_append_of_le_length, List.take_append_of_le_length,
      List.length_append, List.length_drop, encodeLE_length, List.drop_eq_nil_of_le,
      Nat.reduceLeDiff, Nat.sub_self, List.nil_append]
    exact List.take_of_length_le (by simp [encodeLE_length])]
  rw [decodeLE_enc1 h.rle hval]

/-- Read `h.topOrigin` from the info block the TGA header writes. -/
theorem tgaHeaderBlock_load26 (m : Mem) (obl : List UInt8) (h : TgaInfo)
    (hm : m 3 = some (tgaHeaderBlock obl h)) (hl : obl.length = 32) (hval : h.topOrigin < 256) :
    load m (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin) := by
  have hlen : 26 + u8.bytes ≤ (tgaHeaderBlock obl h).length := by
    rw [tgaHeaderBlock_length obl h hl]; simp only [IntTy.bytes]; omega
  rw [load_int_some m u8 3 26 (tgaHeaderBlock obl h) hm hlen]
  simp only [Ty.size, IntTy.bytes]
  rw [show ((tgaHeaderBlock obl h).drop 26).take 1 = encodeLE 1 h.topOrigin from by
    simp only [tgaHeaderBlock, List.drop_append_of_le_length, List.take_append_of_le_length,
      List.length_append, List.length_drop, encodeLE_length, List.drop_eq_nil_of_le,
      Nat.reduceLeDiff, Nat.sub_self, List.nil_append]
    exact List.take_of_length_le (by simp [encodeLE_length])]
  rw [decodeLE_enc1 h.topOrigin hval]

/-- Read `h.rightOrigin` from the info block the TGA header writes. -/
theorem tgaHeaderBlock_load27 (m : Mem) (obl : List UInt8) (h : TgaInfo)
    (hm : m 3 = some (tgaHeaderBlock obl h)) (hl : obl.length = 32) (hval : h.rightOrigin < 256) :
    load m (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin) := by
  have hlen : 27 + u8.bytes ≤ (tgaHeaderBlock obl h).length := by
    rw [tgaHeaderBlock_length obl h hl]; simp only [IntTy.bytes]; omega
  rw [load_int_some m u8 3 27 (tgaHeaderBlock obl h) hm hlen]
  simp only [Ty.size, IntTy.bytes]
  rw [show ((tgaHeaderBlock obl h).drop 27).take 1 = encodeLE 1 h.rightOrigin from by
    simp only [tgaHeaderBlock, List.drop_append_of_le_length, List.take_append_of_le_length,
      List.length_append, List.length_drop, encodeLE_length, List.drop_eq_nil_of_le,
      Nat.reduceLeDiff, Nat.sub_self, List.nil_append]
    exact List.take_of_length_le (by simp [encodeLE_length])]
  rw [decodeLE_enc1 h.rightOrigin hval]

end NANO.C.Proofs
