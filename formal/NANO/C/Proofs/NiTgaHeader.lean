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


/-! ### Take/drop of a concatenation prefix -/

private theorem tk (P S : List UInt8) (k : Nat) (h : P.length = k) : (P ++ S).take k = P := by
  rw [← h]; exact List.take_append_length

private theorem dr (P S : List UInt8) (k j : Nat) (h : P.length = k) :
    (P ++ S).drop (k + j) = S.drop j := by
  rw [← h]; exact List.drop_length_add_append j

private theorem take_take_eq (l : List UInt8) (a b : Nat) (h : b ≤ a) :
    (l.take a).take b = l.take b := by
  rw [List.take_take, Nat.min_eq_left h]

/-- `obl.take 16` has length 16 (for a 32-byte block). -/
private theorem len_take16 (obl : List UInt8) (hl : obl.length = 32) :
    (obl.take 16).length = 16 := by
  rw [List.length_take, Nat.min_eq_left (by rw [hl]; omega)]

/-- `obl.take 8` has length 8 (for a 32-byte block). -/
private theorem len_take8 (obl : List UInt8) (hl : obl.length = 32) :
    (obl.take 8).length = 8 := by
  rw [List.length_take, Nat.min_eq_left (by rw [hl]; omega)]

/-- The canonical 32-byte info block is exactly the result of writing the eight
    header fields (in `ni_tga_header`'s C order) into an incoming 32-byte block. -/
theorem tgaHeaderBlock_stores (obl : List UInt8)
    (w hh ch rle top right doff osz : Nat) (hl : obl.length = 32) :
    let b1 := obl.take 16 ++ encodeLE 4 w ++ obl.drop 20
    let b2 := b1.take 20 ++ encodeLE 4 hh ++ b1.drop 24
    let b3 := b2.take 24 ++ encodeLE 1 ch ++ b2.drop 25
    let b4 := b3.take 25 ++ encodeLE 1 rle ++ b3.drop 26
    let b5 := b4.take 26 ++ encodeLE 1 top ++ b4.drop 27
    let b6 := b5.take 27 ++ encodeLE 1 right ++ b5.drop 28
    let b7 := b6.take 8 ++ encodeLE 8 doff ++ b6.drop 16
    let b8 := b7.take 0 ++ encodeLE 8 osz ++ b7.drop 8
    b8 = encodeLE 8 osz ++ encodeLE 8 doff ++ encodeLE 4 w ++ encodeLE 4 hh ++
      encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top ++ encodeLE 1 right ++ obl.drop 28 := by
  intro b1 b2 b3 b4 b5 b6 b7 b8
  have hP1 : (obl.take 16 ++ encodeLE 4 w).length = 20 := by
    simp [encodeLE_length, List.length_take, List.length_append, Nat.min_eq_left (by omega : 16 ≤ 32), hl]
  have hP2 : (obl.take 16 ++ encodeLE 4 w ++ encodeLE 4 hh).length = 24 := by
    simp [encodeLE_length, List.length_take, List.length_append, Nat.min_eq_left (by omega : 16 ≤ 32), hl]
  have hP3 : (obl.take 16 ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch).length = 25 := by
    simp [encodeLE_length, List.length_take, List.length_append, Nat.min_eq_left (by omega : 16 ≤ 32), hl]
  have hP4 : (obl.take 16 ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle).length = 26 := by
    simp [encodeLE_length, List.length_take, List.length_append, Nat.min_eq_left (by omega : 16 ≤ 32), hl]
  have hP5 : (obl.take 16 ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top).length = 27 := by
    simp [encodeLE_length, List.length_take, List.length_append, Nat.min_eq_left (by omega : 16 ≤ 32), hl]
  have hP6 : (obl.take 16 ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top ++ encodeLE 1 right).length = 28 := by
    simp [encodeLE_length, List.length_take, List.length_append, Nat.min_eq_left (by omega : 16 ≤ 32), hl]
  have e1 : b1 = (obl.take 16 ++ encodeLE 4 w) ++ obl.drop 20 := rfl
  have e2 : b2 = (obl.take 16 ++ encodeLE 4 w ++ encodeLE 4 hh) ++ obl.drop 24 := by
    rw [show b2 = b1.take 20 ++ encodeLE 4 hh ++ b1.drop 24 from rfl, e1]
    have hd : ((obl.take 16 ++ encodeLE 4 w) ++ obl.drop 20).drop 24 = obl.drop 24 := by
      rw [show (24 : Nat) = 20 + 4 by omega, dr _ _ 20 4 hP1, List.drop_drop]
    rw [tk _ _ 20 hP1, hd]
  have e3 : b3 = (obl.take 16 ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch) ++ obl.drop 25 := by
    rw [show b3 = b2.take 24 ++ encodeLE 1 ch ++ b2.drop 25 from rfl, e2]
    have hd : ((obl.take 16 ++ encodeLE 4 w ++ encodeLE 4 hh) ++ obl.drop 24).drop 25 = obl.drop 25 := by
      rw [show (25 : Nat) = 24 + 1 by omega, dr _ _ 24 1 hP2, List.drop_drop]
    rw [tk _ _ 24 hP2, hd]
  have e4 : b4 = (obl.take 16 ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle) ++ obl.drop 26 := by
    rw [show b4 = b3.take 25 ++ encodeLE 1 rle ++ b3.drop 26 from rfl, e3]
    have hd : ((obl.take 16 ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch) ++ obl.drop 25).drop 26 = obl.drop 26 := by
      rw [show (26 : Nat) = 25 + 1 by omega, dr _ _ 25 1 hP3, List.drop_drop]
    rw [tk _ _ 25 hP3, hd]
  have e5 : b5 = (obl.take 16 ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top) ++ obl.drop 27 := by
    rw [show b5 = b4.take 26 ++ encodeLE 1 top ++ b4.drop 27 from rfl, e4]
    have hd : ((obl.take 16 ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle) ++ obl.drop 26).drop 27 = obl.drop 27 := by
      rw [show (27 : Nat) = 26 + 1 by omega, dr _ _ 26 1 hP4, List.drop_drop]
    rw [tk _ _ 26 hP4, hd]
  have e6 : b6 = (obl.take 16 ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top ++ encodeLE 1 right) ++ obl.drop 28 := by
    rw [show b6 = b5.take 27 ++ encodeLE 1 right ++ b5.drop 28 from rfl, e5]
    have hd : ((obl.take 16 ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top) ++ obl.drop 27).drop 28 = obl.drop 28 := by
      rw [show (28 : Nat) = 27 + 1 by omega, dr _ _ 27 1 hP5, List.drop_drop]
    rw [tk _ _ 27 hP5, hd]
  -- b7: expose b6 = (obl.take 16) ++ REST
  have hmin16 : (obl.take 16).length = 16 := len_take16 obl hl
  have e6' : b6 = obl.take 16 ++ (encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top ++ encodeLE 1 right ++ obl.drop 28) := by
    rw [e6]; simp [List.append_assoc]
  have e7 : b7 = obl.take 8 ++ encodeLE 8 doff ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top ++ encodeLE 1 right ++ obl.drop 28 := by
    rw [show b7 = b6.take 8 ++ encodeLE 8 doff ++ b6.drop 16 from rfl, e6']
    have htk8 : (obl.take 16 ++ (encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top ++ encodeLE 1 right ++ obl.drop 28)).take 8 = obl.take 8 := by
      rw [List.take_append_of_le_length (by rw [hmin16]; omega), take_take_eq obl 16 8 (by omega)]
    have hdr16 : (obl.take 16 ++ (encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top ++ encodeLE 1 right ++ obl.drop 28)).drop 16
        = encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top ++ encodeLE 1 right ++ obl.drop 28 := by
      rw [List.drop_append_of_le_length (by rw [hmin16]; omega),
          List.drop_eq_nil_of_le (by omega), List.nil_append]
    rw [htk8, hdr16]; simp [List.append_assoc]
  -- b8
  have e8 : b8 = encodeLE 8 osz ++ encodeLE 8 doff ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top ++ encodeLE 1 right ++ obl.drop 28 := by
    rw [show b8 = b7.take 0 ++ encodeLE 8 osz ++ b7.drop 8 from rfl, e7]
    have hmin8 : (obl.take 8).length = 8 := len_take8 obl hl
    have hdr8 : (obl.take 8 ++ (encodeLE 8 doff ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top ++ encodeLE 1 right ++ obl.drop 28)).drop 8
        = encodeLE 8 doff ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top ++ encodeLE 1 right ++ obl.drop 28 := by
      rw [List.drop_append_of_le_length (by rw [hmin8]; omega),
          List.drop_eq_nil_of_le (by omega), List.nil_append]
    rw [show (obl.take 8 ++ encodeLE 8 doff ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top ++ encodeLE 1 right ++ obl.drop 28)
          = obl.take 8 ++ (encodeLE 8 doff ++ encodeLE 4 w ++ encodeLE 4 hh ++ encodeLE 1 ch ++ encodeLE 1 rle ++ encodeLE 1 top ++ encodeLE 1 right ++ obl.drop 28) from by simp [List.append_assoc]]
    rw [List.take_zero, List.nil_append, hdr8]; simp [List.append_assoc]
  exact e8

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- Preamble of `ni_tga_header`: size gate (false), then load bytes 0/1/2/16/17
    and read u16le width/height at 12/14. -/
theorem tgaHeader_loads (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hlen : d.length < 2 ^ 64) (ro : Bool) (hro : ro = false)
    (hsz : ¬ size < 18) :
    ∃ s7, ExS Gen.prog ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩
      (.seq (.ite (.bin .lt (some u64) (.var 1) (.cast u64 (.const (.int u32 18)))) (.ret (some (.const (.int i32 1)))) .skip) (.seq (.set 3 (.load (.int u8) (.index (.var 0) (.const (.int i32 0)) 1))) (.seq (.set 4 (.load (.int u8) (.index (.var 0) (.const (.int i32 1)) 1))) (.seq (.set 5 (.load (.int u8) (.index (.var 0) (.const (.int i32 2)) 1))) (.seq (.call (some 6) 0 [(.index (.var 0) (.const (.int i32 12)) 1)]) (.seq (.call (some 7) 0 [(.index (.var 0) (.const (.int i32 14)) 1)]) (.seq (.set 8 (.load (.int u8) (.index (.var 0) (.const (.int i32 16)) 1))) (.set 9 (.load (.int u8) (.index (.var 0) (.const (.int i32 17)) 1))))))))))
      .normal s7 ∧
      s7.locals 0 = some (.ptr bd 0) ∧
      s7.locals 1 = some (.int u64 size) ∧
      s7.locals 2 = some (.ptr 3 0) ∧
      s7.locals 3 = some (.int u8 (byteAt d 0)) ∧
      s7.locals 4 = some (.int u8 (byteAt d 1)) ∧
      s7.locals 5 = some (.int u8 (byteAt d 2)) ∧
      s7.locals 6 = some (.int u16 (rd16le d 12)) ∧
      s7.locals 7 = some (.int u16 (rd16le d 14)) ∧
      s7.locals 8 = some (.int u8 (byteAt d 16)) ∧
      s7.locals 9 = some (.int u8 (byteAt d 17)) ∧
      s7.mem = m := by
  have hd18 : 18 ≤ d.length := by omega
  have htb : truthy (boolVal false) = .ok false := truthy_boolVal false
  let s0 : State := ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩
  -- size gate (false)
  have hcast : evalCast u64 (.int u32 18) = .ok (.int u64 18) := u32_u64_cast 18 (by omega)
  have hlt : EvE Gen.prog s0 (.bin .lt (some u64) (.var 1) (.cast u64 (.const (.int u32 18))))
      (boolVal (decide (size < 18))) :=
    EvE.bin (EvE.var rfl) (EvE.cast (EvE.const _) hcast) (bin_u64_lt size 18)
  have hltf : EvE Gen.prog s0 (.bin .lt (some u64) (.var 1) (.cast u64 (.const (.int u32 18)))) (boolVal false) := by
    rw [show decide (size < 18) = false from decide_eq_false_iff_not.mpr hsz] at hlt; exact hlt
  have hgate0 : ExS Gen.prog s0 (.ite (.bin .lt (some u64) (.var 1) (.cast u64 (.const (.int u32 18)))) (.ret (some (.const (.int i32 1)))) .skip) .normal s0 :=
    ExS.ite hltf htb ExS.skip
  -- byte loads
  have load3 : ExS Gen.prog s0 (.set 3 (.load (.int u8) (.index (.var 0) (.const (.int i32 0)) 1))) .normal
      {s0 with locals := s0.locals.upd 3 (.int u8 (byteAt d 0))} :=
    ExS.set (EvE.load (ev_ptr_const (s := s0) (d := d) (k := 0) hm rfl (by omega) (by omega))
      (load_byte_dyn m bd d hm 0 (by omega)))
  let s3 : State := { locals := s0.locals.upd 3 (.int u8 (byteAt d 0)), mem := m, ro := ro }
  have load4 : ExS Gen.prog s3 (.set 4 (.load (.int u8) (.index (.var 0) (.const (.int i32 1)) 1))) .normal
      {s3 with locals := s3.locals.upd 4 (.int u8 (byteAt d 1))} :=
    ExS.set (EvE.load (ev_ptr_const (s := s3) (d := d) (k := 1) hm (by rfl) (by omega) (by omega))
      (load_byte_dyn m bd d hm 1 (by omega)))
  let s4 : State := { locals := s3.locals.upd 4 (.int u8 (byteAt d 1)), mem := m, ro := ro }
  have load5 : ExS Gen.prog s4 (.set 5 (.load (.int u8) (.index (.var 0) (.const (.int i32 2)) 1))) .normal
      {s4 with locals := s4.locals.upd 5 (.int u8 (byteAt d 2))} :=
    ExS.set (EvE.load (ev_ptr_const (s := s4) (d := d) (k := 2) hm (by rfl) (by omega) (by omega))
      (load_byte_dyn m bd d hm 2 (by omega)))
  let s5 : State := { locals := s4.locals.upd 5 (.int u8 (byteAt d 2)), mem := m, ro := ro }
  -- u16le reads
  have call6 : ExS Gen.prog s5 (.call (some 6) 0 [(.index (.var 0) (.const (.int i32 12)) 1)]) .normal
      {s5 with locals := s5.locals.upd 6 (.int u16 (rd16le d 12))} :=
    ExS.call_dst (s' := ⟨frameLocals [0] [.ptr bd 12], m, ro⟩) (EvArgs.cons (ev_ptr_const (s := s5) (d := d) (k := 12) hm (by rfl) (by omega) (by omega)) EvArgs.nil)
      (show Gen.prog 0 = some Gen.ni_read_u16le from rfl)
      (show Gen.ni_read_u16le.params.length = 1 from rfl)
      (ni_read_u16le_exs m bd d hm 12 (by omega) hlen ro)
  let s6 : State := { locals := s5.locals.upd 6 (.int u16 (rd16le d 12)), mem := m, ro := ro }
  have call7 : ExS Gen.prog s6 (.call (some 7) 0 [(.index (.var 0) (.const (.int i32 14)) 1)]) .normal
      {s6 with locals := s6.locals.upd 7 (.int u16 (rd16le d 14))} :=
    ExS.call_dst (s' := ⟨frameLocals [0] [.ptr bd 14], m, ro⟩) (EvArgs.cons (ev_ptr_const (s := s6) (d := d) (k := 14) hm (by rfl) (by omega) (by omega)) EvArgs.nil)
      (show Gen.prog 0 = some Gen.ni_read_u16le from rfl)
      (show Gen.ni_read_u16le.params.length = 1 from rfl)
      (ni_read_u16le_exs m bd d hm 14 (by omega) hlen ro)
  let s7a : State := { locals := s6.locals.upd 7 (.int u16 (rd16le d 14)), mem := m, ro := ro }
  have load8 : ExS Gen.prog s7a (.set 8 (.load (.int u8) (.index (.var 0) (.const (.int i32 16)) 1))) .normal
      {s7a with locals := s7a.locals.upd 8 (.int u8 (byteAt d 16))} :=
    ExS.set (EvE.load (ev_ptr_const (s := s7a) (d := d) (k := 16) hm (by rfl) (by omega) (by omega))
      (load_byte_dyn m bd d hm 16 (by omega)))
  let s7b : State := { locals := s7a.locals.upd 8 (.int u8 (byteAt d 16)), mem := m, ro := ro }
  have load9 : ExS Gen.prog s7b (.set 9 (.load (.int u8) (.index (.var 0) (.const (.int i32 17)) 1))) .normal
      {s7b with locals := s7b.locals.upd 9 (.int u8 (byteAt d 17))} :=
    ExS.set (EvE.load (ev_ptr_const (s := s7b) (d := d) (k := 17) hm (by rfl) (by omega) (by omega))
      (load_byte_dyn m bd d hm 17 (by omega)))
  let s7 : State := { locals := s7b.locals.upd 9 (.int u8 (byteAt d 17)), mem := m, ro := ro }
  refine ⟨s7, ?_, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl⟩
  exact ExS.seq hgate0 (ExS.seq load3 (ExS.seq load4 (ExS.seq load5
    (ExS.seq call6 (ExS.seq call7 (ExS.seq load8 load9))))))

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- `evalCast` u8→u32 preserves a byte. -/
theorem u8_u32_cast (n : Nat) (h : n < 256) : evalCast u32 (.int u8 n) = .ok (.int u32 n) := by
  simp [evalCast, u8, u32, IntTy.modulus, Nat.mod_eq_of_lt (show n < 4294967296 by omega)]

/-- `evalCast` u8→u64 preserves a byte. -/
theorem u8_u64_cast (n : Nat) (h : n < 256) : evalCast u64 (.int u8 n) = .ok (.int u64 n) := by
  simp [evalCast, u8, u64, IntTy.modulus, Nat.mod_eq_of_lt (show n < 18446744073709551616 by omega)]

/-- `evalCast` u16→u64 preserves a short. -/
theorem u16_u64_cast' (n : Nat) (h : n < 65536) : evalCast u64 (.int u16 n) = .ok (.int u64 n) :=
  u16_u64_cast n h

/-- Unsigned u32 bitwise-and. -/
theorem bin_u32_band (n k : Nat) :
    evalBin .band (some u32) (.int u32 n) (.int u32 k) = .ok (.int u32 (n &&& k)) := by
  simp [evalBin, evalBinInt, binInt, intOf, u32, isPtr, ptrEq]

/-- `evalCast` i32→u8 for a small non-negative literal. -/
theorem i32_u8_cast (k : Nat) (hk : k < 256) :
    evalCast u8 (.int i32 k) = .ok (.int u8 k) := by
  simp only [evalCast, i32, u8, IntTy.signed, if_true]
  simp [IntTy.wrap, IntTy.toInt, IntTy.modulus, IntTy.signed, IntTy.width, u8,
    show ¬ (2147483648 ≤ k) by omega, Int.emod_eq_of_lt (by omega : (0 : Int) ≤ (k : Int)) (by omega : (k : Int) < 256), Int.toNat_natCast]

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- `evalCast` u32→u8 truncates; value preserved for bytes. -/
theorem u32_u8_cast (k : Nat) (hk : k < 256) : evalCast u8 (.int u32 k) = .ok (.int u8 k) := by
  simp [evalCast, u8, u32, IntTy.modulus, Nat.mod_eq_of_lt hk]

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- Unsigned u64 multiply (non-wrapping). -/
theorem bin_u64_mul (a b : Nat) (h : a * b < 2 ^ 64) :
    evalBin .mul (some u64) (.int u64 a) (.int u64 b) = .ok (.int u64 (a * b)) := by
  simp [evalBin, evalBinInt, binInt, intOf, u64, IntTy.modulus, isPtr, ptrEq, Nat.mod_eq_of_lt h]

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- `evalCast` i32→u64 for a small non-negative literal. -/
theorem i32_u64_cast (k : Nat) (hk : k < 2 ^ 31) : evalCast u64 (.int i32 k) = .ok (.int u64 k) := by
  simp only [evalCast, i32, u64, IntTy.signed, if_true]
  simp [IntTy.wrap, IntTy.toInt, IntTy.modulus, IntTy.signed, IntTy.width, u64,
    show ¬ (2147483648 ≤ k) by omega,
    Int.emod_eq_of_lt (by omega : (0 : Int) ≤ (k : Int)) (by omega : (k : Int) < 18446744073709551616),
    Int.toNat_natCast]

end NANO.C.Proofs
