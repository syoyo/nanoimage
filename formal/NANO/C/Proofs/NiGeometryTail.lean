/-/
  Shared store/operations utilities for ni_bmp_geometry: the five
  fixed-offset stores into a 48-byte ni_bmp_info block, the post-LT tail
  expression executor `tail_exs`, and supporting pointer arithmetic helpers.
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Lemmas
import NANO.Spec
import NANO.Bmp
import NANO.C.Proofs.Core

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 40000

namespace NANO.C.Proofs
open NANO NANO.C

syntax "wsimp" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| wsimp [$ts,*]) => `(tactic| simp [Gen.prog, execStmt, evalExpr, evalArgs,
      evalBin, evalBinInt, binInt, evalCast, evalUn, intOf, load, C.store, readBytes, writeBytes,
      ptrAddN, ptrAdd, IntTy.u64, IntTy.u32, IntTy.u16, IntTy.u8, IntTy.i32, IntTy.toInt,
      IntTy.bytes, IntTy.modulus, Ty.size, Nat.mod_eq_of_lt, C.guard, truthy, boolVal, isPtr,
      ptrEq, Res.bind_ok, Res.bind_eq, List.idxOf?, List.findIdx?, List.findIdx?.go,
      $ts,*, *])
  | `(tactic| wsimp) => `(tactic| wsimp [Nat.zero_le])


/-- The 48-byte `ni_bmp_info` block after the five geometry stores,
    as a pure function of the original block and the stored fields
    (width@24, height@28, bit_count@40, channels@42, top_down@43). -/
def bmpTailBlock (obl : List UInt8) (w h : Nat) (b c t : Nat) : List UInt8 :=
  obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 h
    ++ (obl.drop 32).take 8 ++ encodeLE 2 b ++ encodeLE 1 c ++ encodeLE 1 t
    ++ obl.drop 44

theorem bmpTailBlock_length (obl : List UInt8) (h48 : obl.length = 48) (w hh b c t : Nat) :
    (bmpTailBlock obl w hh b c t).length = 48 := by
  simp [bmpTailBlock, h48, encodeLE_length, List.length_take, List.length_append, List.length_drop]

theorem bmpTailBlock_slice24 (obl : List UInt8) (h48 : obl.length = 48) (w hh b c t : Nat) :
    ((bmpTailBlock obl w hh b c t).drop 24).take 4 = encodeLE 4 w := by
  simp only [bmpTailBlock]
  simp [h48, encodeLE_length, List.length_take, List.length_drop, List.length_append,
        List.take_append, List.drop_append, List.drop_of_length_le, List.take_of_length_le,
        List.nil_append, List.append_nil]

theorem bmpTailBlock_slice28 (obl : List UInt8) (h48 : obl.length = 48) (w hh b c t : Nat) :
    ((bmpTailBlock obl w hh b c t).drop 28).take 4 = encodeLE 4 hh := by
  simp only [bmpTailBlock]
  simp [h48, encodeLE_length, List.length_take, List.length_drop, List.length_append,
        List.take_append, List.drop_append, List.drop_of_length_le, List.take_of_length_le,
        List.nil_append, List.append_nil]

theorem bmpTailBlock_slice40 (obl : List UInt8) (h48 : obl.length = 48) (w hh b c t : Nat) :
    ((bmpTailBlock obl w hh b c t).drop 40).take 2 = encodeLE 2 b := by
  simp only [bmpTailBlock]
  simp [h48, encodeLE_length, List.length_take, List.length_drop, List.length_append,
        List.take_append, List.drop_append, List.drop_of_length_le, List.take_of_length_le,
        List.nil_append, List.append_nil]

theorem bmpTailBlock_slice42 (obl : List UInt8) (h48 : obl.length = 48) (w hh b c t : Nat) :
    ((bmpTailBlock obl w hh b c t).drop 42).take 1 = encodeLE 1 c := by
  simp only [bmpTailBlock]
  simp [h48, encodeLE_length, List.length_take, List.length_drop, List.length_append,
        List.take_append, List.drop_append, List.drop_of_length_le, List.take_of_length_le,
        List.nil_append, List.append_nil]

theorem bmpTailBlock_slice43 (obl : List UInt8) (h48 : obl.length = 48) (w hh b c t : Nat) :
    ((bmpTailBlock obl w hh b c t).drop 43).take 1 = encodeLE 1 t := by
  simp only [bmpTailBlock]
  simp [h48, encodeLE_length, List.length_take, List.length_drop, List.length_append,
        List.take_append, List.drop_append, List.drop_of_length_le, List.take_of_length_le,
        List.nil_append, List.append_nil]


theorem stores_block_eq (obl : List UInt8) (h48 : obl.length = 48) (w hh b c t : Nat)
    (b1 : List UInt8) (hb1 : b1 = obl.take 24 ++ encodeLE 4 w ++ obl.drop 28)
    (b2 : List UInt8) (hb2 : b2 = b1.take 28 ++ encodeLE 4 hh ++ b1.drop 32)
    (b3 : List UInt8) (hb3 : b3 = b2.take 40 ++ encodeLE 2 b ++ b2.drop 42)
    (b4 : List UInt8) (hb4 : b4 = b3.take 42 ++ encodeLE 1 c ++ b3.drop 43) :
    b4.take 43 ++ encodeLE 1 t ++ b4.drop 44 = bmpTailBlock obl w hh b c t := by
  have hE4w : (encodeLE 4 w).length = 4 := encodeLE_length 4 w
  have hE4h : (encodeLE 4 hh).length = 4 := encodeLE_length 4 hh
  have hE2b : (encodeLE 2 b).length = 2 := encodeLE_length 2 b
  have hE1c : (encodeLE 1 c).length = 1 := encodeLE_length 1 c
  have hA : (obl.take 24 ++ encodeLE 4 w).length = 28 := by
    simp [h48, hE4w, List.length_take, List.length_append]
  have hB : (obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh).length = 32 := by
    simp [h48, hE4w, hE4h, List.length_take, List.length_append]
  have hb1_take28 : (obl.take 24 ++ encodeLE 4 w ++ obl.drop 28).take 28 = obl.take 24 ++ encodeLE 4 w := by
    rw [show ((obl.take 24 ++ encodeLE 4 w) ++ obl.drop 28) = obl.take 24 ++ encodeLE 4 w ++ obl.drop 28 from rfl]
    rw [show (28 : Nat) = (obl.take 24 ++ encodeLE 4 w).length from hA.symm]
    exact List.take_append_length
  have hb1_drop32 : (obl.take 24 ++ encodeLE 4 w ++ obl.drop 28).drop 32 = obl.drop 32 := by
    have key := List.drop_length_add_append (l₁ := obl.take 24 ++ encodeLE 4 w)
      (l₂ := obl.drop 28) (i := 4)
    rw [hA] at key
    rw [key]
    rw [show (32 : Nat) = 4 + 28 from rfl, List.drop_drop]
  have hb2_take40 : (obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh ++ obl.drop 32).take 40
      = obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh ++ (obl.drop 32).take 8 := by
    have key := List.take_length_add_append (l₁ := (obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh))
      (l₂ := obl.drop 32) (i := 8)
    rw [hB] at key
    rw [key]
  have hb2_drop42 : (obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh ++ obl.drop 32).drop 42 = obl.drop 42 := by
    have key := List.drop_length_add_append (l₁ := obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh)
      (l₂ := obl.drop 32) (i := 10)
    rw [hB] at key
    rw [key]
    rw [show (42 : Nat) = 10 + 32 from rfl, List.drop_drop]
  have hb3_take42 : (obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh ++ (obl.drop 32).take 8 ++ encodeLE 2 b ++ obl.drop 42).take 42
      = obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh ++ (obl.drop 32).take 8 ++ encodeLE 2 b := by
    have hC : (obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh ++ (obl.drop 32).take 8 ++ encodeLE 2 b).length = 42 := by
      simp [h48, hE4w, hE4h, hE2b, List.length_take, List.length_drop, List.length_append]
    have key := List.take_append_length (l₁ := obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh
        ++ (obl.drop 32).take 8 ++ encodeLE 2 b) (l₂ := obl.drop 42)
    rw [hC] at key
    exact key
  have hb3_drop43 : (obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh ++ (obl.drop 32).take 8 ++ encodeLE 2 b ++ obl.drop 42).drop 43 = obl.drop 43 := by
    have hC : (obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh ++ (obl.drop 32).take 8 ++ encodeLE 2 b).length = 42 := by
      simp [h48, hE4w, hE4h, hE2b, List.length_take, List.length_drop, List.length_append]
    have key := List.drop_length_add_append (l₁ := obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh
        ++ (obl.drop 32).take 8 ++ encodeLE 2 b) (l₂ := obl.drop 42) (i := 1)
    rw [hC] at key
    rw [key]
    rw [show (43 : Nat) = 1 + 42 from rfl, List.drop_drop]
  have hb4_take43 : (obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh ++ (obl.drop 32).take 8 ++ encodeLE 2 b ++ encodeLE 1 c ++ obl.drop 43).take 43
      = obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh ++ (obl.drop 32).take 8 ++ encodeLE 2 b ++ encodeLE 1 c := by
    have hC : (obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh ++ (obl.drop 32).take 8 ++ encodeLE 2 b ++ encodeLE 1 c).length = 43 := by
      simp [h48, hE4w, hE4h, hE2b, hE1c, List.length_take, List.length_drop, List.length_append]
    have key := List.take_append_length (l₁ := obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh
        ++ (obl.drop 32).take 8 ++ encodeLE 2 b ++ encodeLE 1 c) (l₂ := obl.drop 43)
    rw [hC] at key
    exact key
  have hb4_drop44 : (obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh ++ (obl.drop 32).take 8 ++ encodeLE 2 b ++ encodeLE 1 c ++ obl.drop 43).drop 44 = obl.drop 44 := by
    have hC : (obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh ++ (obl.drop 32).take 8 ++ encodeLE 2 b ++ encodeLE 1 c).length = 43 := by
      simp [h48, hE4w, hE4h, hE2b, hE1c, List.length_take, List.length_drop, List.length_append]
    have key := List.drop_length_add_append (l₁ := obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 hh
        ++ (obl.drop 32).take 8 ++ encodeLE 2 b ++ encodeLE 1 c) (l₂ := obl.drop 43) (i := 1)
    rw [hC] at key
    rw [key]
    rw [show (44 : Nat) = 1 + 43 from rfl, List.drop_drop]
  subst hb1 hb2 hb3 hb4
  rw [hb1_take28, hb1_drop32]
  rw [hb2_take40, hb2_drop42]
  rw [hb3_take42, hb3_drop43]
  rw [hb4_take43, hb4_drop44]
  rfl

theorem mem_upd_same (m : Mem) (b : Nat) (blk blk' : Block) :
    (m.upd b blk).upd b blk' = m.upd b blk' := by
  funext k
  by_cases h : k = b <;> simp [Mem.upd, h]

/-- Same as `store_field_u32`, for u64 fields. -/
theorem store_field_u64 (m : Mem) (ob : Nat) (obl : List UInt8) (hm : m ob = some obl)
    (hl : obl.length = 48) (off : Nat) (hoff : off + 8 ≤ 48) (v : Nat) (hv : v < 18446744073709551616) :
    store m (.int u64) (.ptr ob off) (.int u64 v)
      = .ok (m.upd ob (obl.take off ++ encodeLE 8 v ++ obl.drop (off + 8))) := by
  have hbytes : IntTy.bytes ⟨64, false⟩ = 8 := rfl
  have hlen : (encodeLE 8 v).length = 8 := encodeLE_length 8 v
  simp only [store, writeBytes, hm, hbytes, hlen]
  rw [ite_true, if_pos (by rw [hl]; omega)]

/-- A `store` at a struct field with static offset into a 48-byte block:
    `encodeLE` of the value is spliced at `off`. -/
theorem store_field_u32 (m : Mem) (ob : Nat) (obl : List UInt8) (hm : m ob = some obl)
    (hl : obl.length = 48) (off : Nat) (hoff : off + 4 ≤ 48) (v : Nat) (hv : v < 4294967296) :
    store m (.int u32) (.ptr ob off) (.int u32 v)
      = .ok (m.upd ob (obl.take off ++ encodeLE 4 v ++ obl.drop (off + 4))) := by
  have hbytes : IntTy.bytes ⟨32, false⟩ = 4 := rfl
  have hlen : (encodeLE 4 v).length = 4 := encodeLE_length 4 v
  simp only [store, writeBytes, hm, hbytes, hlen]
  rw [ite_true, if_pos (by rw [hl]; omega)]

theorem store_field_u16 (m : Mem) (ob : Nat) (obl : List UInt8) (hm : m ob = some obl)
    (hl : obl.length = 48) (off : Nat) (hoff : off + 2 ≤ 48) (v : Nat) (hv : v < 65536) :
    store m (.int u16) (.ptr ob off) (.int u16 v)
      = .ok (m.upd ob (obl.take off ++ encodeLE 2 v ++ obl.drop (off + 2))) := by
  have hbytes : IntTy.bytes ⟨16, false⟩ = 2 := rfl
  have hlen : (encodeLE 2 v).length = 2 := encodeLE_length 2 v
  simp only [store, writeBytes, hm, hbytes, hlen]
  rw [ite_true, if_pos (by rw [hl]; omega)]

theorem store_field_u8 (m : Mem) (ob : Nat) (obl : List UInt8) (hm : m ob = some obl)
    (hl : obl.length = 48) (off : Nat) (hoff : off + 1 ≤ 48) (v : Nat) (hv : v < 256) :
    store m (.int u8) (.ptr ob off) (.int u8 v)
      = .ok (m.upd ob (obl.take off ++ encodeLE 1 v ++ obl.drop (off + 1))) := by
  have hbytes : IntTy.bytes ⟨8, false⟩ = 1 := rfl
  have hlen : (encodeLE 1 v).length = 1 := encodeLE_length 1 v
  simp only [store, writeBytes, hm, hbytes, hlen]
  rw [ite_true, if_pos (by rw [hl]; omega)]

/-- `&bytes[k]` for a constant index `k` (a pointer into the block). -/
theorem ev_ptr_const {s : State} {bd : Nat} {d : List UInt8} {k : Nat}
    (hm : s.mem bd = some d) (hl : s.locals 0 = some (.ptr bd 0)) (hk : k ≤ d.length)
    (hkb : k < 2147483648) :
    EvE Gen.prog s (.index (.var 0) (.const (.int i32 k)) 1) (.ptr bd k) := by
  have hbase : EvE Gen.prog s (.var 0) (.ptr bd 0) := EvE.var hl
  have hidx : EvE Gen.prog s (.const (.int i32 k)) (.int i32 k) := EvE.const _
  refine EvE.index hbase hidx ?_
  rw [if_pos (show i32.signed = true from rfl), toInt_i32_small hkb]
  simp only [ptrAdd, hm]
  rw [if_pos (by omega), show (((0 : Nat) : Int) + (k : Int) * ((1 : Nat) : Int)).toNat = k by omega]

/-- `(int)bytes[k]` for a constant index `k` into a byte block. -/
theorem ev_byte_const {s : State} {bd : Nat} {d : List UInt8} {k : Nat}
    (hm : s.mem bd = some d) (hl : s.locals 0 = some (.ptr bd 0)) (hk : k < d.length)
    (hkb : k < 2147483648) :
    EvE Gen.prog s (.cast i32 (.load (.int u8) (.index (.var 0) (.const (.int i32 k)) 1)))
      (.int i32 (byteAt d k)) := by
  have hp : EvE Gen.prog s (.index (.var 0) (.const (.int i32 k)) 1) (.ptr bd k) :=
    ev_ptr_const hm hl (by omega) hkb
  have hload : EvE Gen.prog s (.load (.int u8) (.index (.var 0) (.const (.int i32 k)) 1))
      (.int u8 (byteAt d k)) :=
    EvE.load hp (by simp [load, readBytes, hm, Ty.size, IntTy.bytes, show k + 1 ≤ d.length from by omega,
      decodeLE_take_one_drop d k hk])
  refine EvE.cast hload ?_
  have := byteAt_lt d k
  have hmod : (⟨32, true⟩ : IntTy).modulus = 4294967296 := rfl
  show Res.ok (Val.int i32 (byteAt d k % (⟨32, true⟩ : IntTy).modulus)) = Res.ok (Val.int i32 (byteAt d k))
  rw [hmod, Nat.mod_eq_of_lt (show byteAt d k < 4294967296 by omega)]




theorem ptrAddN_ok {m : Mem} {b o k : Nat} {blk : Block} (hm : m b = some blk)
    (hk : o + k ≤ blk.length) : ptrAddN m (.ptr b o) k = .ok (.ptr b (o + k)) := by
  simp [ptrAddN, hm, ite_eq_left_iff]
  omega

/-- Five fixed-offset stores into the 48-byte `ni_bmp_info` block: strengthened
    form also pins down the final block in the returned state. -/
theorem bmp_stores_exs (m : Mem) (obl : List UInt8) (hob : m 3 = some obl) (h48 : obl.length = 48)
    (ro : Bool) (hro : ro = false)
    (l : Locals)
    (hl2 : l 2 = some (.ptr 3 0))
    (w h : Nat) (hw : w < 4294967296) (hh : h < 4294967296)
    (hl8 : l 8 = some (.int ⟨32, false⟩ w))
    (hl9 : l 9 = some (.int ⟨32, false⟩ h))
    (b : Nat) (hb : b < 65536)
    (hl6 : l 6 = some (.int ⟨16, false⟩ b))
    (c t : Nat) (hc : c < 256) (ht : t < 256)
    (hl10 : l 10 = some (.int ⟨8, false⟩ c))
    (hl11 : l 11 = some (.int ⟨8, false⟩ t)) :
    ∃ s', ExS Gen.prog ⟨l, m, ro⟩
      (.seq (.store (.int ⟨32, false⟩) (.field (.var 2) 24) (.var 8))
      (.seq (.store (.int ⟨32, false⟩) (.field (.var 2) 28) (.var 9))
      (.seq (.store (.int ⟨16, false⟩) (.field (.var 2) 40) (.var 6))
      (.seq (.store (.int ⟨8, false⟩) (.field (.var 2) 42) (.var 10))
            (.seq (.store (.int ⟨8, false⟩) (.field (.var 2) 43) (.var 11))
                  (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 0)))))))))
      (Outcome.ret (some (.int ⟨32, true⟩ 0))) s' ∧
    s'.mem 3 = some (bmpTailBlock obl w h b c t) := by
  have h2 : EvE Gen.prog ⟨l, m, ro⟩ (.var 2) (.ptr 3 0) := EvE.var hl2
  have h8 : EvE Gen.prog ⟨l, m, ro⟩ (.var 8) (.int ⟨32, false⟩ w) := EvE.var hl8
  have h9 : EvE Gen.prog ⟨l, m, ro⟩ (.var 9) (.int ⟨32, false⟩ h) := EvE.var hl9
  have h6 : EvE Gen.prog ⟨l, m, ro⟩ (.var 6) (.int ⟨16, false⟩ b) := EvE.var hl6
  have h10 : EvE Gen.prog ⟨l, m, ro⟩ (.var 10) (.int ⟨8, false⟩ c) := EvE.var hl10
  have h11 : EvE Gen.prog ⟨l, m, ro⟩ (.var 11) (.int ⟨8, false⟩ t) := EvE.var hl11
  have hr24 : EvE Gen.prog ⟨l, m, ro⟩ (.field (.var 2) 24) (.ptr 3 24) :=
    EvE.field h2 (ptrAddN_ok hob (by omega))
  have hW : ExS Gen.prog ⟨l, m, ro⟩ (.store (.int ⟨32, false⟩) (.field (.var 2) 24) (.var 8)) .normal
      { locals := l, mem := m.upd 3 (obl.take 24 ++ encodeLE 4 w ++ obl.drop 28), ro := ro } :=
    ExS.store hr24 h8 hro
      (store_field_u32 m 3 obl hob h48 24 (by omega) w hw)
  let b1 : List UInt8 := obl.take 24 ++ encodeLE 4 w ++ obl.drop 28
  have hb1 : b1.length = 48 := by simp [b1, h48, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have h2m1 : (m.upd 3 b1) 3 = some b1 := rfl
  let s1 : State := { locals := l, mem := m.upd 3 b1, ro := ro }
  have h2s : EvE Gen.prog s1 (.var 2) (.ptr 3 0) := EvE.var hl2
  have h8s : EvE Gen.prog s1 (.var 8) (.int ⟨32, false⟩ w) := EvE.var hl8
  have h9s : EvE Gen.prog s1 (.var 9) (.int ⟨32, false⟩ h) := EvE.var hl9
  have h6s : EvE Gen.prog s1 (.var 6) (.int ⟨16, false⟩ b) := EvE.var hl6
  have h10s : EvE Gen.prog s1 (.var 10) (.int ⟨8, false⟩ c) := EvE.var hl10
  have h11s : EvE Gen.prog s1 (.var 11) (.int ⟨8, false⟩ t) := EvE.var hl11
  have hr28 : EvE Gen.prog s1 (.field (.var 2) 28) (.ptr 3 28) :=
    EvE.field h2s (ptrAddN_ok h2m1 (by omega))
  have hH : ExS Gen.prog s1 (.store (.int ⟨32, false⟩) (.field (.var 2) 28) (.var 9)) .normal
      { s1 with mem := (m.upd 3 b1).upd 3 (b1.take 28 ++ encodeLE 4 h ++ b1.drop 32) } :=
    ExS.store hr28 h9s hro
      (store_field_u32 (m.upd 3 b1) 3 b1 h2m1 hb1 28 (by omega) h hh)
  let b2 : List UInt8 := b1.take 28 ++ encodeLE 4 h ++ b1.drop 32
  have hb2 : b2.length = 48 := by simp [b2, hb1, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have h2m2 : ((m.upd 3 b1).upd 3 b2) 3 = some b2 := rfl
  let s2 : State := { s1 with mem := (m.upd 3 b1).upd 3 b2 }
  have h2s2 : EvE Gen.prog s2 (.var 2) (.ptr 3 0) := EvE.var hl2
  have h9s2 : EvE Gen.prog s2 (.var 9) (.int ⟨32, false⟩ h) := EvE.var hl9
  have h6s2 : EvE Gen.prog s2 (.var 6) (.int ⟨16, false⟩ b) := EvE.var hl6
  have h10s2 : EvE Gen.prog s2 (.var 10) (.int ⟨8, false⟩ c) := EvE.var hl10
  have h11s2 : EvE Gen.prog s2 (.var 11) (.int ⟨8, false⟩ t) := EvE.var hl11
  have hr40 : EvE Gen.prog s2 (.field (.var 2) 40) (.ptr 3 40) :=
    EvE.field h2s2 (ptrAddN_ok h2m2 (by omega))
  have hBP : ExS Gen.prog s2 (.store (.int ⟨16, false⟩) (.field (.var 2) 40) (.var 6)) .normal
      { s2 with mem := ((m.upd 3 b1).upd 3 b2).upd 3 (b2.take 40 ++ encodeLE 2 b ++ b2.drop 42) } :=
    ExS.store hr40 h6s2 hro
      (store_field_u16 ((m.upd 3 b1).upd 3 b2) 3 b2 h2m2 hb2 40 (by omega) b hb)
  let b3 : List UInt8 := b2.take 40 ++ encodeLE 2 b ++ b2.drop 42
  have hb3 : b3.length = 48 := by simp [b3, hb2, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have h2m3 : (((m.upd 3 b1).upd 3 b2).upd 3 b3) 3 = some b3 := rfl
  let s3 : State := { s2 with mem := ((m.upd 3 b1).upd 3 b2).upd 3 b3 }
  have h2s3 : EvE Gen.prog s3 (.var 2) (.ptr 3 0) := EvE.var hl2
  have h6s3 : EvE Gen.prog s3 (.var 6) (.int ⟨16, false⟩ b) := EvE.var hl6
  have h10s3 : EvE Gen.prog s3 (.var 10) (.int ⟨8, false⟩ c) := EvE.var hl10
  have h11s3 : EvE Gen.prog s3 (.var 11) (.int ⟨8, false⟩ t) := EvE.var hl11
  have hr42 : EvE Gen.prog s3 (.field (.var 2) 42) (.ptr 3 42) :=
    EvE.field h2s3 (ptrAddN_ok h2m3 (by omega))
  have hCH : ExS Gen.prog s3 (.store (.int ⟨8, false⟩) (.field (.var 2) 42) (.var 10)) .normal
      { s3 with mem := (((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 (b3.take 42 ++ encodeLE 1 c ++ b3.drop 43) } :=
    ExS.store hr42 h10s3 hro
      (store_field_u8 _ 3 b3 h2m3 hb3 42 (by omega) c hc)
  let b4 : List UInt8 := b3.take 42 ++ encodeLE 1 c ++ b3.drop 43
  have hb4 : b4.length = 48 := by simp [b4, hb3, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have h2m4 : ((((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4) 3 = some b4 := rfl
  let s4 : State := { s3 with mem := (((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4 }
  have h2s4 : EvE Gen.prog s4 (.var 2) (.ptr 3 0) := EvE.var hl2
  have h11s4 : EvE Gen.prog s4 (.var 11) (.int ⟨8, false⟩ t) := EvE.var hl11
  have hr43 : EvE Gen.prog s4 (.field (.var 2) 43) (.ptr 3 43) :=
    EvE.field h2s4 (ptrAddN_ok h2m4 (by omega))
  have hTD : ExS Gen.prog s4 (.store (.int ⟨8, false⟩) (.field (.var 2) 43) (.var 11)) .normal
      { s4 with mem := (((((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 (b4.take 43 ++ encodeLE 1 t ++ b4.drop 44)) } :=
    ExS.store hr43 h11s4 hro
      (store_field_u8 _ 3 b4 h2m4 hb4 43 (by omega) t ht)
  have hret : ExS Gen.prog
      { s4 with mem := (((((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 (b4.take 43 ++ encodeLE 1 t ++ b4.drop 44)) }
      (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 0))))
      (Outcome.ret (some (.int ⟨32, true⟩ 0)))
      { s4 with mem := (((((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 (b4.take 43 ++ encodeLE 1 t ++ b4.drop 44)) } :=
    ExS.ret (EvE.const (v := (.int ⟨32, true⟩ 0)))
  have hb1' : b1 = obl.take 24 ++ encodeLE 4 w ++ obl.drop 28 := rfl
  have hb2' : b2 = b1.take 28 ++ encodeLE 4 h ++ b1.drop 32 := rfl
  have hb3' : b3 = b2.take 40 ++ encodeLE 2 b ++ b2.drop 42 := rfl
  have hb4' : b4 = b3.take 42 ++ encodeLE 1 c ++ b3.drop 43 := rfl
  have hblk : (b4.take 43 ++ encodeLE 1 t ++ b4.drop 44) = bmpTailBlock obl w h b c t :=
    stores_block_eq obl h48 w h b c t b1 hb1' b2 hb2' b3 hb3' b4 hb4'
  have hfin : (((((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 (b4.take 43 ++ encodeLE 1 t ++ b4.drop 44))
      = m.upd 3 (bmpTailBlock obl w h b c t) := by
    rw [mem_upd_same, mem_upd_same, mem_upd_same, mem_upd_same]
    rw [hblk]
  have hmem : ({ s4 with mem := (((((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 (b4.take 43 ++ encodeLE 1 t ++ b4.drop 44)) } : State).mem 3
      = some (bmpTailBlock obl w h b c t) := by
    rw [hfin]
    rfl
  refine ⟨{ s4 with mem := (((((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 (b4.take 43 ++ encodeLE 1 t ++ b4.drop 44)) },
    ExS.seq hW (ExS.seq hH (ExS.seq hBP (ExS.seq hCH (ExS.seq hTD hret)))), hmem⟩

/-- The 48-byte `ni_bmp_info` block when `ni_bmp_geometry` succeeds: depends on
    the sign of `heightI` (the value stored at @28) and on `channels`
    (`bit_count == 32 ? 4 : 3`). -/
def geomOutBlock (obl d : List UInt8) : List UInt8 :=
  if (NANO.toInt32 (rd32le d 22) : Int) ≥ 0 then
    bmpTailBlock obl (rd32le d 18) (rd32le d 22) (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3) 0
  else if NANO.toInt32 (rd32le d 22) = -2147483648 then
    bmpTailBlock obl (rd32le d 18) 2147483648 (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3) 1
  else
    bmpTailBlock obl (rd32le d 18)
      (IntTy.wrap ⟨32, true⟩ (-(IntTy.toInt ⟨32, true⟩ (rd32le d 22))))
      (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3) 1

theorem geomOutBlock_pos (obl d : List UInt8) (hPos : (NANO.toInt32 (rd32le d 22) : Int) ≥ 0) :
    geomOutBlock obl d = bmpTailBlock obl (rd32le d 18) (rd32le d 22) (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) 0 := by
  rw [geomOutBlock]; rw [if_pos hPos]

theorem geomOutBlock_intmin (obl d : List UInt8) (hNeg : (NANO.toInt32 (rd32le d 22) : Int) < 0)
    (hInMin : NANO.toInt32 (rd32le d 22) = -2147483648) :
    geomOutBlock obl d = bmpTailBlock obl (rd32le d 18) 2147483648 (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) 1 := by
  have hfalse : ¬ (NANO.toInt32 (rd32le d 22) : Int) ≥ 0 := by omega
  rw [geomOutBlock]; rw [if_neg hfalse, if_pos hInMin]

theorem geomOutBlock_neg_normal (obl d : List UInt8) (hNeg : (NANO.toInt32 (rd32le d 22) : Int) < 0)
    (hInMin : ¬ (NANO.toInt32 (rd32le d 22) = -2147483648)) :
    geomOutBlock obl d = bmpTailBlock obl (rd32le d 18)
      (IntTy.wrap ⟨32, true⟩ (-(IntTy.toInt ⟨32, true⟩ (rd32le d 22))))
      (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3) 1 := by
  have hfalse : ¬ (NANO.toInt32 (rd32le d 22) : Int) ≥ 0 := by omega
  rw [geomOutBlock]; rw [if_neg hfalse, if_neg hInMin]

/-- Tail of `ni_bmp_geometry`: `set8`, comp≠0 → ret5, bit∉ valid → ret6,
    otherwise channels → `set10`, five stores, `ret 0`. Parameterized by the
    post-LT state `s5B`. -/
theorem tail_exs (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hd : 34 ≤ d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : m 3 = some obl) (h48 : obl.length = 48) (ro : Bool)
    (hro : ro = false)
    (heightU : Nat) (hhU : heightU < 4294967296)
    (topD : Nat) (htopd : topD < 256)
    (hgt : NANO.toInt32 (rd32le d 18) > 0)
    (hh0 : NANO.toInt32 (rd32le d 22) ≠ 0)
    (hPl : rd16le d 26 = 1)
    (hIntmin : NANO.toInt32 (rd32le d 22) ≠ -2147483648) :
    ∃ s' code, ExS Gen.prog
      { locals := ((frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0]).upd 3 (.int ⟨32, true⟩ (rd32le d 18))
                |>.upd 4 (.int ⟨32, true⟩ (rd32le d 22))
                |>.upd 5 (.int ⟨16, false⟩ (rd16le d 26))
                |>.upd 6 (.int ⟨16, false⟩ (rd16le d 28))
                |>.upd 7 (.int ⟨32, false⟩ (rd32le d 30))
                |>.upd 11 (.int ⟨8, false⟩ topD)
                |>.upd 9 (.int ⟨32, false⟩ heightU)),
        mem := m, ro := ro }
      (.seq (.set 8 (.cast ⟨32, false⟩ (.var 3)))
      (.seq (.ite (.bin .ne (some ⟨32, false⟩) (.var 7) (.const (.int ⟨32, false⟩ 0)))
                  (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 5)))) .skip)
      (.seq (.ite (.land (.land (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
                                (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24))))
                         (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32))))
                  (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 6)))) .skip)
      (.seq (.set 10 (.cast ⟨8, false⟩ (.cond (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
                                               (.const (.int ⟨32, false⟩ 4)) (.const (.int ⟨32, false⟩ 3)))))
      (.seq (.store (.int ⟨32, false⟩) (.field (.var 2) 24) (.var 8))
      (.seq (.store (.int ⟨32, false⟩) (.field (.var 2) 28) (.var 9))
      (.seq (.store (.int ⟨16, false⟩) (.field (.var 2) 40) (.var 6))
      (.seq (.store (.int ⟨8, false⟩) (.field (.var 2) 42) (.var 10))
            (.seq (.store (.int ⟨8, false⟩) (.field (.var 2) 43) (.var 11))
                  (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 0)))))))))))))
      (Outcome.ret (some (.int ⟨32, true⟩ code))) s' ∧
    code = bmpGeometryCode d ∧
    (∀ (hb : code = 0), s'.mem 3 = some (bmpTailBlock obl (rd32le d 18) heightU (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) topD)) := by
  let s5B : State :=
    { locals := ((frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0]).upd 3 (.int ⟨32, true⟩ (rd32le d 18))
                |>.upd 4 (.int ⟨32, true⟩ (rd32le d 22))
                |>.upd 5 (.int ⟨16, false⟩ (rd16le d 26))
                |>.upd 6 (.int ⟨16, false⟩ (rd16le d 28))
                |>.upd 7 (.int ⟨32, false⟩ (rd32le d 30))
                |>.upd 11 (.int ⟨8, false⟩ topD)
                |>.upd 9 (.int ⟨32, false⟩ heightU)),
      mem := m, ro := ro }
  have hl3 : s5B.locals 3 = some (.int ⟨32, true⟩ (rd32le d 18)) := rfl
  have hl6 : s5B.locals 6 = some (.int ⟨16, false⟩ (rd16le d 28)) := rfl
  have hl7 : s5B.locals 7 = some (.int ⟨32, false⟩ (rd32le d 30)) := rfl
  have hl2 : s5B.locals 2 = some (.ptr 3 0) := rfl
  have hl9 : s5B.locals 9 = some (.int ⟨32, false⟩ heightU) := rfl
  have hl11 : s5B.locals 11 = some (.int ⟨8, false⟩ topD) := rfl
  have hv3 : EvE Gen.prog s5B (.var 3) (.int ⟨32, true⟩ (rd32le d 18)) := EvE.var hl3
  have cast8 : EvE Gen.prog s5B (.cast ⟨32, false⟩ (.var 3)) (.int ⟨32, false⟩ (rd32le d 18)) :=
    EvE.cast hv3 (cast_u32_i32 (rd32le d 18) (rd32_lt d 18))
  have hSet8 : ExS Gen.prog s5B
      (.set 8 (.cast ⟨32, false⟩ (.var 3)))
      .normal
      { s5B with locals := s5B.locals.upd 8 (.int ⟨32, false⟩ (rd32le d 18)) } :=
    ExS.set cast8
  let s5C : State := { s5B with locals := s5B.locals.upd 8 (.int ⟨32, false⟩ (rd32le d 18)) }
  have hv7 : EvE Gen.prog s5C (.var 7) (.int ⟨32, false⟩ (rd32le d 30)) := by
    have e : s5C.locals 7 = some (.int ⟨32, false⟩ (rd32le d 30)) := by
      show (s5B.locals.upd 8 (.int ⟨32, false⟩ (rd32le d 18))) 7 = _
      rw [Locals.upd_ne _ _ (by omega : 7 ≠ 8)]
      exact hl7
    exact EvE.var e
  have eCmp : EvE Gen.prog s5C
      (.bin .ne (some ⟨32, false⟩) (.var 7) (.const (.int ⟨32, false⟩ 0)))
      (boolVal (decide (rd32le d 30 ≠ 0))) :=
    EvE.bin hv7 (EvE.const _) (bin_u32_ne _ _)
  by_cases hCmp : rd32le d 30 ≠ 0
  · refine ⟨s5C, 5, ?_⟩
    have eCmpT : EvE Gen.prog s5C
        (.bin .ne (some ⟨32, false⟩) (.var 7) (.const (.int ⟨32, false⟩ 0)))
        (boolVal true) := by
      rwa [decide_eq_true_eq.mpr hCmp] at eCmp
    have hCMPRet : ExS Gen.prog s5C
        (.ite (.bin .ne (some ⟨32, false⟩) (.var 7) (.const (.int ⟨32, false⟩ 0)))
          (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 5)))) .skip)
        (Outcome.ret (some (.int ⟨32, true⟩ 5))) s5C :=
      ExS.ite eCmpT (truthy_boolVal true) (ExS.ret (EvE.const (v := (.int ⟨32, true⟩ 5))))
    have hbv : bmpGeometryCode d = 5 := by
      have hgt' : ¬ (NANO.toInt32 (rd32le d 18) ≤ 0) := by omega
      simp [bmpGeometryCode, hgt', hh0, hPl, hCmp, hIntmin]
    exact ⟨ExS.seq hSet8 (ExS.seq_ret hCMPRet), hbv.symm,
      fun hb => absurd hb (by decide)⟩
  · have eCmpF : EvE Gen.prog s5C
        (.bin .ne (some ⟨32, false⟩) (.var 7) (.const (.int ⟨32, false⟩ 0)))
        (boolVal false) := by
      rw [decide_eq_false_iff_not.mpr (by omega)] at eCmp
      exact eCmp
    have hCmpSkip : ExS Gen.prog s5C
        (.ite (.bin .ne (some ⟨32, false⟩) (.var 7) (.const (.int ⟨32, false⟩ 0)))
          (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 5)))) .skip)
        .normal s5C :=
      ExS.ite eCmpF (truthy_boolVal false) ExS.skip
    -- bit count branch
    have hv6 : EvE Gen.prog s5C (.var 6) (.int ⟨16, false⟩ (rd16le d 28)) := by
      have e : s5C.locals 6 = some (.int ⟨16, false⟩ (rd16le d 28)) := by
        show (s5B.locals.upd 8 (.int ⟨32, false⟩ (rd32le d 18))) 6 = _
        rw [Locals.upd_ne _ _ (by omega : 6 ≠ 8)]
        exact hl6
      exact EvE.var e
    have hu32c6 : EvE Gen.prog s5C (.cast ⟨32, false⟩ (.var 6)) (.int ⟨32, false⟩ (rd16le d 28)) :=
      EvE.cast hv6 (u16_u32_cast (rd16le d 28) (rd16le_lt d 28))
    have eBit8 : EvE Gen.prog s5C
        (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
        (boolVal (decide (rd16le d 28 ≠ 8))) :=
      EvE.bin hu32c6 (EvE.const _) (bin_u32_ne _ _)
    have eBit24 : EvE Gen.prog s5C
        (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24)))
        (boolVal (decide (rd16le d 28 ≠ 24))) :=
      EvE.bin hu32c6 (EvE.const _) (bin_u32_ne _ _)
    have eBit32 : EvE Gen.prog s5C
        (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
        (boolVal (decide (rd16le d 28 ≠ 32))) :=
      EvE.bin hu32c6 (EvE.const _) (bin_u32_ne _ _)
    by_cases hB8 : rd16le d 28 = 8
    · -- bit = 8 → channels = 3, ret 0
      have eB8 : EvE Gen.prog s5C
          (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
          (boolVal false) := by
        have ebits : EvE Gen.prog s5C
            (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
            (boolVal (decide (rd16le d 28 ≠ 8))) := eBit8
        rw [decide_eq_false_iff_not.mpr (by omega : ¬ (rd16le d 28 ≠ 8))] at ebits
        exact ebits
      have t8t : truthy (boolVal false) = .ok false := truthy_boolVal false
      have eInner : EvE Gen.prog s5C
          (.land (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
                 (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24))))
          (boolVal false) :=
        EvE.land_false eB8 t8t
      have eOuter : EvE Gen.prog s5C
          (.land (.land (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
                        (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24))))
                 (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32))))
          (boolVal false) :=
        EvE.land_false eInner t8t
      have hBitSkip : ExS Gen.prog s5C
          (.ite (.land (.land (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
                              (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24))))
                       (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32))))
            (.ret (some (.const (.int ⟨32, true⟩ 6)))) .skip)
          .normal s5C :=
        ExS.ite eOuter t8t ExS.skip
      have ebit32 : EvE Gen.prog s5C
          (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
          (boolVal (decide (rd16le d 28 = 32))) :=
        EvE.bin hu32c6 (EvE.const _) (bin_u32_eq _ _)
      rw [hB8] at ebit32
      have e32F : EvE Gen.prog s5C
          (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
          (boolVal false) := by
        rw [decide_eq_false_iff_not.mpr (by omega : ¬ (8 = 32))] at ebit32
        exact ebit32
      have hCond : EvE Gen.prog s5C
          (.cond (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
                 (.const (.int ⟨32, false⟩ 4))
                 (.const (.int ⟨32, false⟩ 3)))
          (.int ⟨32, false⟩ 3) :=
        EvE.cond e32F (truthy_boolVal false) (EvE.const _)
      have hCast8c : EvE Gen.prog s5C
          (.cast ⟨8, false⟩
            (.cond (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
                   (.const (.int ⟨32, false⟩ 4))
                   (.const (.int ⟨32, false⟩ 3))))
          (.int ⟨8, false⟩ 3) :=
        EvE.cast hCond (by simp [evalCast, IntTy.modulus, IntTy.width])
      have hSet10 : ExS Gen.prog s5C
          (.set 10 (.cast ⟨8, false⟩
            (.cond (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
                   (.const (.int ⟨32, false⟩ 4))
                   (.const (.int ⟨32, false⟩ 3)))))
          .normal
          { s5C with locals := s5C.locals.upd 10 (.int ⟨8, false⟩ 3) } :=
        ExS.set hCast8c
      let s5D : State := { s5C with locals := s5C.locals.upd 10 (.int ⟨8, false⟩ 3) }
      have hl2D : s5D.locals 2 = some (.ptr 3 0) := rfl
      have hl8D : s5D.locals 8 = some (.int ⟨32, false⟩ (rd32le d 18)) := rfl
      have hl9D : s5D.locals 9 = some (.int ⟨32, false⟩ heightU) := rfl
      have hl6D : s5D.locals 6 = some (.int ⟨16, false⟩ (rd16le d 28)) := rfl
      have hl10D : s5D.locals 10 = some (.int ⟨8, false⟩ 3) := rfl
      have hl11D : s5D.locals 11 = some (.int ⟨8, false⟩ topD) := rfl
      obtain ⟨s', hTail, hblk⟩ := bmp_stores_exs m obl hob h48 ro hro s5D.locals hl2D
        (rd32le d 18) heightU (rd32_lt d 18) hhU hl8D hl9D
        (rd16le d 28) (rd16le_lt d 28) hl6D
        3 topD (by omega) htopd hl10D hl11D
      have hblk3 : s'.mem 3 = some (bmpTailBlock obl (rd32le d 18) heightU (rd16le d 28)
          (if rd16le d 28 = 32 then 4 else 3) topD) := by
        rw [show (if rd16le d 28 = 32 then 4 else 3) = 3 from by simp [hB8]]
        exact hblk
      refine ⟨s', 0, ?_⟩
      have hbv : bmpGeometryCode d = 0 := by
        have hgt' : ¬ (NANO.toInt32 (rd32le d 18) ≤ 0) := by omega
        have hcomp : rd32le d 30 = 0 := by omega
        simp [bmpGeometryCode, hgt', hh0, hPl, hcomp, hB8, hIntmin]
      exact ⟨ExS.seq hSet8 (ExS.seq hCmpSkip (ExS.seq hBitSkip (ExS.seq hSet10 hTail))), hbv.symm,
        fun _ => hblk3⟩
    · by_cases hB24 : rd16le d 28 = 24
      · -- bit = 24 → ch=3, ret 0
        have eB8 : EvE Gen.prog s5C
            (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
            (boolVal true) := by
          have ebits : EvE Gen.prog s5C
              (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
              (boolVal (decide (rd16le d 28 ≠ 8))) := eBit8
          rw [decide_eq_true_eq.mpr (by omega)] at ebits
          exact ebits
        have eB24 : EvE Gen.prog s5C
            (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24)))
            (boolVal false) := by
          have ebits : EvE Gen.prog s5C
              (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24)))
              (boolVal (decide (rd16le d 28 ≠ 24))) := eBit24
          rw [decide_eq_false_iff_not.mpr (by omega : ¬ (rd16le d 28 ≠ 24))] at ebits
          exact ebits
        have tt8 : truthy (boolVal true) = .ok true := truthy_boolVal true
        have eInner : EvE Gen.prog s5C
            (.land (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
                   (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24))))
            (boolVal false) :=
          EvE.land_true eB8 tt8 eB24 (truthy_boolVal false)
        have eOuter : EvE Gen.prog s5C
            (.land (.land (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
                          (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24))))
                   (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32))))
            (boolVal false) :=
          EvE.land_false eInner (truthy_boolVal false)
        have hBitSkip : ExS Gen.prog s5C
            (.ite (.land (.land (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
                                (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24))))
                         (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32))))
              (.ret (some (.const (.int ⟨32, true⟩ 6)))) .skip)
            .normal s5C :=
          ExS.ite eOuter (truthy_boolVal false) ExS.skip
        have ebit32 : EvE Gen.prog s5C
            (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
            (boolVal (decide (rd16le d 28 = 32))) :=
          EvE.bin hu32c6 (EvE.const _) (bin_u32_eq _ _)
        rw [hB24] at ebit32
        have e32F : EvE Gen.prog s5C
            (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
            (boolVal false) := by
          rwa [decide_eq_false_iff_not.mpr (by omega : ¬ (24 = 32))] at ebit32
        have hCond : EvE Gen.prog s5C
            (.cond (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
                   (.const (.int ⟨32, false⟩ 4))
                   (.const (.int ⟨32, false⟩ 3)))
            (.int ⟨32, false⟩ 3) :=
          EvE.cond e32F (truthy_boolVal false) (EvE.const _)
        have hCast8c : EvE Gen.prog s5C
            (.cast ⟨8, false⟩
              (.cond (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
                     (.const (.int ⟨32, false⟩ 4))
                     (.const (.int ⟨32, false⟩ 3))))
            (.int ⟨8, false⟩ 3) :=
          EvE.cast hCond (by simp [evalCast, IntTy.modulus, IntTy.width])
        have hSet10 : ExS Gen.prog s5C
            (.set 10 (.cast ⟨8, false⟩
              (.cond (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
                     (.const (.int ⟨32, false⟩ 4))
                     (.const (.int ⟨32, false⟩ 3)))))
            .normal
            { s5C with locals := s5C.locals.upd 10 (.int ⟨8, false⟩ 3) } :=
          ExS.set hCast8c
        let s5D : State := { s5C with locals := s5C.locals.upd 10 (.int ⟨8, false⟩ 3) }
        have hl2D : s5D.locals 2 = some (.ptr 3 0) := rfl
        have hl8D : s5D.locals 8 = some (.int ⟨32, false⟩ (rd32le d 18)) := rfl
        have hl9D : s5D.locals 9 = some (.int ⟨32, false⟩ heightU) := rfl
        have hl6D : s5D.locals 6 = some (.int ⟨16, false⟩ (rd16le d 28)) := rfl
        have hl10D : s5D.locals 10 = some (.int ⟨8, false⟩ 3) := rfl
        have hl11D : s5D.locals 11 = some (.int ⟨8, false⟩ topD) := rfl
        obtain ⟨s', hTail, hblk⟩ := bmp_stores_exs m obl hob h48 ro hro s5D.locals hl2D
          (rd32le d 18) heightU (rd32_lt d 18) hhU hl8D hl9D
          (rd16le d 28) (rd16le_lt d 28) hl6D
          3 topD (by omega) htopd hl10D hl11D
        have hblk3 : s'.mem 3 = some (bmpTailBlock obl (rd32le d 18) heightU (rd16le d 28)
            (if rd16le d 28 = 32 then 4 else 3) topD) := by
          rw [show (if rd16le d 28 = 32 then 4 else 3) = 3 from by simp [hB24]]
          exact hblk
        refine ⟨s', 0, ?_⟩
        have hbv : bmpGeometryCode d = 0 := by
          have hgt' : ¬ (NANO.toInt32 (rd32le d 18) ≤ 0) := by omega
          have hcomp : rd32le d 30 = 0 := by omega
          simp [bmpGeometryCode, hgt', hh0, hPl, hcomp, hB24, hIntmin]
        exact ⟨ExS.seq hSet8 (ExS.seq hCmpSkip (ExS.seq hBitSkip (ExS.seq hSet10 hTail))), hbv.symm,
          fun _ => hblk3⟩
      · by_cases hB32 : rd16le d 28 = 32
        · -- bit = 32 → ch=4, ret 0
          have eB8 : EvE Gen.prog s5C
              (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
              (boolVal true) := by
            have ebits : EvE Gen.prog s5C
                (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
                (boolVal (decide (rd16le d 28 ≠ 8))) := eBit8
            rw [decide_eq_true_eq.mpr (by omega)] at ebits
            exact ebits
          have eB24 : EvE Gen.prog s5C
              (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24)))
              (boolVal true) := by
            have ebits : EvE Gen.prog s5C
                (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24)))
                (boolVal (decide (rd16le d 28 ≠ 24))) := eBit24
            rw [decide_eq_true_eq.mpr (by omega)] at ebits
            exact ebits
          have eB32 : EvE Gen.prog s5C
              (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
              (boolVal false) := by
            have ebits : EvE Gen.prog s5C
                (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
                (boolVal (decide (rd16le d 28 ≠ 32))) := eBit32
            rw [decide_eq_false_iff_not.mpr (by omega : ¬ (rd16le d 28 ≠ 32))] at ebits
            exact ebits
          have tt8 : truthy (boolVal true) = .ok true := truthy_boolVal true
          have eInner : EvE Gen.prog s5C
              (.land (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
                     (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24))))
              (boolVal true) :=
            EvE.land_true eB8 tt8 eB24 tt8
          have eOuter : EvE Gen.prog s5C
              (.land (.land (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
                            (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24))))
                     (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32))))
              (boolVal false) :=
            EvE.land_true eInner (truthy_boolVal true) eB32 (truthy_boolVal false)
          have hBitSkip : ExS Gen.prog s5C
              (.ite (.land (.land (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
                                  (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24))))
                           (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32))))
                (.ret (some (.const (.int ⟨32, true⟩ 6)))) .skip)
              .normal s5C :=
            ExS.ite eOuter (truthy_boolVal false) ExS.skip
          have ebit32 : EvE Gen.prog s5C
              (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
              (boolVal (decide (rd16le d 28 = 32))) :=
            EvE.bin hu32c6 (EvE.const _) (bin_u32_eq _ _)
          rw [hB32] at ebit32
          have e32T : EvE Gen.prog s5C
              (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
              (boolVal true) := by
            rwa [decide_eq_true_eq.mpr (by omega : (32 : Nat) = 32)] at ebit32
          have hCond : EvE Gen.prog s5C
              (.cond (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
                     (.const (.int ⟨32, false⟩ 4))
                     (.const (.int ⟨32, false⟩ 3)))
              (.int ⟨32, false⟩ 4) :=
            EvE.cond e32T (truthy_boolVal true) (EvE.const _)
          have hCast8c : EvE Gen.prog s5C
              (.cast ⟨8, false⟩
                (.cond (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
                       (.const (.int ⟨32, false⟩ 4))
                       (.const (.int ⟨32, false⟩ 3))))
              (.int ⟨8, false⟩ 4) :=
            EvE.cast hCond (by simp [evalCast, IntTy.modulus, IntTy.width])
          have hSet10 : ExS Gen.prog s5C
              (.set 10 (.cast ⟨8, false⟩
                (.cond (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
                       (.const (.int ⟨32, false⟩ 4))
                       (.const (.int ⟨32, false⟩ 3)))))
              .normal
              { s5C with locals := s5C.locals.upd 10 (.int ⟨8, false⟩ 4) } :=
            ExS.set hCast8c
          let s5D : State := { s5C with locals := s5C.locals.upd 10 (.int ⟨8, false⟩ 4) }
          have hl2D : s5D.locals 2 = some (.ptr 3 0) := rfl
          have hl8D : s5D.locals 8 = some (.int ⟨32, false⟩ (rd32le d 18)) := rfl
          have hl9D : s5D.locals 9 = some (.int ⟨32, false⟩ heightU) := rfl
          have hl6D : s5D.locals 6 = some (.int ⟨16, false⟩ (rd16le d 28)) := rfl
          have hl10D : s5D.locals 10 = some (.int ⟨8, false⟩ 4) := rfl
          have hl11D : s5D.locals 11 = some (.int ⟨8, false⟩ topD) := rfl
          obtain ⟨s', hTail, hblk⟩ := bmp_stores_exs m obl hob h48 ro hro s5D.locals hl2D
            (rd32le d 18) heightU (rd32_lt d 18) hhU hl8D hl9D
            (rd16le d 28) (rd16le_lt d 28) hl6D
            4 topD (by omega) htopd hl10D hl11D
          have hblk3 : s'.mem 3 = some (bmpTailBlock obl (rd32le d 18) heightU (rd16le d 28)
              (if rd16le d 28 = 32 then 4 else 3) topD) := by
            rw [show (if rd16le d 28 = 32 then 4 else 3) = 4 from by simp [hB32]]
            exact hblk
          refine ⟨s', 0, ?_⟩
          have hbv : bmpGeometryCode d = 0 := by
            have hgt' : ¬ (NANO.toInt32 (rd32le d 18) ≤ 0) := by omega
            have hcomp : rd32le d 30 = 0 := by omega
            simp [bmpGeometryCode, hgt', hh0, hPl, hcomp, hB32, hIntmin]
          exact ⟨ExS.seq hSet8 (ExS.seq hCmpSkip (ExS.seq hBitSkip (ExS.seq hSet10 hTail))), hbv.symm,
            fun _ => hblk3⟩
        · -- invalid bit → ret 6
          have hb8 : rd16le d 28 ≠ 8 ∧ rd16le d 28 ≠ 24 ∧ rd16le d 28 ≠ 32 :=
            ⟨hB8, hB24, hB32⟩
          have eB8 : EvE Gen.prog s5C
              (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
              (boolVal true) := by
            rwa [decide_eq_true_eq.mpr hb8.1] at eBit8
          have eB24 : EvE Gen.prog s5C
              (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24)))
              (boolVal true) := by
            rwa [decide_eq_true_eq.mpr hb8.2.1] at eBit24
          have eB32 : EvE Gen.prog s5C
              (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32)))
              (boolVal true) := by
            rwa [decide_eq_true_eq.mpr hb8.2.2] at eBit32
          have ttB : truthy (boolVal true) = .ok true := truthy_boolVal true
          have eInner : EvE Gen.prog s5C
              (.land (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
                     (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24))))
              (boolVal true) :=
            EvE.land_true eB8 ttB eB24 ttB
          have eOuter : EvE Gen.prog s5C
              (.land (.land (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
                            (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24))))
                     (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32))))
              (boolVal true) :=
            EvE.land_true eInner (truthy_boolVal true) eB32 ttB
          have hBitRet6 : ExS Gen.prog s5C
              (.ite (.land (.land (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 8)))
                                  (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 24))))
                           (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 32))))
                (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 6)))) .skip)
              (Outcome.ret (some (.int ⟨32, true⟩ 6))) s5C :=
            ExS.ite eOuter (truthy_boolVal true) (ExS.ret (EvE.const (v := (.int ⟨32, true⟩ 6))))
          have hbv : bmpGeometryCode d = 6 := by
            have hgt' : ¬ (NANO.toInt32 (rd32le d 18) ≤ 0) := by omega
            have hcomp : rd32le d 30 = 0 := by omega
            simp [bmpGeometryCode, hgt', hh0, hPl, hcomp, hb8.1, hb8.2.1, hb8.2.2, hIntmin]
          exact ⟨s5C, 6, ⟨ExS.seq hSet8 (ExS.seq hCmpSkip (ExS.seq_ret hBitRet6)), hbv.symm,
            fun hb => absurd hb (by decide)⟩⟩

theorem wrap_i32_lt (z : Int) : IntTy.wrap ⟨32, true⟩ z < 4294967296 := by
  simp [IntTy.wrap, IntTy.modulus, IntTy.width]
  have h := Int.emod_lt_of_pos z (show (4294967296 : Int) > 0 by decide)
  have h2 := Int.emod_nonneg z (show (4294967296 : Int) ≠ 0 by decide)
  omega

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- Channels from bit-depth are at most 4. -/
theorem channels_le_4 (bc : Nat) : (if bc = 32 then 4 else 3) ≤ 4 := by
  by_cases h : bc = 32
  · rw [if_pos h]; decide
  · rw [if_neg h]; omega

/-- Channels from bit-depth are positive. -/
theorem channels_ge_1 (bc : Nat) : 1 ≤ (if bc = 32 then 4 else 3) := by
  by_cases h : bc = 32
  · rw [if_pos h]; decide
  · rw [if_neg h]; decide

/-- Channels from bit-depth are < 256. -/
theorem channels_lt_256 (bc : Nat) : (if bc = 32 then 4 else 3) < 256 := by
  have := channels_le_4 bc; omega

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- The resulting 48-byte block after the 10-store epilogue (splices the
    `ni_bmp_info` fields into the initial block at the C layout offsets). -/
def niInfoBlock (obl : Block) (rowStride outSize paletteOffset width height pixelOffset paletteEntries bitCount channels topDown : Nat) : Block :=
  let b1 := obl.take 0 ++ encodeLE 8 rowStride ++ obl.drop 8
  let b2 := b1.take 8 ++ encodeLE 8 outSize ++ b1.drop 16
  let b3 := b2.take 16 ++ encodeLE 8 paletteOffset ++ b2.drop 24
  let b4 := b3.take 24 ++ encodeLE 4 width ++ b3.drop 28
  let b5 := b4.take 28 ++ encodeLE 4 height ++ b4.drop 32
  let b6 := b5.take 32 ++ encodeLE 4 pixelOffset ++ b5.drop 36
  let b7 := b6.take 36 ++ encodeLE 4 paletteEntries ++ b6.drop 40
  let b8 := b7.take 40 ++ encodeLE 2 bitCount ++ b7.drop 42
  let b9 := b8.take 42 ++ encodeLE 1 channels ++ b8.drop 43
  let b10 := b9.take 43 ++ encodeLE 1 topDown ++ b9.drop 44
  b10

end NANO.C.Proofs
