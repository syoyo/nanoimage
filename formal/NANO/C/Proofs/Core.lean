/-
  Phase 1 proofs: the shared scalar helpers of the nanoimage verified core
  refine their specifications (`NANO.Spec`). Pattern follows the reference
  formalization (`T1` proofs): for every input the translated C terminates
  without undefined behaviour, returns the specified value, and writes only
  the caller-provided outputs.
-/
import NANO.C.Gen
import NANO.C.Hoare
import NANO.C.Lemmas
import NANO.Spec

set_option linter.unusedSimpArgs false

namespace NANO.C.Proofs
open NANO NANO.C

abbrev u8 : IntTy := ⟨8, false⟩
abbrev u16 : IntTy := ⟨16, false⟩
abbrev u32 : IntTy := ⟨32, false⟩
abbrev i32 : IntTy := ⟨32, true⟩
abbrev u64 : IntTy := ⟨64, false⟩

theorem ni_read_u16le_exs (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d) (o : Nat)
    (ho : o + 2 ≤ d.length) (hl : d.length < 2 ^ 64) (ro : Bool) :
    ExS Gen.prog ⟨frameLocals [0] [.ptr bd o], m, ro⟩ Gen.ni_read_u16le.body
      (.ret (some (.int u16 (rd16le d o)))) ⟨frameLocals [0] [.ptr bd o], m, ro⟩ := by
  refine ExS.of_eq 30 (fun n => ?_)
  have l1 : o + 1 < 2 ^ 64 := by omega
  have h1 : o < d.length := by omega
  have h2 : o + 1 < d.length := by omega
  simp [Gen.ni_read_u16le, execStmt, evalExpr, frameLocals, evalBin, isPtr, ptrEq, evalBinInt, binInt, evalCast, intOf, load,
    readBytes, hm, ptrAddN, ptrAdd, List.idxOf?, List.findIdx?, List.findIdx?.go, IntTy.u64, IntTy.u32, IntTy.u16, IntTy.u8,
    arith, IntTy.inRange, IntTy.toInt, Ty.size, IntTy.bytes, IntTy.modulus, l1, Nat.mod_eq_of_lt, C.guard,
    decodeLE_take_one_drop, h1, h2, rd16le_or,
    (by omega : o ≤ d.length), (by omega : o + 1 ≤ d.length),
    (by omega : (o : Int) + 1 ≤ (d.length : Int)), (by omega : 0 ≤ (o : Int) + 1),
    (by omega : o + 1 + 1 ≤ d.length),
    (by have := byteAt_lt d o; omega : byteAt d o % 65536 % 4294967296 = byteAt d o),
    (by have := byteAt_lt d (o + 1); omega : byteAt d (o + 1) % 65536 % 4294967296 = byteAt d (o + 1)),
    (show ¬ ((↑(byteAt d (o + 1)) : Int) < 0) by have := byteAt_lt d (o + 1); omega),
    (show ¬ (2147483648 ≤ byteAt d (o + 1)) by have := byteAt_lt d (o + 1); omega),
    (show ¬ (2147483648 ≤ byteAt d o) by have := byteAt_lt d o; omega),
    (show (IntTy.mk 32 true).minVal ≤ (↑(byteAt d (o + 1)) : Int) * 256 by
      have := byteAt_lt d (o + 1); have h : (IntTy.mk 32 true).minVal = -2147483648 := rfl; omega),
    (show (↑(byteAt d (o + 1)) : Int) * 256 ≤ (IntTy.mk 32 true).maxVal by
      have := byteAt_lt d (o + 1); have h : (IntTy.mk 32 true).maxVal = 2147483647 := rfl; omega),
    (show ¬ (2147483648 ≤ rd16le d o) by have := rd16le_lt d o; omega),
    (show byteAt d (o + 1) * 256 % 4294967296 = byteAt d (o + 1) * 256 from
      Nat.mod_eq_of_lt (by have := byteAt_lt d (o + 1); omega)),
    (wrap_i32_byte_mul (byteAt_lt d (o + 1))),
    (wrap_u16_ofNat2 (rd16le_lt d o)),
    rd16le_or'']

/-- `ni_read_u32le(p)`. -/
theorem ni_read_u32le_exs (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d) (o : Nat)
    (ho : o + 4 ≤ d.length) (hl : d.length < 2 ^ 64) (ro : Bool) :
    ExS Gen.prog ⟨frameLocals [0] [.ptr bd o], m, ro⟩ Gen.ni_read_u32le.body
      (.ret (some (.int u32 (rd32le d o)))) ⟨frameLocals [0] [.ptr bd o], m, ro⟩ := by
  refine ExS.of_eq 30 (fun n => ?_)
  have l1 : o + 1 < 2 ^ 64 := by omega
  have h1 : o < d.length := by omega
  have h2 : o + 1 < d.length := by omega
  have h3 : o + 2 < d.length := by omega
  have h4 : o + 3 < d.length := by omega
  simp [Gen.ni_read_u32le, execStmt, evalExpr, frameLocals, evalBin, isPtr, ptrEq, evalBinInt, binInt, evalCast, intOf, load,
    readBytes, hm, ptrAddN, ptrAdd, List.idxOf?, List.findIdx?, List.findIdx?.go, IntTy.u64, IntTy.u32, IntTy.u16, IntTy.u8,
    IntTy.toInt, Ty.size, IntTy.bytes, IntTy.modulus, l1, Nat.mod_eq_of_lt, C.guard,
    decodeLE_take_one_drop, h1, h2, h3, h4, rd32_or,
    (by omega : o ≤ d.length), (by omega : o + 1 ≤ d.length), (by omega : o + 2 ≤ d.length),
    (by omega : o + 3 ≤ d.length), (by omega : o + 1 + 1 ≤ d.length), (by omega : o + 2 + 1 ≤ d.length),
    (by omega : o + 3 + 1 ≤ d.length),
    (by omega : (o : Int) + 1 ≤ (d.length : Int)), (by omega : (o : Int) + 2 ≤ (d.length : Int)),
    (by omega : (o : Int) + 3 ≤ (d.length : Int)),
    (by omega : ((o : Int) + 2).toNat + 1 ≤ d.length), (by omega : ((o : Int) + 3).toNat + 1 ≤ d.length),
    (by omega : ((o : Int) + 1).toNat + 1 ≤ d.length),
    (by omega : ((o : Int) + 2).toNat < d.length), (by omega : ((o : Int) + 3).toNat < d.length),
    (show ((o : Int) + 2).toNat = o + 2 by omega), (show ((o : Int) + 3).toNat = o + 3 by omega),
    (by omega : 0 ≤ (o : Int) + 1), (by omega : 0 ≤ (o : Int) + 2), (by omega : 0 ≤ (o : Int) + 3)]

/-- Calling `ni_read_u32le(p)` in an expression. -/
theorem ni_read_u32le_call {s : State} {bd : Nat} {d : List UInt8} {hm : s.mem bd = some d} (o : Nat)
    (ho : o + 4 ≤ d.length) (hl : d.length < 2 ^ 64)
    (hp : EvE Gen.prog s (.var 0) (.ptr bd o)) :
    EvE Gen.prog s (.call Gen.fid_ni_read_u32le [.var 0]) (.int u32 (rd32le d o)) :=
  EvE.call (EvArgs.cons hp EvArgs.nil) rfl rfl
    (ni_read_u32le_exs s.mem bd d hm o ho hl true)

/-- `ni_read_i32le(p)`: little-endian 32-bit load, re-interpreted as i32. -/
theorem ni_read_i32le_exs (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d) (o : Nat)
    (ho : o + 4 ≤ d.length) (hl : d.length < 2 ^ 64) (ro : Bool) :
    ExS Gen.prog ⟨frameLocals [0] [.ptr bd o], m, ro⟩ Gen.ni_read_i32le.body
      (.ret (some (.int i32 (rd32le d o)))) ⟨frameLocals [0] [.ptr bd o], m, ro⟩ :=
  let s := (⟨frameLocals [0] [.ptr bd o], m, ro⟩ : State)
  have hp : EvE Gen.prog s (.var 0) (.ptr bd o) := EvE.var rfl
  have hcall : EvE Gen.prog s (.call Gen.fid_ni_read_u32le [(.var 0)]) (.int u32 (rd32le d o)) :=
    EvE.call (EvArgs.cons hp EvArgs.nil) rfl rfl (ni_read_u32le_exs m bd d hm o ho hl true)
  have hv : evalCast ⟨32, true⟩ (.int u32 (rd32le d o)) = Res.ok (.int i32 (rd32le d o)) := by
    simp [evalCast, IntTy.u32, IntTy.i32, IntTy.modulus, Nat.mod_eq_of_lt (show rd32le d o < 4294967296 from by
      have := rd32_lt d o; omega)]
  have hcast : EvE Gen.prog s (.cast ⟨32, true⟩ (.call Gen.fid_ni_read_u32le [(.var 0)]))
      (.int i32 (rd32le d o)) :=
    EvE.cast hcall hv
  ExS.ret hcast

/-- `ni_read_u16be(p)`. -/
theorem ni_read_u16be_exs (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d) (o : Nat)
    (ho : o + 2 ≤ d.length) (hl : d.length < 2 ^ 64) (ro : Bool) :
    ExS Gen.prog ⟨frameLocals [0] [.ptr bd o], m, ro⟩ Gen.ni_read_u16be.body
      (.ret (some (.int u16 (rd16be d o)))) ⟨frameLocals [0] [.ptr bd o], m, ro⟩ := by
  refine ExS.of_eq 30 (fun n => ?_)
  have l1 : o + 1 < 2 ^ 64 := by omega
  have h1 : o < d.length := by omega
  have h2 : o + 1 < d.length := by omega
  have hcon : ¬ (2147483648 : Int) ≤ ((byteAt d o) * 256 + (byteAt d (o + 1)) : Nat) := by
    have h1 := byteAt_lt d o
    have h2 := byteAt_lt d (o + 1)
    omega
  have hconN : ¬ (byteAt d o * 256 + byteAt d (o + 1)) ≥ 2147483648 := by
    have h1 := byteAt_lt d o
    have h2 := byteAt_lt d (o + 1)
    omega
  simp [Gen.ni_read_u16be, if_neg hconN, execStmt, evalExpr, frameLocals, evalBin, isPtr, ptrEq, evalBinInt, binInt, evalCast, intOf, arith, IntTy.inRange, load,
    readBytes, hm, ptrAddN, ptrAdd, List.idxOf?, List.findIdx?, List.findIdx?.go, IntTy.u64, IntTy.u32, IntTy.u16, IntTy.u8,
    IntTy.toInt, Ty.size, IntTy.bytes, IntTy.modulus, l1, Nat.mod_eq_of_lt, C.guard,
    decodeLE_take_one_drop, h1, h2, rd16be, rd32be, rd16be_or, hcon,
    Int.ofNat_lt,
    (show (2147483648 : Int) ≤ byteAt d o * 256 + byteAt d (o + 1) ↔ 2147483648 ≤ (byteAt d o * 256 + byteAt d (o + 1) : Nat) from Int.ofNat_le),
    wrap_u16_bytes (byteAt d o) (byteAt d (o + 1)) (byteAt_lt d o) (byteAt_lt d (o + 1)),
    Int.natCast_add, Int.natCast_mul,
    hcon,
    (by omega : o ≤ d.length), (by omega : o + 1 ≤ d.length), (by omega : o + 1 + 1 ≤ d.length),
    (by omega : (o : Int) + 1 ≤ (d.length : Int)), (by omega : 0 ≤ (o : Int) + 1),
    (show (IntTy.mk 32 true).minVal ≤ (↑(byteAt d o) : Int) * 256 ∧
        (↑(byteAt d o) : Int) * 256 ≤ (IntTy.mk 32 true).maxVal from by
      have := byteAt_lt d o
      have hmin : (IntTy.mk 32 true).minVal = -2147483648 := rfl
      have hmax : (IntTy.mk 32 true).maxVal = 2147483647 := rfl
      omega),
    (show ¬ ((↑(byteAt d o) : Int) < 0) by have := byteAt_lt d o; omega),
    (show ¬ (2147483648 ≤ byteAt d o) by have := byteAt_lt d o; omega),
    (by have := byteAt_lt d o; omega : byteAt d o % 65536 % 4294967296 = byteAt d o),
    (by have := byteAt_lt d o; omega : byteAt d o % 65536 = byteAt d o),
    (show ¬ (2147483648 ≤ rd16be d o) by have := rd16be_lt d o; omega),
    (wrap_i32_byte_mul (byteAt_lt d o))]

/-- `ni_read_u32be(p)`. -/
theorem ni_read_u32be_exs (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d) (o : Nat)
    (ho : o + 4 ≤ d.length) (hl : d.length < 2 ^ 64) (ro : Bool) :
    ExS Gen.prog ⟨frameLocals [0] [.ptr bd o], m, ro⟩ Gen.ni_read_u32be.body
      (.ret (some (.int u32 (rd32be d o)))) ⟨frameLocals [0] [.ptr bd o], m, ro⟩ := by
  refine ExS.of_eq 30 (fun n => ?_)
  have l1 : o + 1 < 2 ^ 64 := by omega
  have h1 : o < d.length := by omega
  have h2 : o + 1 < d.length := by omega
  have h3 : o + 2 < d.length := by omega
  have h4 : o + 3 < d.length := by omega
  have hconN : ¬ (byteAt d o * 16777216 + byteAt d (o + 1) * 65536 + byteAt d (o + 2) * 256 + byteAt d (o + 3)) ≥ 4294967296 := by
    have b0 := byteAt_lt d o; have b1 := byteAt_lt d (o + 1); have b2 := byteAt_lt d (o + 2); have b3 := byteAt_lt d (o + 3)
    omega
  simp [Gen.ni_read_u32be, if_neg hconN, execStmt, evalExpr, frameLocals, evalBin, isPtr, ptrEq, evalBinInt, binInt, evalCast, intOf, load,
    readBytes, hm, ptrAddN, ptrAdd, List.idxOf?, List.findIdx?, List.findIdx?.go, IntTy.u64, IntTy.u32, IntTy.u16, IntTy.u8,
    IntTy.toInt, Ty.size, IntTy.bytes, IntTy.modulus, l1, Nat.mod_eq_of_lt, C.guard,
    decodeLE_take_one_drop, h1, h2, h3, h4, rd32be_or,
    (by omega : o ≤ d.length), (by omega : o + 1 ≤ d.length), (by omega : o + 2 ≤ d.length),
    (by omega : o + 3 ≤ d.length), (by omega : o + 1 + 1 ≤ d.length), (by omega : o + 2 + 1 ≤ d.length),
    (by omega : o + 3 + 1 ≤ d.length),
    (by omega : (o : Int) + 1 ≤ (d.length : Int)), (by omega : (o : Int) + 2 ≤ (d.length : Int)),
    (by omega : (o : Int) + 3 ≤ (d.length : Int)),
    (by omega : ((o : Int) + 2).toNat + 1 ≤ d.length), (by omega : ((o : Int) + 3).toNat + 1 ≤ d.length),
    (by omega : ((o : Int) + 1).toNat + 1 ≤ d.length),
    (by omega : ((o : Int) + 2).toNat < d.length), (by omega : ((o : Int) + 3).toNat < d.length),
    (show ((o : Int) + 2).toNat = o + 2 by omega), (show ((o : Int) + 3).toNat = o + 3 by omega),
    (by omega : 0 ≤ (o : Int) + 1), (by omega : 0 ≤ (o : Int) + 2), (by omega : 0 ≤ (o : Int) + 3)]

/-! ## Size arithmetic: `ni_size_mul` / `ni_size_add` -/

theorem ni_size_mul_exs_ok (m : Mem) (ob : Nat) (oblock : List UInt8)
    (hm : m ob = some oblock) (hlt : 8 ≤ oblock.length) (hbl : oblock.length < 2 ^ 64)
    (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hfits : a = 0 ∨ b ≤ (2 ^ 64 - 1) / a) :
    ExS Gen.prog ⟨frameLocals [0, 1, 2] [.int u64 a, .int u64 b, .ptr ob 0], m, false⟩
      Gen.ni_size_mul.body
      (.ret (some (.int i32 1)))
      ⟨frameLocals [0, 1, 2] [.int u64 a, .int u64 b, .ptr ob 0],
        m.upd ob (NANO.C.encodeLE 8 (a * b) ++ oblock.drop 8), false⟩ := by
  let s := (⟨frameLocals [0, 1, 2] [.int u64 a, .int u64 b, .ptr ob 0], m, false⟩ : State)
  have hab : a * b ≤ 2 ^ 64 - 1 := by
    rcases hfits with h0 | hfit
    · simp [h0]
    · have h1 : a * b ≤ a * ((2 ^ 64 - 1) / a) := Nat.mul_le_mul_left a hfit
      have hd : a * ((2 ^ 64 - 1) / a) ≤ 2 ^ 64 - 1 := Nat.mul_div_le (2 ^ 64 - 1) a
      omega
  have hbytes : IntTy.u64.bytes = 8 := rfl
  have hmem : store m (.int u64) (.ptr ob 0) (.int u64 (a * b)) =
      .ok (m.upd ob (NANO.C.encodeLE 8 (a * b) ++ oblock.drop 8)) := by
    simp only [store, writeBytes, hm, IntTy.bytes, IntTy.u64]
    simp [show IntTy.u64.bytes = 8 from rfl, NANO.C.encodeLE_length, hlt, List.take_zero]
  have h1 : EvE Gen.prog s (.var 0) (.int u64 a) := EvE.var rfl
  have h2 : EvE Gen.prog s (.var 1) (.int u64 b) := EvE.var rfl
  have hc0 : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))) (.int u64 0) :=
    EvE.cast (EvE.const (v := (.int ⟨32, false⟩ 0))) rfl
  have hn : EvE Gen.prog s (.bin .ne (some ⟨64, false⟩) (.var 0)
      (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
      (boolVal (decide (a ≠ 0))) :=
    EvE.bin h1 hc0 (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq])
  have hd (hne : a ≠ 0) :
      EvE Gen.prog s (.bin .div (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 0))
        (.int u64 ((2 ^ 64 - 1) / a)) := by
    have hconst : EvE Gen.prog s (.const (.int ⟨64, false⟩ 18446744073709551615)) (.int u64 (2 ^ 64 - 1)) :=
      EvE.of_eq 1 (by simp [evalExpr, IntTy.u64])
    exact EvE.bin hconst h1 (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq, hne])
  have hgt (hne : a ≠ 0) (hle : b ≤ (2 ^ 64 - 1) / a) :
      EvE Gen.prog s (.bin .gt (some ⟨64, false⟩) (.var 1)
        (.bin .div (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 0)))
        (boolVal (decide (b > (2 ^ 64 - 1) / a))) :=
    EvE.bin h2 (hd hne) (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq])
  have hcond : EvE Gen.prog s
      (.land (.bin .ne (some ⟨64, false⟩) (.var 0) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
        (.bin .gt (some ⟨64, false⟩) (.var 1)
          (.bin .div (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 0))))
      (.int IntTy.i32 0) := by
    rcases hfits with h0 | hfit
    · subst h0
      exact EvE.land_false hn rfl
    · by_cases h0 : a = 0
      · subst h0; exact EvE.land_false hn rfl
      · have hdt : decide (a ≠ 0) = true := decide_eq_true_iff.2 h0
        have hdf : decide (b > (2 ^ 64 - 1) / a) = false :=
          decide_eq_false_iff_not.2 (by omega)
        have htr : truthy (boolVal (decide (a ≠ 0))) = .ok true := by rw [hdt]; rfl
        have htf : truthy (boolVal (decide (b > (2 ^ 64 - 1) / a))) = .ok false := by rw [hdf]; rfl
        exact EvE.land_true hn htr (hgt h0 hfit) htf
  have hit : ExS Gen.prog s
      (.ite (.land (.bin .ne (some ⟨64, false⟩) (.var 0) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
        (.bin .gt (some ⟨64, false⟩) (.var 1)
          (.bin .div (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 0))))
        (.ret (some (.const (.int ⟨32, true⟩ 0))))
        .skip)
      .normal s :=
    ExS.ite hcond rfl ExS.skip
  have hmul : EvE Gen.prog s (.bin .mul (some ⟨64, false⟩) (.var 0) (.var 1)) (.int u64 (a * b)) :=
    EvE.bin h1 h2 (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq, show (⟨64, false⟩ : IntTy).modulus = 18446744073709551616 from rfl, Nat.mod_eq_of_lt (show a * b < 18446744073709551616 by omega)])
  have hstore : ExS Gen.prog s
      (.store (.int ⟨64, false⟩) (.var 2) (.bin .mul (some ⟨64, false⟩) (.var 0) (.var 1)))
      .normal ⟨frameLocals [0, 1, 2] [.int u64 a, .int u64 b, .ptr ob 0],
        m.upd ob (NANO.C.encodeLE 8 (a * b) ++ oblock.drop 8), false⟩ :=
    ExS.store (EvE.var rfl (i := 2)) hmul rfl hmem
  exact ExS.seq hit (ExS.seq hstore (ExS.ret (EvE.const (v := (.int IntTy.i32 1)))))


/-- `ni_size_mul` fails with 0 (writes nothing) when `a * b` would overflow. -/
theorem ni_size_mul_exs_fail (m : Mem) (ob : Nat) (oblock : List UInt8)
    (hm : m ob = some oblock) (hlt : 8 ≤ oblock.length) (hbl : oblock.length < 2 ^ 64)
    (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hno : a ≠ 0 ∧ (2 ^ 64 - 1) / a < b) :
    ExS Gen.prog ⟨frameLocals [0, 1, 2] [.int u64 a, .int u64 b, .ptr ob 0], m, false⟩
      Gen.ni_size_mul.body
      (.ret (some (.int i32 0)))
      ⟨frameLocals [0, 1, 2] [.int u64 a, .int u64 b, .ptr ob 0], m, false⟩ := by
  let s := (⟨frameLocals [0, 1, 2] [.int u64 a, .int u64 b, .ptr ob 0], m, false⟩ : State)
  have h1 : EvE Gen.prog s (.var 0) (.int u64 a) := EvE.var rfl
  have h2 : EvE Gen.prog s (.var 1) (.int u64 b) := EvE.var rfl
  have hc0 : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))) (.int u64 0) :=
    EvE.cast (EvE.const (v := (.int ⟨32, false⟩ 0))) rfl
  have hn : EvE Gen.prog s (.bin .ne (some ⟨64, false⟩) (.var 0)
      (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
      (boolVal (decide (a ≠ 0))) :=
    EvE.bin h1 hc0 (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq])
  have hd : EvE Gen.prog s (.bin .div (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 0))
      (.int u64 ((2 ^ 64 - 1) / a)) := by
    have hconst : EvE Gen.prog s (.const (.int ⟨64, false⟩ 18446744073709551615)) (.int u64 (2 ^ 64 - 1)) :=
      EvE.of_eq 1 (by simp [evalExpr, IntTy.u64])
    exact EvE.bin hconst h1 (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq, hno.1])
  have hgt : EvE Gen.prog s (.bin .gt (some ⟨64, false⟩) (.var 1)
      (.bin .div (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 0)))
      (boolVal (decide (b > (2 ^ 64 - 1) / a))) :=
    EvE.bin h2 hd (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq])
  have hcond : EvE Gen.prog s
      (.land (.bin .ne (some ⟨64, false⟩) (.var 0) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0))))
        (.bin .gt (some ⟨64, false⟩) (.var 1)
          (.bin .div (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 0))))
      (.int IntTy.i32 1) := by
    have hdt : decide (a ≠ 0) = true := decide_eq_true_iff.2 hno.1
    have hdt2 : decide (b > (2 ^ 64 - 1) / a) = true := decide_eq_true_iff.2 hno.2
    have htr : truthy (boolVal (decide (a ≠ 0))) = .ok true := by rw [hdt]; rfl
    have htf : truthy (boolVal (decide (b > (2 ^ 64 - 1) / a))) = .ok true := by rw [hdt2]; rfl
    exact EvE.land_true hn htr hgt htf
  exact ExS.seq_ret (ExS.ite hcond rfl (ExS.ret (EvE.const (v := (.int IntTy.i32 0)))))

/-- `ni_size_add` succeeds and stores `a + b` when it does not overflow. -/
theorem ni_size_add_exs_ok (m : Mem) (ob : Nat) (oblock : List UInt8)
    (hm : m ob = some oblock) (hlt : 8 ≤ oblock.length) (hbl : oblock.length < 2 ^ 64)
    (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hfits : a ≤ (2 ^ 64 - 1) - b) :
    ExS Gen.prog ⟨frameLocals [0, 1, 2] [.int u64 a, .int u64 b, .ptr ob 0], m, false⟩
      Gen.ni_size_add.body
      (.ret (some (.int i32 1)))
      ⟨frameLocals [0, 1, 2] [.int u64 a, .int u64 b, .ptr ob 0],
        m.upd ob (NANO.C.encodeLE 8 (a + b) ++ oblock.drop 8), false⟩ := by
  let s := (⟨frameLocals [0, 1, 2] [.int u64 a, .int u64 b, .ptr ob 0], m, false⟩ : State)
  have hab : a + b ≤ 2 ^ 64 - 1 := by omega
  have hmem : store m (.int u64) (.ptr ob 0) (.int u64 (a + b)) =
      .ok (m.upd ob (NANO.C.encodeLE 8 (a + b) ++ oblock.drop 8)) := by
    simp only [store, writeBytes, hm, IntTy.bytes, IntTy.u64]
    simp [show (⟨64, false⟩ : IntTy).width = 64 from rfl, NANO.C.encodeLE_length, hlt, List.take_zero]
  have h1 : EvE Gen.prog s (.var 0) (.int u64 a) := EvE.var rfl
  have h2 : EvE Gen.prog s (.var 1) (.int u64 b) := EvE.var rfl
  have hconst : EvE Gen.prog s (.const (.int ⟨64, false⟩ 18446744073709551615)) (.int u64 (2 ^ 64 - 1)) :=
    EvE.of_eq 1 (by simp [evalExpr, IntTy.u64])
  have hsub : EvE Gen.prog s (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 1))
      (.int u64 ((2 ^ 64 - 1) - b)) :=
    EvE.bin hconst h2 (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq, show b ≤ 18446744073709551615 from by omega])
  have hgt_false : EvE Gen.prog s (.bin .gt (some ⟨64, false⟩) (.var 0)
      (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 1)))
      (boolVal (decide (a > (2 ^ 64 - 1) - b))) :=
    EvE.bin h1 hsub (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq])
  have hcond : EvE Gen.prog s
      (.bin .gt (some ⟨64, false⟩) (.var 0)
        (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 1)))
      (.int IntTy.i32 0) := by
    have hdf : decide (a > (2 ^ 64 - 1) - b) = false :=
      decide_eq_false_iff_not.2 (by omega)
    have htf : truthy (boolVal (decide (a > (2 ^ 64 - 1) - b))) = .ok false := by rw [hdf]; rfl
    have hcond' : EvE Gen.prog s
        (.bin .gt (some ⟨64, false⟩) (.var 0)
          (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 1)))
        (.int IntTy.i32 0) := by
      have : (.int IntTy.i32 0) = boolVal (decide (a > (2 ^ 64 - 1) - b)) := by
        simp [boolVal, decide_eq_false_iff_not.2 (by omega : ¬ a > (2 ^ 64 - 1) - b)]
      rw [this]
      exact hgt_false
    exact hcond'
  have hit : ExS Gen.prog s
      (.ite (.bin .gt (some ⟨64, false⟩) (.var 0)
        (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 1)))
        (.ret (some (.const (.int ⟨32, true⟩ 0))))
        .skip)
      .normal s :=
    ExS.ite hcond rfl ExS.skip
  have hadd : EvE Gen.prog s (.bin .add (some ⟨64, false⟩) (.var 0) (.var 1)) (.int u64 (a + b)) :=
    EvE.bin h1 h2 (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq,
      show (⟨64, false⟩ : IntTy).modulus = 18446744073709551616 from rfl,
      Nat.mod_eq_of_lt (show a + b < 18446744073709551616 by omega)])
  have hstore : ExS Gen.prog s
      (.store (.int ⟨64, false⟩) (.var 2) (.bin .add (some ⟨64, false⟩) (.var 0) (.var 1)))
      .normal ⟨frameLocals [0, 1, 2] [.int u64 a, .int u64 b, .ptr ob 0],
        m.upd ob (NANO.C.encodeLE 8 (a + b) ++ oblock.drop 8), false⟩ :=
    ExS.store (EvE.var rfl (i := 2)) hadd rfl hmem
  exact ExS.seq hit (ExS.seq hstore (ExS.ret (EvE.const (v := (.int IntTy.i32 1)))))

/-- `ni_size_add` fails with 0 (writes nothing) when `a + b` would overflow. -/
theorem ni_size_add_exs_fail (m : Mem) (ob : Nat) (oblock : List UInt8)
    (hm : m ob = some oblock) (hlt : 8 ≤ oblock.length) (hbl : oblock.length < 2 ^ 64)
    (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hno : (2 ^ 64 - 1) - b < a) :
    ExS Gen.prog ⟨frameLocals [0, 1, 2] [.int u64 a, .int u64 b, .ptr ob 0], m, false⟩
      Gen.ni_size_add.body
      (.ret (some (.int i32 0)))
      ⟨frameLocals [0, 1, 2] [.int u64 a, .int u64 b, .ptr ob 0], m, false⟩ := by
  let s := (⟨frameLocals [0, 1, 2] [.int u64 a, .int u64 b, .ptr ob 0], m, false⟩ : State)
  have h1 : EvE Gen.prog s (.var 0) (.int u64 a) := EvE.var rfl
  have h2 : EvE Gen.prog s (.var 1) (.int u64 b) := EvE.var rfl
  have hconst : EvE Gen.prog s (.const (.int ⟨64, false⟩ 18446744073709551615)) (.int u64 (2 ^ 64 - 1)) :=
    EvE.of_eq 1 (by simp [evalExpr, IntTy.u64])
  have hsub : EvE Gen.prog s (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 1))
      (.int u64 ((2 ^ 64 - 1) - b)) :=
    EvE.bin hconst h2 (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq, show b ≤ 18446744073709551615 from by omega])
  have hgt : EvE Gen.prog s (.bin .gt (some ⟨64, false⟩) (.var 0)
      (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 1)))
      (boolVal (decide (a > (2 ^ 64 - 1) - b))) :=
    EvE.bin h1 hsub (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq])
  have hcond : EvE Gen.prog s
      (.bin .gt (some ⟨64, false⟩) (.var 0)
        (.bin .sub (some ⟨64, false⟩) (.const (.int ⟨64, false⟩ 18446744073709551615)) (.var 1)))
      (.int IntTy.i32 1) := by
    have hdt : decide (a > (2 ^ 64 - 1) - b) = true := decide_eq_true_iff.2 hno
    have htr : truthy (boolVal (decide (a > (2 ^ 64 - 1) - b))) = .ok true := by rw [hdt]; rfl
    have : (.int IntTy.i32 1) = boolVal (decide (a > (2 ^ 64 - 1) - b)) := by
      simp [boolVal, decide_eq_true_iff.2 hno]
    rw [this]
    exact hgt
  exact ExS.seq_ret (ExS.ite hcond rfl (ExS.ret (EvE.const (v := (.int IntTy.i32 0)))))

/-! ## `ni_clamp_u8` -/

theorem ni_clamp_u8_exs (m : Mem) (ro : Bool) (n : Nat) (hn : n < 4294967296) :
    ExS Gen.prog ⟨frameLocals [0] [.int i32 n], m, ro⟩ Gen.ni_clamp_u8.body
      (.ret (some (.int u8 (clampU8 (IntTy.toInt i32 n)))))
      ⟨frameLocals [0] [.int i32 n], m, ro⟩ := by
  let s : State := ⟨frameLocals [0] [.int i32 n], m, ro⟩
  have h0 : EvE Gen.prog s (.var 0) (.int i32 n) := EvE.var rfl
  have hc0 : EvE Gen.prog s (.const (.int i32 0)) (.int i32 0) := EvE.const _
  have hc255 : EvE Gen.prog s (.const (.int i32 255)) (.int i32 255) := EvE.const _
  have hlt : EvE Gen.prog s (.bin .lt (some i32) (.var 0) (.const (.int i32 0)))
      (boolVal (decide (IntTy.toInt i32 n < 0))) :=
    EvE.bin h0 hc0 (by rw [bin_i32_lt, toInt_i32_zero])
  have hgt : EvE Gen.prog s (.bin .gt (some i32) (.var 0) (.const (.int i32 255)))
      (boolVal (decide (IntTy.toInt i32 n > 255))) :=
    EvE.bin h0 hc255 (by rw [bin_i32_gt]; rfl)
  have hcast0 : EvE Gen.prog s (.cast u8 (.const (.int u32 0))) (.int u8 0) :=
    EvE.cast (EvE.const _) rfl
  have hcast255 : EvE Gen.prog s (.cast u8 (.const (.int u32 255))) (.int u8 255) :=
    EvE.cast (EvE.const _) rfl
  have hcastv : ∀ z : Int, 0 ≤ z → z ≤ 255 → IntTy.toInt i32 n = z →
      EvE Gen.prog s (.cast u8 (.var 0)) (.int u8 z.toNat) := by
    intro z h0' h1' hz
    refine EvE.cast h0 ?_
    simp [evalCast, hz, wrap_u8_range h0' h1']
  have hb := toInt_i32_bounds n hn
  rcases Int.lt_or_le (IntTy.toInt i32 n) 0 with hneg | hnn
  · rw [clampU8_neg hneg]
    have htr : truthy (boolVal (decide (IntTy.toInt i32 n < 0))) = .ok true := by
      rw [decide_eq_true hneg]; rfl
    exact ExS.seq_ret (ExS.ite hlt htr (ExS.ret hcast0))
  · have htf : truthy (boolVal (decide (IntTy.toInt i32 n < 0))) = .ok false := by
      rw [decide_eq_false (by omega)]; rfl
    rcases Int.lt_or_le 255 (IntTy.toInt i32 n) with hbig | hsm
    · rw [clampU8_big hbig]
      have htr : truthy (boolVal (decide (IntTy.toInt i32 n > 255))) = .ok true := by
        rw [decide_eq_true hbig]; rfl
      exact ExS.seq (ExS.ite hlt htf ExS.skip) (ExS.seq_ret (ExS.ite hgt htr (ExS.ret hcast255)))
    · have htf2 : truthy (boolVal (decide (IntTy.toInt i32 n > 255))) = .ok false := by
        rw [decide_eq_false (by omega)]; rfl
      rw [clampU8_mid hnn hsm]
      exact ExS.seq (ExS.ite hlt htf ExS.skip)
        (ExS.seq (ExS.ite hgt htf2 ExS.skip) (ExS.ret (hcastv _ hnn hsm rfl)))

/-! ## `ni_read_packed_bits` (PNG depths 1, 2, 4, 8) -/

theorem packed_shift_bounds (p bd : Nat) (hbd : bd = 1 ∨ bd = 2 ∨ bd = 4 ∨ bd = 8) :
    (p * bd) % 8 + bd ≤ 8 := by
  rcases hbd with rfl | rfl | rfl | rfl <;> omega

theorem ni_read_packed_bits_exs (m : Mem) (ob : Nat) (row : List UInt8) (hm : m ob = some row)
    (p bd : Nat) (hp : p < 2 ^ 32) (hbd : bd = 1 ∨ bd = 2 ∨ bd = 4 ∨ bd = 8)
    (hin : p * bd / 8 < row.length) (hrl : row.length < 2 ^ 64) (ro : Bool) :
    ∃ s', ExS Gen.prog ⟨frameLocals [0, 1, 2] [.ptr ob 0, .int u64 p, .int u8 bd], m, ro⟩
      Gen.ni_read_packed_bits.body (.ret (some (.int u32 (packedBits row p bd)))) s' := by
  let s0 : State := ⟨frameLocals [0, 1, 2] [.ptr ob 0, .int u64 p, .int u8 bd], m, ro⟩
  have hsb := packed_shift_bounds p bd hbd
  have hbdv : bd < 256 := by rcases hbd with rfl | rfl | rfl | rfl <;> omega
  have hbi : p * bd < 2 ^ 64 := by
    rcases hbd with rfl | rfl | rfl | rfl <;> omega
  have e1 : EvE Gen.prog s0 (.var 1) (.int u64 p) := EvE.var rfl
  have e2 : EvE Gen.prog s0 (.var 2) (.int u8 bd) := EvE.var rfl
  have ecast2 : EvE Gen.prog s0 (.cast u64 (.var 2)) (.int u64 bd) :=
    EvE.cast e2 (by simp [evalCast, IntTy.u8, IntTy.u64, IntTy.modulus, Nat.mod_eq_of_lt (show bd < 18446744073709551616 by omega)])
  have hmul : EvE Gen.prog s0 (.bin .mul (some u64) (.var 1) (.cast u64 (.var 2))) (.int u64 (p * bd)) :=
    EvE.bin e1 ecast2 (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq,
      show (⟨64, false⟩ : IntTy).modulus = 18446744073709551616 from rfl,
      Nat.mod_eq_of_lt hbi])
  let s1 : State := {s0 with locals := s0.locals.upd 3 (.int u64 (p * bd))}
  have e3 : EvE Gen.prog s1 (.var 3) (.int u64 (p * bd)) := EvE.var (by simp [s1])
  have hv4 : EvE Gen.prog s1 (.bin .shr (some u64) (.var 3) (.const (.int u32 3))) (.int u64 (p * bd / 8)) :=
    EvE.bin e3 (EvE.const _) (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, IntTy.u32, isPtr, ptrEq,
      show (⟨64, false⟩ : IntTy).modulus = 18446744073709551616 from rfl, IntTy.toInt,
      show (2 : Nat) ^ 3 = 8 from rfl, show (p * bd / 2 ^ 3) = p * bd / 8 from rfl, C.guard])
  let s2 : State := {s1 with locals := s1.locals.upd 4 (.int u64 (p * bd / 8))}
  have e4 : EvE Gen.prog s2 (.var 4) (.int u64 (p * bd / 8)) := EvE.var (by simp [s2])
  have e2' : EvE Gen.prog s2 (.var 2) (.int u8 bd) := EvE.var rfl
  have e3' : EvE Gen.prog s2 (.var 3) (.int u64 (p * bd)) := EvE.var (by simp [s2, s1])
  have ecast32 : EvE Gen.prog s2 (.cast u32 (.var 2)) (.int u32 bd) :=
    EvE.cast e2' (by simp [evalCast, IntTy.u8, IntTy.u32, IntTy.modulus, show bd < 4294967296 by omega, Nat.mod_eq_of_lt (show bd < 4294967296 by omega)])
  have hsub8 : EvE Gen.prog s2 (.bin .sub (some u32) (.const (.int u32 8)) (.cast u32 (.var 2)))
      (.int u32 (8 - bd)) :=
    EvE.bin (EvE.const _) ecast32 (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u32, isPtr, ptrEq,
      show (8 : Nat) - bd = 8 - bd from rfl, show bd ≤ 8 by omega, Nat.mod_eq_of_lt (show 8 < 4294967296 by omega),
      Nat.mod_eq_of_lt (show 8 - bd < 4294967296 by omega), C.guard])
  have hcast64 : EvE Gen.prog s2 (.cast u64 (.bin .sub (some u32) (.const (.int u32 8)) (.cast u32 (.var 2))))
      (.int u64 (8 - bd)) :=
    EvE.cast hsub8 (by simp [evalCast, IntTy.u32, IntTy.u64, IntTy.modulus, Nat.mod_eq_of_lt (show 8 - bd < 18446744073709551616 by omega)])
  have hband : EvE Gen.prog s2 (.bin .band (some u64) (.var 3) (.cast u64 (.const (.int u32 7))))
      (.int u64 ((p * bd) % 8)) :=
    EvE.bin e3' (EvE.cast (v := .int u64 7) (EvE.const (v := .int u32 7)) (by simp [evalCast, IntTy.u32, IntTy.u64, IntTy.modulus]))
      (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq, and_seven])
  have hsub64 : EvE Gen.prog s2 (.bin .sub (some u64) (.cast u64 (.bin .sub (some u32) (.const (.int u32 8)) (.cast u32 (.var 2))))
      (.bin .band (some u64) (.var 3) (.cast u64 (.const (.int u32 7)))))
      (.int u64 (8 - bd - (p * bd) % 8)) :=
    EvE.bin hcast64 hband (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u64, isPtr, ptrEq, hsb,
      show IntTy.u64.modulus = 18446744073709551616 from rfl, Nat.mod_eq_of_lt (show 8 - bd - (p * bd) % 8 < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (8 - bd) < 18446744073709551616 by omega), show (8 - bd) - (p * bd) % 8 = 8 - bd - (p * bd) % 8 from rfl, show ¬ (8 - bd < (p * bd) % 8) from by omega])
  have hsh : EvE Gen.prog s2 (.cast u8 (.bin .sub (some u64) (.cast u64 (.bin .sub (some u32) (.const (.int u32 8)) (.cast u32 (.var 2))))
      (.bin .band (some u64) (.var 3) (.cast u64 (.const (.int u32 7))))))
      (.int u8 (8 - bd - (p * bd) % 8)) :=
    EvE.cast hsub64 (by simp [evalCast, IntTy.u64, IntTy.u8, IntTy.modulus, Nat.mod_eq_of_lt (show 8 - bd - (p * bd) % 8 < 256 by omega)])
  let s3 : State := {s2 with locals := s2.locals.upd 5 (.int u8 (8 - bd - (p * bd) % 8))}
  have e2s : EvE Gen.prog s3 (.var 2) (.int u8 bd) := EvE.var rfl
  have hbd8 : bd ≤ 8 := by omega
  have hp2 : 2 ^ bd ≤ 256 := pow2_le256 hbd8
  have hi32 : EvE Gen.prog s3 (.cast ⟨32, true⟩ (.var 2)) (.int ⟨32, true⟩ bd) :=
    EvE.cast e2s (by simp [evalCast, IntTy.u8, show (⟨32, true⟩ : IntTy).modulus = 4294967296 from rfl,
      Nat.mod_eq_of_lt (show bd < 4294967296 by omega), toInt_i32_small (show bd < 2147483648 by omega),
      IntTy.toInt, wrap_i32_ofNat (show bd < 2147483648 by omega)])
  have hshl : EvE Gen.prog s3 (.bin .shl (some u32) (.const (.int u32 1)) (.cast ⟨32, true⟩ (.var 2)))
      (.int u32 (2 ^ bd)) :=
    EvE.bin (EvE.const _) hi32 (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u32, isPtr, ptrEq, C.guard,
      toInt_i32_small (show bd < 2147483648 by omega), show bd < 32 by omega,
      show (⟨32, false⟩ : IntTy).modulus = 4294967296 from rfl, show (⟨32, false⟩ : IntTy).modulus = 4294967296 from rfl,
      show (bd : Int) < 32 by omega, Int.ofNat_lt.mpr (show bd < 32 by omega),
      show (2 : Nat) ^ bd < 4294967296 by omega, Nat.mod_eq_of_lt (show 2 ^ bd < 4294967296 by omega)])
  have hmk1 : EvE Gen.prog s3 (.bin .sub (some u32) (.bin .shl (some u32) (.const (.int u32 1)) (.cast ⟨32, true⟩ (.var 2)))
      (.const (.int u32 1))) (.int u32 (2 ^ bd - 1)) :=
    EvE.bin hshl (EvE.const _) (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u32, isPtr, ptrEq, C.guard,
      show 1 ≤ 2 ^ bd from Nat.one_le_two_pow, show 2 ^ bd - 1 < 4294967296 by omega,
      Nat.mod_eq_of_lt (show 2 ^ bd - 1 < 4294967296 by omega)])
  have hmk : EvE Gen.prog s3 (.cast u8 (.bin .sub (some u32) (.bin .shl (some u32) (.const (.int u32 1)) (.cast ⟨32, true⟩ (.var 2)))
      (.const (.int u32 1)))) (.int u8 (2 ^ bd - 1)) :=
    EvE.cast hmk1 (by simp [evalCast, IntTy.u32, IntTy.u8, IntTy.modulus, Nat.mod_eq_of_lt (show 2 ^ bd - 1 < 256 by omega)])
  let s4 : State := {s3 with locals := s3.locals.upd 6 (.int u8 (2 ^ bd - 1))}
  have hm4 : s4.mem ob = some row := hm
  have e0 : EvE Gen.prog s4 (.var 0) (.ptr ob 0) := EvE.var rfl
  have e4' : EvE Gen.prog s4 (.var 4) (.int u64 (p * bd / 8)) := EvE.var rfl
  have e5' : EvE Gen.prog s4 (.var 5) (.int u8 (8 - bd - (p * bd) % 8)) := EvE.var rfl
  have e6' : EvE Gen.prog s4 (.var 6) (.int u8 (2 ^ bd - 1)) := EvE.var rfl
  have hidx : EvE Gen.prog s4 (.index (.var 0) (.var 4) 1) (.ptr ob (p * bd / 8)) :=
    EvE.index e0 e4' (by simp [IntTy.u64, ptrAddN, hm4, show p * bd / 8 ≤ row.length by omega])
  have hload : EvE Gen.prog s4 (.load (.int ⟨8, false⟩) (.index (.var 0) (.var 4) 1))
      (.int ⟨8, false⟩ (byteAt row (p * bd / 8))) :=
    EvE.load hidx (by simp [load, readBytes, hm4, Ty.size, IntTy.bytes, show p * bd / 8 + 1 ≤ row.length by omega,
      decodeLE_take_one_drop row (p * bd / 8) (show p * bd / 8 < row.length by omega)])
  have hbyte_lt : byteAt row (p * bd / 8) < 256 := byteAt_lt row _
  have hcb : EvE Gen.prog s4 (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.var 0) (.var 4) 1)))
      (.int ⟨32, true⟩ (byteAt row (p * bd / 8))) :=
    EvE.cast hload (by simp [evalCast, IntTy.u8, show (⟨32, true⟩ : IntTy).modulus = 4294967296 from rfl,
      toInt_i32_small (show byteAt row (p * bd / 8) < 2147483648 by omega),
      Nat.mod_eq_of_lt (show byteAt row (p * bd / 8) < 4294967296 by omega), IntTy.toInt])
  have hcs : EvE Gen.prog s4 (.cast ⟨32, true⟩ (.var 5)) (.int ⟨32, true⟩ (8 - bd - (p * bd) % 8)) :=
    EvE.cast e5' (by simp [evalCast, IntTy.u8, show (⟨32, true⟩ : IntTy).modulus = 4294967296 from rfl,
      toInt_i32_small (show 8 - bd - (p * bd) % 8 < 2147483648 by omega),
      Nat.mod_eq_of_lt (show 8 - bd - (p * bd) % 8 < 4294967296 by omega), IntTy.toInt])
  have hcm : EvE Gen.prog s4 (.cast ⟨32, true⟩ (.var 6)) (.int ⟨32, true⟩ (2 ^ bd - 1)) :=
    EvE.cast e6' (by simp [evalCast, IntTy.u8, show (⟨32, true⟩ : IntTy).modulus = 4294967296 from rfl,
      toInt_i32_small (show 2 ^ bd - 1 < 2147483648 by omega),
      Nat.mod_eq_of_lt (show 2 ^ bd - 1 < 4294967296 by omega), IntTy.toInt])
  have hdiv_lt : byteAt row (p * bd / 8) / 2 ^ (8 - bd - (p * bd) % 8) < 2147483648 :=
    div_pow_lt_231 hbyte_lt
  have hshr : EvE Gen.prog s4 (.bin .shr (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.var 0) (.var 4) 1)))
      (.cast ⟨32, true⟩ (.var 5))) (.int ⟨32, true⟩ (byteAt row (p * bd / 8) / 2 ^ (8 - bd - (p * bd) % 8))) :=
    EvE.bin hcb hcs (bin_shr_i32 (show byteAt row (p * bd / 8) < 2147483648 by omega) (by omega))
  have hmod_lt : byteAt row (p * bd / 8) / 2 ^ (8 - bd - (p * bd) % 8) % 2 ^ bd < 256 :=
    mod_pow_lt_256 hp2
  have hband : EvE Gen.prog s4 (.bin .band (some ⟨32, true⟩)
      (.bin .shr (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.var 0) (.var 4) 1)))
        (.cast ⟨32, true⟩ (.var 5)))
      (.cast ⟨32, true⟩ (.var 6)))
      (.int ⟨32, true⟩ (byteAt row (p * bd / 8) / 2 ^ (8 - bd - (p * bd) % 8) % 2 ^ bd)) :=
    EvE.bin hshr hcm (by
      simp [evalBin, evalBinInt, binInt, intOf, isPtr, ptrEq, IntTy.toInt, C.guard,
        show (⟨32, true⟩ : IntTy).modulus = 4294967296 from rfl,
        hdiv_lt, hmod_lt, int_div_two_pow, int_mod_two_pow,
        wrap_i32_ofNat (show byteAt row (p * bd / 8) / 2 ^ (8 - bd - (p * bd) % 8) % 2 ^ bd < 2147483648 by omega),
        Nat.and_two_pow_sub_one_eq_mod])
  have hmod_lt' : byteAt row (p * bd / 8) / 2 ^ (8 - bd - (p * bd) % 8) % 2 ^ bd < 2147483648 :=
    Nat.lt_of_lt_of_le hmod_lt (by omega)
  have hfinal : EvE Gen.prog s4 (.cast ⟨32, false⟩ (.bin .band (some ⟨32, true⟩)
      (.bin .shr (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.var 0) (.var 4) 1)))
        (.cast ⟨32, true⟩ (.var 5)))
      (.cast ⟨32, true⟩ (.var 6))))
      (.int ⟨32, false⟩ (packedBits row p bd)) :=
    EvE.cast hband (by
      change Res.ok (Val.int ⟨32, false⟩ (IntTy.wrap ⟨32, false⟩
        (IntTy.toInt ⟨32, true⟩ (byteAt row (p * bd / 8) / 2 ^ (8 - bd - (p * bd) % 8) % 2 ^ bd))))
        = Res.ok (Val.int ⟨32, false⟩ (packedBits row p bd))
      rw [toInt_i32_small hmod_lt', wrap_u32_small hmod_lt']
      unfold packedBits
      rw [Nat.and_two_pow_sub_one_eq_mod])
  refine ⟨_, ExS.seq (ExS.set hmul) (ExS.seq (ExS.set hv4) (ExS.seq (ExS.set hsh) (ExS.seq (ExS.set hmk) (ExS.ret hfinal))))⟩

/-! ## `ni_scale_to_8bit` -/

theorem ni_scale_to_8bit_exs_ok (m : Mem) (ob : Nat) (blk : List UInt8) (hm : m ob = some blk)
    (hlen : 1 ≤ blk.length) (hbl : blk.length < 2 ^ 64) (v bd : Nat) (hv : v < 2 ^ 32)
    (hb1 : 1 ≤ bd) (hb8 : bd ≤ 8) :
    ∃ s', ExS Gen.prog ⟨frameLocals [0, 1, 2] [.int u32 v, .int u8 bd, .ptr ob 0], m, false⟩
        Gen.ni_scale_to_8bit.body (.ret (some (.int i32 1))) s' ∧
      s'.mem ob = some (((scaleTo8 v bd).getD 0).toUInt8 :: blk.tail) := by
  have hp2 : 2 ^ bd ≤ 256 := pow2_le256 hb8
  have hp1 : 1 ≤ 2 ^ bd := Nat.one_le_two_pow
  have hp2' : 2 ≤ 2 ^ bd := by
    have := Nat.pow_le_pow_right (show 2 > 0 by decide) hb1
    simpa using this
  let s0 : State := ⟨frameLocals [0, 1, 2] [.int u32 v, .int u8 bd, .ptr ob 0], m, false⟩
  have e0 : EvE Gen.prog s0 (.var 0) (.int u32 v) := EvE.var rfl
  have e1 : EvE Gen.prog s0 (.var 1) (.int u8 bd) := EvE.var rfl
  have e2 : EvE Gen.prog s0 (.var 2) (.ptr ob 0) := EvE.var rfl
  have c1 : EvE Gen.prog s0 (.cast u32 (.var 1)) (.int u32 bd) :=
    EvE.cast e1 (by simp [evalCast, IntTy.u8, IntTy.u32, IntTy.modulus, show bd < 4294967296 by omega,
      Nat.mod_eq_of_lt (show bd < 4294967296 by omega)])
  have c0 : EvE Gen.prog s0 (.const (.int u32 0)) (.int u32 0) := EvE.const _
  have c8 : EvE Gen.prog s0 (.const (.int u32 8)) (.int u32 8) := EvE.const _
  have eq0 : EvE Gen.prog s0 (.bin .eq (some u32) (.cast u32 (.var 1)) (.const (.int u32 0)))
      (boolVal (decide (bd = 0))) :=
    EvE.bin c1 c0 (by simp [evalBin, evalBinInt, binInt, intOf, isPtr, ptrEq, IntTy.u32, boolVal])
  have gt8 : EvE Gen.prog s0 (.bin .gt (some u32) (.cast u32 (.var 1)) (.const (.int u32 8)))
      (boolVal (decide (bd > 8))) :=
    EvE.bin c1 c8 (by simp [evalBin, evalBinInt, binInt, intOf, isPtr, ptrEq, IntTy.u32, boolVal])
  have eqnull : EvE Gen.prog s0 (.bin .eq none (.var 2) (.const .null)) (boolVal false) :=
    EvE.bin e2 (EvE.const _) (by simp [evalBin, isPtr, ptrEq, boolVal])
  have hbd0 : decide (bd = 0) = false := decide_eq_false (by omega)
  have hgt8f : decide (bd > 8) = false := decide_eq_false (by omega)
  have eqA : EvE Gen.prog s0 (.lor (.bin .eq (some u32) (.cast u32 (.var 1)) (.const (.int u32 0)))
      (.bin .gt (some u32) (.cast u32 (.var 1)) (.const (.int u32 8)))) (boolVal false) :=
    EvE.lor_false eq0 (by rw [hbd0]; rfl) gt8 (by rw [hgt8f]; rfl)
  have cond : EvE Gen.prog s0 (.lor (.lor (.bin .eq (some u32) (.cast u32 (.var 1)) (.const (.int u32 0)))
      (.bin .gt (some u32) (.cast u32 (.var 1)) (.const (.int u32 8))))
      (.bin .eq none (.var 2) (.const .null))) (boolVal false) :=
    EvE.lor_false eqA (by rfl) eqnull (by rfl)
  have htf : truthy (boolVal false) = .ok false := rfl
  have hi32 : EvE Gen.prog s0 (.cast ⟨32, true⟩ (.var 1)) (.int ⟨32, true⟩ bd) :=
    EvE.cast e1 (by simp [evalCast, IntTy.u8, show (⟨32, true⟩ : IntTy).modulus = 4294967296 from rfl,
      toInt_i32_small (show bd < 2147483648 by omega), wrap_i32_ofNat (show bd < 2147483648 by omega),
      Nat.mod_eq_of_lt (show bd < 4294967296 by omega)])
  have hshl : EvE Gen.prog s0 (.bin .shl (some u32) (.const (.int u32 1)) (.cast ⟨32, true⟩ (.var 1)))
      (.int u32 (2 ^ bd)) :=
    EvE.bin (EvE.const _) hi32 (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u32, isPtr, ptrEq, C.guard,
      toInt_i32_small (show bd < 2147483648 by omega), show bd < 32 by omega,
      show (⟨32, false⟩ : IntTy).modulus = 4294967296 from rfl, show (⟨32, false⟩ : IntTy).modulus = 4294967296 from rfl,
      show (bd : Int) < 32 by omega, Int.ofNat_lt.mpr (show bd < 32 by omega),
      show (2 : Nat) ^ bd < 4294967296 by omega, Nat.mod_eq_of_lt (show 2 ^ bd < 4294967296 by omega)])
  have hset3v : EvE Gen.prog s0 (.bin .sub (some u32) (.bin .shl (some u32) (.const (.int u32 1)) (.cast ⟨32, true⟩ (.var 1)))
      (.const (.int u32 1))) (.int u32 (2 ^ bd - 1)) :=
    EvE.bin hshl (EvE.const _) (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u32, isPtr, ptrEq, C.guard,
      show 1 ≤ 2 ^ bd from Nat.one_le_two_pow, show 2 ^ bd - 1 < 4294967296 by omega,
      Nat.mod_eq_of_lt (show 2 ^ bd - 1 < 4294967296 by omega)])
  let s1 : State := {s0 with locals := s0.locals.upd 3 (.int u32 (2 ^ bd - 1))}
  have f0 : EvE Gen.prog s1 (.var 0) (.int u32 v) := EvE.var rfl
  have f3 : EvE Gen.prog s1 (.var 3) (.int u32 (2 ^ bd - 1)) := EvE.var rfl
  have f2 : EvE Gen.prog s1 (.var 2) (.ptr ob 0) := EvE.var rfl
  have hmul : EvE Gen.prog s1 (.bin .mul (some u32) (.var 0) (.const (.int u32 255)))
      (.int u32 (v * 255 % 4294967296)) :=
    EvE.bin f0 (EvE.const _) (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u32, isPtr, ptrEq,
      show (⟨32, false⟩ : IntTy).modulus = 4294967296 from rfl])
  have hhalf : EvE Gen.prog s1 (.bin .div (some u32) (.var 3) (.const (.int u32 2)))
      (.int u32 ((2 ^ bd - 1) / 2)) :=
    EvE.bin f3 (EvE.const _) (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u32, isPtr, ptrEq, C.guard])
  have hsum : EvE Gen.prog s1 (.bin .add (some u32) (.bin .mul (some u32) (.var 0) (.const (.int u32 255)))
      (.bin .div (some u32) (.var 3) (.const (.int u32 2))))
      (.int u32 ((v * 255 % 4294967296 + (2 ^ bd - 1) / 2) % 4294967296)) :=
    EvE.bin hmul hhalf (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u32, isPtr, ptrEq,
      show (⟨32, false⟩ : IntTy).modulus = 4294967296 from rfl])
  have hquot : EvE Gen.prog s1 (.bin .div (some u32) (.bin .add (some u32) (.bin .mul (some u32) (.var 0) (.const (.int u32 255)))
      (.bin .div (some u32) (.var 3) (.const (.int u32 2)))) (.var 3))
      (.int u32 ((v * 255 % 4294967296 + (2 ^ bd - 1) / 2) % 4294967296 / (2 ^ bd - 1))) :=
    EvE.bin hsum f3 (by simp [evalBin, evalBinInt, binInt, intOf, IntTy.u32, isPtr, ptrEq, C.guard,
      show 2 ^ bd - 1 ≠ 0 by have := Nat.one_le_two_pow (n := bd); omega])
  have hcastb : EvE Gen.prog s1 (.cast u8 (.bin .div (some u32) (.bin .add (some u32) (.bin .mul (some u32) (.var 0) (.const (.int u32 255)))
      (.bin .div (some u32) (.var 3) (.const (.int u32 2)))) (.var 3)))
      (.int u8 ((v * 255 % 4294967296 + (2 ^ bd - 1) / 2) % 4294967296 / (2 ^ bd - 1) % 256)) :=
    EvE.cast hquot (by simp [evalCast, IntTy.u32, IntTy.u8, IntTy.modulus, show 2 ^ bd - 1 >= 0 from by omega,
      Nat.mod_eq_of_lt (show (v * 255 % 4294967296 + (2 ^ bd - 1) / 2) % 4294967296 / (2 ^ bd - 1) % 256 < 256 from by omega)])
  let Xb : Nat := (v * 255 % 4294967296 + (2 ^ bd - 1) / 2) % 4294967296 / (2 ^ bd - 1) % 256
  have hXb : Xb < 256 := Nat.mod_lt _ (by decide)
  have hspec : scaleTo8 v bd = some Xb := by
    unfold scaleTo8
    simp only [show bd ≠ 0 by omega, show ¬ (bd > 8) by omega, decide_false, Bool.or_false, Bool.false_or,
      if_false, Nat.mod_eq_of_lt hv, Xb, Nat.mul_comm]
    rfl
  have hmem : store s1.mem (.int u8) (.ptr ob 0) (.int u8 Xb) = .ok (m.upd ob (Xb.toUInt8 :: blk.tail)) := by
    simp only [s1, s0, store, writeBytes, hm, IntTy.u8, IntTy.bytes, ite_true, encodeLE, encodeLE_length]
    rw [if_pos (by simp; omega)]
    simp [List.drop_one, Nat.mod_eq_of_lt hXb]
  refine ⟨{s1 with mem := m.upd ob (Xb.toUInt8 :: blk.tail)}, ?_, ?_⟩
  · exact ExS.seq (ExS.ite cond htf ExS.skip)
      (ExS.seq (ExS.set hset3v) (ExS.seq (ExS.store f2 hcastb rfl hmem) (ExS.ret (EvE.const _))))
  · show (m.upd ob (Xb.toUInt8 :: blk.tail)) ob = _
    rw [Mem.upd_same, hspec]
    rfl

theorem ni_scale_to_8bit_exs_fail (m : Mem) (ob : Nat) (blk : List UInt8) (hm : m ob = some blk)
    (v bd : Nat) (hbd : bd = 0 ∨ (8 < bd ∧ bd < 256)) :
    ExS Gen.prog ⟨frameLocals [0, 1, 2] [.int u32 v, .int u8 bd, .ptr ob 0], m, false⟩
        Gen.ni_scale_to_8bit.body (.ret (some (.int i32 0)))
        ⟨frameLocals [0, 1, 2] [.int u32 v, .int u8 bd, .ptr ob 0], m, false⟩ := by
  let s0 : State := ⟨frameLocals [0, 1, 2] [.int u32 v, .int u8 bd, .ptr ob 0], m, false⟩
  have e1 : EvE Gen.prog s0 (.var 1) (.int u8 bd) := EvE.var rfl
  have e2 : EvE Gen.prog s0 (.var 2) (.ptr ob 0) := EvE.var rfl
  have c1 : EvE Gen.prog s0 (.cast u32 (.var 1)) (.int u32 bd) :=
    EvE.cast e1 (by simp [evalCast, IntTy.u8, IntTy.u32, IntTy.modulus, show bd < 4294967296 by omega,
      Nat.mod_eq_of_lt (show bd < 4294967296 by omega)])
  have c0 : EvE Gen.prog s0 (.const (.int u32 0)) (.int u32 0) := EvE.const _
  have c8 : EvE Gen.prog s0 (.const (.int u32 8)) (.int u32 8) := EvE.const _
  have eq0 : EvE Gen.prog s0 (.bin .eq (some u32) (.cast u32 (.var 1)) (.const (.int u32 0)))
      (boolVal (decide (bd = 0))) :=
    EvE.bin c1 c0 (by simp [evalBin, evalBinInt, binInt, intOf, isPtr, ptrEq, IntTy.u32, boolVal])
  have gt8 : EvE Gen.prog s0 (.bin .gt (some u32) (.cast u32 (.var 1)) (.const (.int u32 8)))
      (boolVal (decide (bd > 8))) :=
    EvE.bin c1 c8 (by simp [evalBin, evalBinInt, binInt, intOf, isPtr, ptrEq, IntTy.u32, boolVal])
  have eqnull : EvE Gen.prog s0 (.bin .eq none (.var 2) (.const .null)) (boolVal false) :=
    EvE.bin e2 (EvE.const _) (by simp [evalBin, isPtr, ptrEq, boolVal])
  have cond : EvE Gen.prog s0 (.lor (.lor (.bin .eq (some u32) (.cast u32 (.var 1)) (.const (.int u32 0)))
      (.bin .gt (some u32) (.cast u32 (.var 1)) (.const (.int u32 8))))
      (.bin .eq none (.var 2) (.const .null))) (boolVal true) := by
    rcases hbd with h0 | ⟨hl, _⟩
    · subst h0
      have hinner : EvE Gen.prog s0 (.lor (.bin .eq (some u32) (.cast u32 (.var 1)) (.const (.int u32 0)))
          (.bin .gt (some u32) (.cast u32 (.var 1)) (.const (.int u32 8)))) (boolVal true) :=
        EvE.lor_true (va := boolVal true) (by simpa using eq0) rfl
      exact EvE.lor_true hinner rfl
    · have hd0 : decide (bd = 0) = false := decide_eq_false (by omega)
      have hd8 : decide (bd > 8) = true := decide_eq_true hl
      have hinner : EvE Gen.prog s0 (.lor (.bin .eq (some u32) (.cast u32 (.var 1)) (.const (.int u32 0)))
          (.bin .gt (some u32) (.cast u32 (.var 1)) (.const (.int u32 8)))) (boolVal true) :=
        EvE.lor_false eq0 (by rw [hd0]; rfl) gt8 (by rw [hd8]; rfl)
      exact EvE.lor_true hinner rfl
  exact ExS.seq_ret (ExS.ite cond rfl (ExS.ret (EvE.const (v := .int i32 0))))

/-! ## `ni_paeth` -/

theorem EvE.cond_t' {p : Prog} {s : State} {c a b : Expr} {vc v} (hc : EvE p s c vc)
    (ht : truthy vc = .ok true) (ha : EvE p s a v) : EvE p s (.cond c a b) v :=
  EvE.cond hc ht (by simpa using ha)

theorem EvE.cond_f' {p : Prog} {s : State} {c a b : Expr} {vc v} (hc : EvE p s c vc)
    (hf : truthy vc = .ok false) (hb : EvE p s b v) : EvE p s (.cond c a b) v :=
  EvE.cond hc hf (by simpa using hb)

theorem ev_cast_u8_i32 {s : State} {i : Nat} {a : Nat} (ha : a < 256) (hl : s.locals i = some (.int u8 a)) :
    EvE Gen.prog s (.cast i32 (.var i)) (.int i32 (IntTy.wrap i32 (a : Int))) :=
  EvE.cast (EvE.var hl) (by simp [evalCast, IntTy.u8, wrap_i32_ofNat (show a < 2147483648 by omega),
    show (0 : Nat) < 1 from by decide])

theorem ev_absd {s : State} {ip ja : Nat} {x y : Int}
    (hx : -2147483648 ≤ x ∧ x ≤ 2147483647) (hy : -2147483648 ≤ y ∧ y ≤ 2147483647)
    (hxy1 : -2147483648 ≤ x - y ∧ x - y ≤ 2147483647) (hxy2 : -2147483648 ≤ y - x ∧ y - x ≤ 2147483647)
    (ep : EvE Gen.prog s (.var ip) (.int i32 (IntTy.wrap i32 x)))
    (ea : EvE Gen.prog s (.cast i32 (.var ja)) (.int i32 (IntTy.wrap i32 y))) :
    EvE Gen.prog s (.cond (.bin .gt (some i32) (.var ip) (.cast i32 (.var ja)))
      (.bin .sub (some i32) (.var ip) (.cast i32 (.var ja)))
      (.bin .sub (some i32) (.cast i32 (.var ja)) (.var ip)))
      (.int i32 (IntTy.wrap i32 (if x > y then x - y else y - x))) := by
  have tx := toInt_wrap_i32 hx.1 hx.2
  have ty := toInt_wrap_i32 hy.1 hy.2
  by_cases hxy : x > y
  · have hg : EvE Gen.prog s (.bin .gt (some i32) (.var ip) (.cast i32 (.var ja)))
        (boolVal (decide (x > y))) :=
      EvE.bin ep ea (by rw [bin_i32_gt, tx, ty])
    have hs : EvE Gen.prog s (.bin .sub (some i32) (.var ip) (.cast i32 (.var ja)))
        (.int i32 (IntTy.wrap i32 (x - y))) :=
      EvE.bin ep ea (by rw [bin_i32_sub, tx, ty, arith_i32_rng hxy1.1 hxy1.2])
    rw [if_pos hxy]
    exact EvE.cond_t' hg (by rw [decide_eq_true hxy]; rfl) hs
  · have hg : EvE Gen.prog s (.bin .gt (some i32) (.var ip) (.cast i32 (.var ja)))
        (boolVal (decide (x > y))) :=
      EvE.bin ep ea (by rw [bin_i32_gt, tx, ty])
    have hs : EvE Gen.prog s (.bin .sub (some i32) (.cast i32 (.var ja)) (.var ip))
        (.int i32 (IntTy.wrap i32 (y - x))) :=
      EvE.bin ea ep (by rw [bin_i32_sub, tx, ty, arith_i32_rng hxy2.1 hxy2.2])
    rw [if_neg hxy]
    exact EvE.cond_f' hg (by rw [decide_eq_false hxy]; rfl) hs

theorem ni_paeth_exs (m : Mem) (a b c : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) (ro : Bool) :
    ∃ s', ExS Gen.prog ⟨frameLocals [0, 1, 2] [.int u8 a, .int u8 b, .int u8 c], m, ro⟩
      Gen.ni_paeth.body (.ret (some (.int u8 (paeth a b c)))) s' := by
  let s0 : State := ⟨frameLocals [0, 1, 2] [.int u8 a, .int u8 b, .int u8 c], m, ro⟩
  have ca := ev_cast_u8_i32 (s := s0) (i := 0) ha rfl
  have cb := ev_cast_u8_i32 (s := s0) (i := 1) hb rfl
  have cc := ev_cast_u8_i32 (s := s0) (i := 2) hc rfl
  have hA : -2147483648 ≤ (a : Int) ∧ (a : Int) ≤ 2147483647 := by omega
  have hB : -2147483648 ≤ (b : Int) ∧ (b : Int) ≤ 2147483647 := by omega
  have hC : -2147483648 ≤ (c : Int) ∧ (c : Int) ≤ 2147483647 := by omega
  have hAB : -2147483648 ≤ (a : Int) + b ∧ (a : Int) + b ≤ 2147483647 := by omega
  have hP : -2147483648 ≤ (a : Int) + b - c ∧ (a : Int) + b - c ≤ 2147483647 := by omega
  have hP' : -2147483648 ≤ ((a : Int) + b - c) - a ∧ ((a : Int) + b - c) - a ≤ 2147483647 := by omega
  have hP'' : -2147483648 ≤ (a : Int) - ((a : Int) + b - c) ∧ (a : Int) - ((a : Int) + b - c) ≤ 2147483647 := by omega
  have hQ' : -2147483648 ≤ ((a : Int) + b - c) - b ∧ ((a : Int) + b - c) - b ≤ 2147483647 := by omega
  have hQ'' : -2147483648 ≤ (b : Int) - ((a : Int) + b - c) ∧ (b : Int) - ((a : Int) + b - c) ≤ 2147483647 := by omega
  have hR' : -2147483648 ≤ ((a : Int) + b - c) - c ∧ ((a : Int) + b - c) - c ≤ 2147483647 := by omega
  have hR'' : -2147483648 ≤ (c : Int) - ((a : Int) + b - c) ∧ (c : Int) - ((a : Int) + b - c) ≤ 2147483647 := by omega
  have hp0 : EvE Gen.prog s0 (.bin .add (some i32) (.cast i32 (.var 0)) (.cast i32 (.var 1)))
      (.int i32 (IntTy.wrap i32 ((a : Int) + b))) :=
    EvE.bin ca cb (by rw [bin_i32_add, toInt_wrap_i32 hA.1 hA.2, toInt_wrap_i32 hB.1 hB.2, arith_i32_rng hAB.1 hAB.2])
  have hp : EvE Gen.prog s0 (.bin .sub (some i32) (.bin .add (some i32) (.cast i32 (.var 0)) (.cast i32 (.var 1)))
      (.cast i32 (.var 2))) (.int i32 (IntTy.wrap i32 ((a : Int) + b - c))) :=
    EvE.bin hp0 cc (by rw [bin_i32_sub, toInt_wrap_i32 hAB.1 hAB.2, toInt_wrap_i32 hC.1 hC.2,
      arith_i32_rng hP.1 hP.2])
  let s1 : State := {s0 with locals := s0.locals.upd 3 (.int i32 (IntTy.wrap i32 ((a : Int) + b - c)))}
  have ep1 : EvE Gen.prog s1 (.var 3) (.int i32 (IntTy.wrap i32 ((a : Int) + b - c))) := EvE.var rfl
  have ea1 : EvE Gen.prog s1 (.cast i32 (.var 0)) (.int i32 (IntTy.wrap i32 (a : Int))) :=
    ev_cast_u8_i32 (s := s1) (i := 0) ha rfl
  have hpa := ev_absd (s := s1) (ip := 3) (ja := 0) hP hA hP' hP'' ep1 ea1
  let s2 : State := {s1 with locals := s1.locals.upd 4 (.int i32 (IntTy.wrap i32
      (if (a : Int) + b - c > a then ((a : Int) + b - c) - a else (a : Int) - ((a : Int) + b - c))))}
  have ep2 : EvE Gen.prog s2 (.var 3) (.int i32 (IntTy.wrap i32 ((a : Int) + b - c))) := EvE.var rfl
  have eb2 : EvE Gen.prog s2 (.cast i32 (.var 1)) (.int i32 (IntTy.wrap i32 (b : Int))) :=
    ev_cast_u8_i32 (s := s2) (i := 1) hb rfl
  have hpb := ev_absd (s := s2) (ip := 3) (ja := 1) hP hB hQ' hQ'' ep2 eb2
  let s3 : State := {s2 with locals := s2.locals.upd 5 (.int i32 (IntTy.wrap i32
      (if (a : Int) + b - c > b then ((a : Int) + b - c) - b else (b : Int) - ((a : Int) + b - c))))}
  have ep3 : EvE Gen.prog s3 (.var 3) (.int i32 (IntTy.wrap i32 ((a : Int) + b - c))) := EvE.var rfl
  have ec3 : EvE Gen.prog s3 (.cast i32 (.var 2)) (.int i32 (IntTy.wrap i32 (c : Int))) :=
    ev_cast_u8_i32 (s := s3) (i := 2) hc rfl
  have hpc := ev_absd (s := s3) (ip := 3) (ja := 2) hP hC hR' hR'' ep3 ec3
  let pa : Int := if (a : Int) + b - c > a then ((a : Int) + b - c) - a else (a : Int) - ((a : Int) + b - c)
  let pb : Int := if (a : Int) + b - c > b then ((a : Int) + b - c) - b else (b : Int) - ((a : Int) + b - c)
  let pc : Int := if (a : Int) + b - c > c then ((a : Int) + b - c) - c else (c : Int) - ((a : Int) + b - c)
  have hpa_r : -2147483648 ≤ pa ∧ pa ≤ 2147483647 := by
    simp only [pa]; split <;> omega
  have hpb_r : -2147483648 ≤ pb ∧ pb ≤ 2147483647 := by
    simp only [pb]; split <;> omega
  have hpc_r : -2147483648 ≤ pc ∧ pc ≤ 2147483647 := by
    simp only [pc]; split <;> omega
  have hval : paeth a b c = if pa ≤ pb && pa ≤ pc then a else if pb ≤ pc then b else c := by
    unfold paeth; rfl
  let s4 : State := {s3 with locals := s3.locals.upd 6 (.int i32 (IntTy.wrap i32 pc))}
  have le45 : EvE Gen.prog s4 (.bin .le (some i32) (.var 4) (.var 5)) (boolVal (decide (pa ≤ pb))) :=
    EvE.bin (EvE.var rfl) (EvE.var rfl)
      (by rw [bin_i32_le, toInt_wrap_i32 hpa_r.1 hpa_r.2, toInt_wrap_i32 hpb_r.1 hpb_r.2])
  have le46 : EvE Gen.prog s4 (.bin .le (some i32) (.var 4) (.var 6)) (boolVal (decide (pa ≤ pc))) :=
    EvE.bin (EvE.var rfl) (EvE.var rfl)
      (by rw [bin_i32_le, toInt_wrap_i32 hpa_r.1 hpa_r.2, toInt_wrap_i32 hpc_r.1 hpc_r.2])
  have le56 : EvE Gen.prog s4 (.bin .le (some i32) (.var 5) (.var 6)) (boolVal (decide (pb ≤ pc))) :=
    EvE.bin (EvE.var rfl) (EvE.var rfl)
      (by rw [bin_i32_le, toInt_wrap_i32 hpb_r.1 hpb_r.2, toInt_wrap_i32 hpc_r.1 hpc_r.2])
  have ev0 : EvE Gen.prog s4 (.var 0) (.int u8 a) := EvE.var rfl
  have ev1 : EvE Gen.prog s4 (.var 1) (.int u8 b) := EvE.var rfl
  have ev2 : EvE Gen.prog s4 (.var 2) (.int u8 c) := EvE.var rfl
  rw [hval]
  by_cases h45 : pa ≤ pb
  · by_cases h46 : pa ≤ pc
    · have cond1 : EvE Gen.prog s4 (.land (.bin .le (some i32) (.var 4) (.var 5)) (.bin .le (some i32) (.var 4) (.var 6)))
          (boolVal true) :=
        EvE.land_true le45 (by rw [decide_eq_true h45]; rfl) le46 (by rw [decide_eq_true h46]; rfl)
      rw [if_pos (by simp [h45, h46])]
      exact ⟨_, ExS.seq (ExS.set (i := 3) hp) (ExS.seq (ExS.set (i := 4) hpa) (ExS.seq (ExS.set (i := 5) hpb) (ExS.seq (ExS.set (i := 6) hpc)
        (ExS.seq_ret (ExS.ite (c := .land (.bin .le (some i32) (.var 4) (.var 5)) (.bin .le (some i32) (.var 4) (.var 6)))
          cond1 (bc := true) (a := .ret (some (.var 0))) (b := .skip) rfl (ExS.ret ev0))))))⟩
    · have cond1 : EvE Gen.prog s4 (.land (.bin .le (some i32) (.var 4) (.var 5)) (.bin .le (some i32) (.var 4) (.var 6)))
          (boolVal false) :=
        EvE.land_true le45 (by rw [decide_eq_true h45]; rfl) le46 (by rw [decide_eq_false h46]; rfl)
      rw [if_neg (by simp [h45, h46])]
      by_cases h56 : pb ≤ pc
      · rw [if_pos h56]
        exact ⟨_, ExS.seq (ExS.set (i := 3) hp) (ExS.seq (ExS.set (i := 4) hpa) (ExS.seq (ExS.set (i := 5) hpb) (ExS.seq (ExS.set (i := 6) hpc)
          (ExS.seq (ExS.ite (c := .land (.bin .le (some i32) (.var 4) (.var 5)) (.bin .le (some i32) (.var 4) (.var 6)))
            (bc := false) (a := .ret (some (.var 0))) (b := .skip) cond1 (by rfl) ExS.skip)
            (ExS.seq_ret (ExS.ite (c := .bin .le (some i32) (.var 5) (.var 6)) le56 (bc := true) (a := .ret (some (.var 1))) (b := .skip) (by rw [decide_eq_true h56]; rfl)
              (ExS.ret ev1)))))))⟩
      · rw [if_neg h56]
        exact ⟨_, ExS.seq (ExS.set (i := 3) hp) (ExS.seq (ExS.set (i := 4) hpa) (ExS.seq (ExS.set (i := 5) hpb) (ExS.seq (ExS.set (i := 6) hpc)
          (ExS.seq (ExS.ite (c := .land (.bin .le (some i32) (.var 4) (.var 5)) (.bin .le (some i32) (.var 4) (.var 6)))
            (bc := false) (a := .ret (some (.var 0))) (b := .skip) cond1 (by rfl) ExS.skip)
            (ExS.seq (ExS.ite (c := .bin .le (some i32) (.var 5) (.var 6)) (a := .ret (some (.var 1))) (b := .skip) le56
              (by rw [decide_eq_false h56]; rfl) ExS.skip) (ExS.ret ev2))))))⟩
  · have cond1 : EvE Gen.prog s4 (.land (.bin .le (some i32) (.var 4) (.var 5)) (.bin .le (some i32) (.var 4) (.var 6)))
        (boolVal false) :=
      EvE.land_false le45 (by rw [decide_eq_false h45]; rfl)
    rw [if_neg (by simp [h45])]
    by_cases h56 : pb ≤ pc
    · rw [if_pos h56]
      exact ⟨_, ExS.seq (ExS.set (i := 3) hp) (ExS.seq (ExS.set (i := 4) hpa) (ExS.seq (ExS.set (i := 5) hpb) (ExS.seq (ExS.set (i := 6) hpc)
        (ExS.seq (ExS.ite (c := .land (.bin .le (some i32) (.var 4) (.var 5)) (.bin .le (some i32) (.var 4) (.var 6)))
          (bc := false) (a := .ret (some (.var 0))) (b := .skip) cond1 (by rfl) ExS.skip)
          (ExS.seq_ret (ExS.ite (c := .bin .le (some i32) (.var 5) (.var 6)) le56 (bc := true) (a := .ret (some (.var 1))) (b := .skip) (by rw [decide_eq_true h56]; rfl)
            (ExS.ret ev1)))))))⟩
    · rw [if_neg h56]
      exact ⟨_, ExS.seq (ExS.set (i := 3) hp) (ExS.seq (ExS.set (i := 4) hpa) (ExS.seq (ExS.set (i := 5) hpb) (ExS.seq (ExS.set (i := 6) hpc)
        (ExS.seq (ExS.ite (c := .land (.bin .le (some i32) (.var 4) (.var 5)) (.bin .le (some i32) (.var 4) (.var 6)))
          (bc := false) (a := .ret (some (.var 0))) (b := .skip) cond1 (by rfl) ExS.skip)
          (ExS.seq (ExS.ite (c := .bin .le (some i32) (.var 5) (.var 6)) (a := .ret (some (.var 1))) (b := .skip) le56
            (by rw [decide_eq_false h56]; rfl) ExS.skip) (ExS.ret ev2))))))⟩
