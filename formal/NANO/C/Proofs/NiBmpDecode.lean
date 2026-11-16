/-
  BMP decode-loop refinement proofs — per-pixel helpers first,
  then the row/pixel loops, then `ni_bmp_decode_into` as a whole.
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Hoare
import NANO.C.Lemmas
import NANO.Spec
import NANO.Bmp
import NANO.C.Proofs.Core
import NANO.C.Proofs.NiGeometryTail

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 800000

namespace NANO.C.Proofs
open NANO NANO.C

theorem take_one_byteAt (d : List UInt8) (o : Nat) (h : o < d.length) :
    (d.drop o).take 1 = encodeLE 1 (byteAt d o) := by
  unfold NANO.byteAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  have : List.drop o d = d[o] :: List.drop (o + 1) d := by rw [List.drop_eq_getElem_cons h]
  rw [this, List.take_succ_cons, List.take_zero]
  simp [encodeLE]

/-! Elementary splice helpers for the three consecutive single-byte stores. -/

theorem take_append_length (l₁ l₂ : List α) (i : Nat) :
    (l₁ ++ l₂).take (l₁.length + i) = l₁ ++ l₂.take i := by
  induction l₁ with
  | nil => simp
  | cons x xs ih =>
      simp only [List.length_cons]
      have e : xs.length + 1 + i = (xs.length + i) + 1 := by omega
      rw [e]
      show (x :: (xs ++ l₂)).take (xs.length + i + 1) = x :: (xs ++ List.take i l₂)
      rw [List.take_succ_cons, ih]

theorem drop_append_length (l₁ l₂ : List α) (i : Nat) :
    (l₁ ++ l₂).drop (l₁.length + i) = l₂.drop i := by
  induction l₁ generalizing i with
  | nil => simp
  | cons x xs ih =>
      simp only [List.length_cons]
      have e : xs.length + 1 + i = (xs.length + i) + 1 := by omega
      rw [e]
      show ((xs ++ l₂).drop (xs.length + i)) = l₂.drop i
      rw [ih]

theorem splice_step (pre post : List UInt8) (a b : List UInt8) (ha : a.length = 1) :
    (pre ++ a ++ post).take (pre.length + 1) ++ b ++ (pre ++ a ++ post).drop (pre.length + 2)
      = pre ++ a ++ b ++ post.drop 1 := by
  have key1 := take_append_length pre (a ++ post) 1
  have key2 := drop_append_length (pre ++ a) post 1
  have htc : (a ++ post).take 1 = a := by
    rw [List.take_append_of_le_length (by omega)]
    rw [List.take_of_length_le (by omega)]
  rw [htc] at key1
  rw [show (pre ++ a).length + 1 = pre.length + 2 from by rw [List.length_append, ha]] at key2
  rw [← List.append_assoc] at key1
  rw [key1, key2]

theorem splice_enc_3 (obl : List UInt8) (x y : Nat) (dst : Nat)
    (ho : dst + 2 ≤ obl.length) :
    (obl.take dst ++ encodeLE 1 x ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 y ++ (obl.take dst ++ encodeLE 1 x ++ obl.drop (dst + 1)).drop (dst + 2)
      = obl.take dst ++ encodeLE 1 x ++ encodeLE 1 y ++ obl.drop (dst + 2) := by
  simp only [List.append_assoc]
  have ht : (obl.take dst).length = dst := List.length_take_of_le (by omega)
  have key1take : (encodeLE 1 x ++ obl.drop (dst + 1)).take 1 = encodeLE 1 x := by
    rw [List.take_append_of_le_length (by simp [NANO.C.encodeLE_length]), List.take_of_length_le (by simp [NANO.C.encodeLE_length])]
  have key1 := take_append_length (obl.take dst) (encodeLE 1 x ++ obl.drop (dst + 1)) 1
  rw [show (obl.take dst).length + 1 = dst + 1 from by rw [ht]] at key1
  rw [key1take] at key1
  have key2 := drop_append_length (obl.take dst ++ encodeLE 1 x) (obl.drop (dst + 1)) 1
  rw [show (obl.take dst ++ encodeLE 1 x).length + 1 = dst + 2 from by
    rw [List.length_append, ht]; rw [NANO.C.encodeLE_length]] at key2
  simp only [List.append_assoc] at key2
  rw [key1]
  rw [key2]
  simp [List.append_assoc]

theorem splice_enc_4 (obl : List UInt8) (x y z : Nat) (dst : Nat)
    (ho : dst + 3 ≤ obl.length) :
    ((obl.take dst ++ encodeLE 1 x ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 y ++
      (obl.take dst ++ encodeLE 1 x ++ obl.drop (dst + 1)).drop (dst + 2)).take (dst + 2) ++ encodeLE 1 z ++
    (((obl.take dst ++ encodeLE 1 x ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 y ++
      (obl.take dst ++ encodeLE 1 x ++ obl.drop (dst + 1)).drop (dst + 2))).drop (dst + 3)
      = obl.take dst ++ encodeLE 1 x ++ encodeLE 1 y ++ encodeLE 1 z ++ obl.drop (dst + 3) := by
  rw [splice_enc_3 obl x y dst (by omega)]
  have ht : (obl.take dst ++ encodeLE 1 x ++ encodeLE 1 y).length = dst + 2 := by
    rw [List.length_append, List.length_append, List.length_take_of_le (by omega)]
    simp [NANO.C.encodeLE_length]
  have key1 := take_append_length (obl.take dst ++ encodeLE 1 x ++ encodeLE 1 y) (obl.drop (dst + 2)) 0
  rw [ht] at key1
  simp only [Nat.add_zero] at key1
  rw [key1]
  simp only [List.take_zero, List.append_nil]
  have key2 := drop_append_length (obl.take dst ++ encodeLE 1 x ++ encodeLE 1 y) (obl.drop (dst + 2)) 1
  rw [show (obl.take dst ++ encodeLE 1 x ++ encodeLE 1 y).length + 1 = dst + 3 from by rw [ht]] at key2
  rw [List.drop_drop] at key2
  rw [List.append_assoc, key2]
  simp [List.append_assoc]

theorem mem_upd_other (m : Mem) (ob k : Nat) (blk : List UInt8) (h : k ≠ ob) :
    (m.upd ob blk) k = m k := by
  simp [Mem.upd, if_neg h]

/-- Byte load at `.ptr b i` for arbitrary length blocks. -/
theorem load_byte_dyn (m : Mem) (b : Nat) (d : List UInt8) (hm : m b = some d)
    (i : Nat) (hi : i < d.length) :
    load m (.int ⟨8, false⟩) (.ptr b i) = .ok (Val.int ⟨8, false⟩ (byteAt d i)) := by
  simp only [load, Ty.size]
  simp only [readBytes]
  rw [hm]
  have hsz : (Ty.int { width := 8, signed := false }).size = 1 := rfl
  have hBytes : IntTy.bytes { width := 8, signed := false } = 1 := rfl
  simp only [hsz, hBytes]
  rw [ite_eq_left (show i + 1 ≤ d.length from by omega)]
  rw [take_one_byteAt d i hi]
  simp [decodeLE_encodeLE, Nat.mod_eq_of_lt (byteAt_lt d i)]

/-- Byte store at `.ptr b i` for arbitrary length blocks. -/
theorem store_byte_dyn (m : Mem) (b : Nat) (obl : List UInt8) (hm : m b = some obl)
    (i : Nat) (hi : i < obl.length) (v : Nat) (hv : v < 256) :
    store m (.int ⟨8, false⟩) (.ptr b i) (.int ⟨8, false⟩ v)
      = .ok (m.upd b (obl.take i ++ encodeLE 1 v ++ obl.drop (i + 1))) := by
  have hbytes : IntTy.bytes ⟨8, false⟩ = 1 := rfl
  have hlen : (encodeLE 1 v).length = 1 := encodeLE_length 1 v
  simp only [store, writeBytes, hm, hbytes, hlen]
  rw [ite_true, ite_eq_left (show i + 1 ≤ obl.length from by omega)]

/-- `load`/`store` at the ptr-arithmetic shape produced by `.index`. -/
theorem load_byte_at (m : Mem) (b : Nat) (d : List UInt8) (hm : m b = some d)
    (i : Nat) (hi : i < d.length) :
    load m (.int ⟨8, false⟩) (.ptr b (0 + i * 1)) = .ok (Val.int ⟨8, false⟩ (byteAt d i)) := by
  have e : 0 + i * 1 = i := by omega
  rw [e]
  exact load_byte_dyn m b d hm i hi

theorem store_byte_at (m : Mem) (b : Nat) (obl : List UInt8) (hm : m b = some obl)
    (i : Nat) (hi : i < obl.length) (v : Nat) (hv : v < 256) :
    store m (.int ⟨8, false⟩) (.ptr b (0 + i * 1)) (.int ⟨8, false⟩ v)
      = .ok (m.upd b (obl.take i ++ encodeLE 1 v ++ obl.drop (i + 1))) := by
  have e : 0 + i * 1 = i := by omega
  rw [e]
  exact store_byte_dyn m b obl hm i hi v hv

theorem mem_upd_neq (m : Mem) (b k : Nat) (blk obl : List UInt8) (hm : m k = some obl) (hne : k ≠ b) :
    (m.upd b blk) k = some obl := by
  simp [Mem.upd, ite_eq_right hne, hm]

theorem mem_upd_eq (m : Mem) (b : Nat) (blk : List UInt8) :
    (m.upd b blk) b = some blk := by
  simp [Mem.upd]


/-- EvE fact: `.bin .add (some ⟨64, false⟩) (.var i) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ k)))`
    evaluates to the sum. Small, factored constant. -/
theorem EvE_u64_add_const {s : State} {i k sidx : Nat}
    (hs : s.locals i = some (.int ⟨64, false⟩ sidx)) (h : sidx + k < 2 ^ 64) (hc : k < 2 ^ 32) :
    EvE Gen.prog s
      (.bin .add (some ⟨64, false⟩) (.var i)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ k))))
      (.int ⟨64, false⟩ (sidx + k)) := by
  have hc' : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ k) = .ok (.int ⟨64, false⟩ k) :=
    u32_u64_cast k (by omega)
  exact EvE.bin (EvE.var hs) (EvE.cast (EvE.const _) hc') (bin_u64_add sidx k h)

/-- `ni_bmp_decode_raw_pixel` writes BGR(A) from s to d, returns 0. -/
theorem ni_bmp_decode_raw_pixel_exs (m : Mem) (d obl : List UInt8)
    (bd ob : Nat) (hm : m bd = some d) (hd : d.length < 2 ^ 64)
    (hob : m ob = some obl) (src dst c : Nat)
    (hs0 : src + 3 ≤ d.length) (hs4 : c = 4 → src + 4 ≤ d.length)
    (hd20 : dst + 3 ≤ obl.length) (hd24 : c = 4 → dst + 4 ≤ obl.length) (hclt : c ≤ 4)
    (hlen : obl.length < 2 ^ 64) (hd0 : bd ≠ ob) (h2ob : 2 ≠ ob)
    (ro : Bool) (hro : ro = false) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals [0, 1, 2, 3, 4] ([.ptr bd 0, .ptr ob 0, .int ⟨64, false⟩ src, .int ⟨64, false⟩ dst, .int ⟨64, false⟩ c] : List Val), m, ro⟩
      Gen.ni_bmp_decode_raw_pixel.body
      (.ret (some (.int ⟨32, true⟩ 0))) s' ∧
    s'.mem ob = some
      (obl.take dst
        ++ ((encodeLE 1 (byteAt d (src + 2))
          ++ encodeLE 1 (byteAt d (src + 1))
          ++ encodeLE 1 (byteAt d src))
          ++ (if c = 4 then encodeLE 1 (byteAt d (src + 3)) else []))
        ++ obl.drop (dst + (if c = 4 then 4 else 3))) ∧
    s'.mem bd = some d ∧
    s'.mem 2 = m 2 := by
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  let s0 : State := { locals := frameLocals [0, 1, 2, 3, 4] ([.ptr bd 0, .ptr ob 0, .int ⟨64, false⟩ src, .int ⟨64, false⟩ dst, .int ⟨64, false⟩ c] : List Val), mem := m, ro := ro }
  have hl0 : s0.locals 0 = some (.ptr bd 0) := rfl
  have hl1 : s0.locals 1 = some (.ptr ob 0) := rfl
  have hl2 : s0.locals 2 = some (.int ⟨64, false⟩ src) := rfl
  have hl3 : s0.locals 3 = some (.int ⟨64, false⟩ dst) := rfl
  have hl4 : s0.locals 4 = some (.int ⟨64, false⟩ c) := rfl
  have hSro : s0.ro = false := hro
  -- source addresses
  have hSrc0 : EvE Gen.prog s0 (.bin .add (some ⟨64, false⟩) (.var 2)
      (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) (.int ⟨64, false⟩ (src + 0)) :=
    EvE_u64_add_const (i := 2) (k := 0) hl2 (by omega) (by omega)
  have hSrc1 : EvE Gen.prog s0 (.bin .add (some ⟨64, false⟩) (.var 2)
      (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) (.int ⟨64, false⟩ (src + 1)) :=
    EvE_u64_add_const (i := 2) (k := 1) hl2 (by omega) (by omega)
  have hSrc2 : EvE Gen.prog s0 (.bin .add (some ⟨64, false⟩) (.var 2)
      (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 2)))) (.int ⟨64, false⟩ (src + 2)) :=
    EvE_u64_add_const (i := 2) (k := 2) hl2 (by omega) (by omega)
  have hSrc3 : EvE Gen.prog s0 (.bin .add (some ⟨64, false⟩) (.var 2)
      (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3)))) (.int ⟨64, false⟩ (src + 3)) :=
    EvE_u64_add_const (i := 2) (k := 3) hl2 (by omega) (by omega)
  have hByte0 : EvE Gen.prog s0 (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 2)))) 1))
      (.int ⟨8, false⟩ (byteAt d (src + 2))) :=
    EvE.load (EvE.index (EvE.var hl0) hSrc2 (ptrAddN_ok hm (by omega)))
      (load_byte_at m bd d hm (src + 2) (by omega))
  have hByte1 : EvE Gen.prog s0 (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) 1))
      (.int ⟨8, false⟩ (byteAt d (src + 1))) :=
    EvE.load (EvE.index (EvE.var hl0) hSrc1 (ptrAddN_ok hm (by omega)))
      (load_byte_at m bd d hm (src + 1) (by omega))
  have hByte2 : EvE Gen.prog s0 (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) 1))
      (.int ⟨8, false⟩ (byteAt d src)) :=
    EvE.load (EvE.index (EvE.var hl0) hSrc0 (ptrAddN_ok hm (by omega)))
      (load_byte_at m bd d hm src (by omega))
  -- ==== store 0: out[dst] = bytes[src + 2] ====
  have hAddr0 : EvE Gen.prog s0 (.index (.var 1)
      (.bin .add (some ⟨64, false⟩) (.var 3)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) 1) (.ptr ob (0 + (dst + 0) * 1)) :=
    EvE.index (EvE.var hl1)
      (EvE_u64_add_const (i := 3) (k := 0) hl3 (by omega) (by omega))
      (ptrAddN_ok hob (by omega))
  have hStore0 : ExS Gen.prog s0
      (.store (.int ⟨8, false⟩) (.index (.var 1)
        (.bin .add (some ⟨64, false⟩) (.var 3)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) 1)
        (.load (.int ⟨8, false⟩) (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 2)))) 1)))
      .normal { s0 with mem := m.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)) } :=
    ExS.store hAddr0 hByte0 hSro
      (store_byte_at m ob obl hob dst (by omega) (byteAt d (src + 2)) (byteAt_lt d (src + 2)))
  let s1 : State := { s0 with mem := m.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)) }
  have hMem1bd : s1.mem bd = some d := by
    show (m.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1))) bd = some d
    exact mem_upd_neq m ob bd (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)) d hm hd0
  have hMem1 : s1.mem ob = some (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)) := by
    show (m.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1))) ob = some (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1))
    exact mem_upd_eq m ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1))
  have hlen_blk0 : (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).length = obl.length := by
    rw [List.length_append, List.length_append, List.length_drop, List.length_take_of_le (by omega)]
    rw [NANO.C.encodeLE_length]
    omega
  -- ==== store 1: out[dst + 1] = bytes[src + 1] ====
  have hAddr1 : EvE Gen.prog s1 (.index (.var 1)
      (.bin .add (some ⟨64, false⟩) (.var 3)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) 1) (.ptr ob (0 + (dst + 1) * 1)) :=
    EvE.index (EvE.var (show s1.locals 1 = some (.ptr ob 0) from rfl))
      (EvE_u64_add_const (i := 3) (k := 1) (show s1.locals 3 = some (.int ⟨64, false⟩ dst) from rfl) (by omega) (by omega))
      (ptrAddN_ok hMem1 (by rw [hlen_blk0]; omega))
  have hSrc1s1 : EvE Gen.prog s1 (.bin .add (some ⟨64, false⟩) (.var 2)
      (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) (.int ⟨64, false⟩ (src + 1)) :=
    EvE_u64_add_const (i := 2) (k := 1) (by rw [show s1.locals 2 = s0.locals 2 from rfl]; exact hl2) (by omega) (by omega)
  have hByte1s1 : EvE Gen.prog s1 (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) 1))
      (.int ⟨8, false⟩ (byteAt d (src + 1))) :=
    EvE.load
      (EvE.index (EvE.var (show s1.locals 0 = some (.ptr bd 0) from rfl)) hSrc1s1
        (ptrAddN_ok hMem1bd (by omega)))
      (load_byte_at s1.mem bd d hMem1bd (src + 1) (by omega))
  have hStore1 : ExS Gen.prog s1
      (.store (.int ⟨8, false⟩) (.index (.var 1)
        (.bin .add (some ⟨64, false⟩) (.var 3)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) 1)
        (.load (.int ⟨8, false⟩) (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) 1)))
      .normal { s1 with mem := s1.mem.upd ob ((obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (src + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).drop (dst + 2)) } :=
    ExS.store hAddr1 hByte1s1 (by rw [show s1.ro = s0.ro from rfl]; exact hSro)
      (store_byte_at s1.mem ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)) hMem1 (dst + 1) (by rw [hlen_blk0]; omega) (byteAt d (src + 1)) (byteAt_lt d (src + 1)))
  let s2 : State := { s1 with mem := s1.mem.upd ob ((obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (src + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).drop (dst + 2)) }
  have hMem2bd : s2.mem bd = some d := by
    show ((s1.mem.upd ob ((obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (src + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).drop (dst + 2))) bd) = some d
    exact mem_upd_neq s1.mem ob bd ((obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (src + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).drop (dst + 2)) d hMem1bd hd0
  have hMem2 : s2.mem ob = some ((obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (src + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).drop (dst + 2)) := by
    show ((s1.mem.upd ob ((obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (src + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).drop (dst + 2))) ob) = some ((obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (src + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).drop (dst + 2))
    exact mem_upd_eq s1.mem ob ((obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (src + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).drop (dst + 2))
  -- ==== store 2: out[dst + 2] = bytes[src] ====
  have hblk1 := splice_enc_3 obl (byteAt d (src + 2)) (byteAt d (src + 1)) dst (by omega)
  have htake : (obl.take dst).length = dst := List.length_take_of_le (by omega)
  have hlen_p : (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ obl.drop (dst + 2)).length = obl.length := by
    simp only [List.length_append, List.length_drop, List.length_take_of_le (by omega), Nat.min_eq_left (by omega : dst ≤ obl.length), NANO.C.encodeLE_length]
    omega
  have hSrc0s2 : EvE Gen.prog s2 (.bin .add (some ⟨64, false⟩) (.var 2)
      (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) (.int ⟨64, false⟩ (src + 0)) :=
    EvE_u64_add_const (i := 2) (k := 0) (by rw [show s2.locals 2 = s0.locals 2 from rfl]; exact hl2) (by omega) (by omega)
  have hByte2s2 : EvE Gen.prog s2 (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) 1))
      (.int ⟨8, false⟩ (byteAt d src)) :=
    EvE.load
      (EvE.index (EvE.var (show s2.locals 0 = some (.ptr bd 0) from rfl)) hSrc0s2
        (ptrAddN_ok hMem2bd (by omega)))
      (load_byte_at s2.mem bd d hMem2bd src (by omega))
  have hMem2flat : s2.mem ob = some (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ obl.drop (dst + 2)) := by
    rw [hblk1] at hMem2
    exact hMem2
  have hlen_blk1_flat : (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ obl.drop (dst + 2)).length = obl.length := by
    simp only [List.length_append, List.length_drop, List.length_take_of_le (by omega), Nat.min_eq_left (by omega : dst ≤ obl.length), NANO.C.encodeLE_length]
    omega
  have hAddr2 : EvE Gen.prog s2 (.index (.var 1)
      (.bin .add (some ⟨64, false⟩) (.var 3)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 2)))) 1) (.ptr ob (0 + (dst + 2) * 1)) :=
    EvE.index (EvE.var (show s2.locals 1 = some (.ptr ob 0) from rfl))
      (EvE_u64_add_const (i := 3) (k := 2) (show s2.locals 3 = some (.int ⟨64, false⟩ dst) from rfl) (by omega) (by omega))
      (ptrAddN_ok hMem2flat (by rw [hlen_blk1_flat]; omega))
  have hblk2 := splice_enc_4 obl (byteAt d (src + 2)) (byteAt d (src + 1)) (byteAt d src) dst (by omega)
  have hblk2' := hblk1
  have hL1 : (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1))).length = dst + 2 := by
    rw [List.length_append, List.length_append, List.length_take_of_le (by omega)]
    rw [NANO.C.encodeLE_length, NANO.C.encodeLE_length]
  have htake : List.take (dst + 2) (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ obl.drop (dst + 2)) = obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) := by
    rw [show dst + 2 = (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1))).length from hL1.symm]
    exact List.take_append_length
  have hdrop : List.drop (dst + 2 + 1) (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ obl.drop (dst + 2)) = obl.drop (dst + 3) := by
    rw [show dst + 2 + 1 = (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1))).length + 1 from by rw [hL1]]
    rw [drop_append_length (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1))) (obl.drop (dst + 2)) 1]
    rw [List.drop_drop]
    rw [hL1]
  have hMem2_final : store s2.mem (.int ⟨8, false⟩) (.ptr ob (0 + (dst + 2) * 1)) (.int ⟨8, false⟩ (byteAt d src)) = .ok (s2.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3))) := by
    rw [store_byte_at s2.mem ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ obl.drop (dst + 2)) hMem2flat (dst + 2) (by rw [hlen_blk1_flat]; omega) (byteAt d src) (byteAt_lt d src)]
    rw [htake, hdrop]
  have hStore2 : ExS Gen.prog s2
      (.store (.int ⟨8, false⟩) (.index (.var 1)
        (.bin .add (some ⟨64, false⟩) (.var 3)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 2)))) 1)
        (.load (.int ⟨8, false⟩) (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) 1)))
      .normal { s2 with mem := s2.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3)) } :=
    ExS.store hAddr2 hByte2s2 (by rw [show s2.ro = s0.ro from rfl]; exact hSro) hMem2_final
  let s3 : State := { s2 with mem := s2.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3)) }
  have hMem3bd : s3.mem bd = some d := by
    show ((s2.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3))) bd) = some d
    exact mem_upd_neq s2.mem ob bd (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3)) d hMem2bd hd0
  have hMem3 : s3.mem ob = some (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3)) := by
    show ((s2.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3))) ob) = some (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3))
    exact mem_upd_eq s2.mem ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3))
  -- ==== the channels branch ====
  have hlen_3flat : (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3)).length = obl.length := by
    simp only [List.length_append, List.length_drop, List.length_take_of_le (by omega), Nat.min_eq_left (by omega : dst ≤ obl.length), NANO.C.encodeLE_length]
    omega
  have hL3 : (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src)).length = dst + 3 := by
    rw [List.length_append, List.length_append, List.length_append, List.length_take_of_le (by omega)]
    rw [NANO.C.encodeLE_length, NANO.C.encodeLE_length, NANO.C.encodeLE_length]
  have htake4 : List.take (dst + 3) (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3)) = obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) := by
    rw [show dst + 3 = (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src)).length from hL3.symm]
    exact List.take_append_length
  have hdrop4 : List.drop (dst + 3 + 1) (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3)) = obl.drop (dst + 4) := by
    rw [show dst + 3 + 1 = (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src)).length + 1 from by rw [hL3]]
    rw [drop_append_length (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src)) (obl.drop (dst + 3)) 1]
    rw [List.drop_drop]
    rw [hL3]
  by_cases hc : c = 4
  · -- 32-bit output: 4th store executes
    have hs4' : src + 4 ≤ d.length := hs4 hc
    have hd24' : dst + 4 ≤ obl.length := hd24 hc
    have heq : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ 4) = .ok (.int ⟨64, false⟩ 4) :=
      u32_u64_cast 4 (by omega)
    have hcv : EvE Gen.prog s3 (.bin .eq (some ⟨64, false⟩) (.var 4) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))) (boolVal true) := by
      subst hc
      have h : evalBin .eq (some ⟨64, false⟩) (.int ⟨64, false⟩ 4) (.int ⟨64, false⟩ 4) = .ok (boolVal true) := rfl
      exact EvE.bin (EvE.var (show s3.locals 4 = some (.int ⟨64, false⟩ 4) from rfl)) (EvE.cast (EvE.const _) heq) h
    have hAddr4 : EvE Gen.prog s3 (.index (.var 1)
        (.bin .add (some ⟨64, false⟩) (.var 3)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3)))) 1) (.ptr ob (0 + (dst + 3) * 1)) :=
      EvE.index (EvE.var (show s3.locals 1 = some (.ptr ob 0) from rfl))
        (EvE_u64_add_const (i := 3) (k := 3) (show s3.locals 3 = some (.int ⟨64, false⟩ dst) from rfl) (by omega) (by omega))
        (ptrAddN_ok hMem3 (by rw [hlen_3flat]; omega))
    have hSrc3s3 : EvE Gen.prog s3 (.bin .add (some ⟨64, false⟩) (.var 2)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3)))) (.int ⟨64, false⟩ (src + 3)) :=
      EvE_u64_add_const (i := 2) (k := 3) (by rw [show s3.locals 2 = s0.locals 2 from rfl]; exact hl2) (by omega) (by omega)
    have hByte4s3 : EvE Gen.prog s3 (.load (.int ⟨8, false⟩)
        (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3)))) 1))
        (.int ⟨8, false⟩ (byteAt d (src + 3))) :=
      EvE.load
        (EvE.index (EvE.var (show s3.locals 0 = some (.ptr bd 0) from rfl)) hSrc3s3
          (ptrAddN_ok hMem3bd (by omega)))
        (load_byte_at s3.mem bd d hMem3bd (src + 3) (by omega))
    have hIh4 : store s3.mem (.int ⟨8, false⟩) (.ptr ob (0 + (dst + 3) * 1)) (.int ⟨8, false⟩ (byteAt d (src + 3)))
        = .ok (s3.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ encodeLE 1 (byteAt d (src + 3)) ++ obl.drop (dst + 4))) := by
      rw [store_byte_at s3.mem ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3)) hMem3 (dst + 3) (by rw [hlen_3flat]; omega) (byteAt d (src + 3)) (byteAt_lt d (src + 3))]
      rw [htake4, hdrop4]
    let s4 : State := { s3 with mem := s3.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ encodeLE 1 (byteAt d (src + 3)) ++ obl.drop (dst + 4)) }
    have hIf4 : ExS Gen.prog s3
        (.ite (.bin .eq (some ⟨64, false⟩) (.var 4)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))
          (.store (.int ⟨8, false⟩) (.index (.var 1)
            (.bin .add (some ⟨64, false⟩) (.var 3)
              (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3)))) 1)
            (.load (.int ⟨8, false⟩) (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2)
              (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3)))) 1))) .skip)
        .normal s4 :=
      ExS.ite hcv truthy_true (ExS.store hAddr4 hByte4s3 (by rw [show s3.ro = s0.ro from rfl]; exact hSro) hIh4)
    refine ⟨s4, ?_, ?_, ?_, ?_⟩
    · show ExS Gen.prog s0 Gen.ni_bmp_decode_raw_pixel.body (.ret (some (.int ⟨32, true⟩ 0))) s4
      exact ExS.seq hStore0 (ExS.seq hStore1 (ExS.seq hStore2 (ExS.seq hIf4 (ExS.ret (EvE.const _)))))
    · show ((s3.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ encodeLE 1 (byteAt d (src + 3)) ++ obl.drop (dst + 4))) ob) = some _
      rw [mem_upd_eq]
      rw [ite_eq_left hc, ite_eq_left hc]
      simp [List.append_assoc]
    · show ((s3.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ encodeLE 1 (byteAt d (src + 3)) ++ obl.drop (dst + 4))) bd) = some d
      rw [mem_upd_other s3.mem ob bd _ hd0]
      exact hMem3bd
    · show ((s3.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ encodeLE 1 (byteAt d (src + 3)) ++ obl.drop (dst + 4))) 2) = m 2
      rw [mem_upd_other s3.mem ob 2 _ h2ob]
      show ((s2.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3))) 2) = m 2
      rw [mem_upd_other s2.mem ob 2 _ h2ob]
      show ((s1.mem.upd ob ((obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (src + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).drop (dst + 2))) 2) = m 2
      rw [mem_upd_other s1.mem ob 2 _ h2ob]
      show ((m.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1))) 2) = m 2
      rw [mem_upd_other m ob 2 _ h2ob]
  · -- 24-bit output: `.ite` takes .skip
    have heq : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ 4) = .ok (.int ⟨64, false⟩ 4) :=
      u32_u64_cast 4 (by omega)
    have hcv : EvE Gen.prog s3 (.bin .eq (some ⟨64, false⟩) (.var 4) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))) (boolVal false) := by
      have h : evalBin .eq (some ⟨64, false⟩) (.int ⟨64, false⟩ c) (.int ⟨64, false⟩ 4) = .ok (boolVal false) := by
        rw [bin_u64_eq]
        rw [show decide (c = 4) = false from by
          cases hdec : decide (c = 4) with
          | true => rw [decide_eq_true_eq] at hdec; exact absurd hdec hc
          | false => rfl]
      exact EvE.bin (EvE.var (show s3.locals 4 = some (.int ⟨64, false⟩ c) from rfl)) (EvE.cast (EvE.const _) heq) h
    have hIf4 : ExS Gen.prog s3
        (.ite (.bin .eq (some ⟨64, false⟩) (.var 4)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))
          (.store (.int ⟨8, false⟩) (.index (.var 1)
            (.bin .add (some ⟨64, false⟩) (.var 3)
              (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3)))) 1)
            (.load (.int ⟨8, false⟩) (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2)
              (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 3)))) 1))) .skip)
        .normal s3 :=
      ExS.ite hcv truthy_false ExS.skip
    refine ⟨s3, ?_, ?_, ?_, ?_⟩
    · show ExS Gen.prog s0 Gen.ni_bmp_decode_raw_pixel.body (.ret (some (.int ⟨32, true⟩ 0))) s3
      exact ExS.seq hStore0 (ExS.seq hStore1 (ExS.seq hStore2 (ExS.seq hIf4 (ExS.ret (EvE.const _)))))
    · show ((s2.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3))) ob) = some _
      rw [mem_upd_eq]
      rw [ite_eq_right hc, ite_eq_right hc]
      simp [List.append_nil, List.append_assoc]
    · show ((s2.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3))) bd) = some d
      rw [mem_upd_other s2.mem ob bd _ hd0]
      exact hMem2bd
    · show ((s2.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ encodeLE 1 (byteAt d (src + 1)) ++ encodeLE 1 (byteAt d src) ++ obl.drop (dst + 3))) 2) = m 2
      rw [mem_upd_other s2.mem ob 2 _ h2ob]
      show ((s1.mem.upd ob ((obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (src + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1)).drop (dst + 2))) 2) = m 2
      rw [mem_upd_other s1.mem ob 2 _ h2ob]
      show ((m.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (src + 2)) ++ obl.drop (dst + 1))) 2) = m 2
      rw [mem_upd_other m ob 2 _ h2ob]

/-- `ni_bmp_decode_indexed_pixel` with an in-range index writes BGR from the
    palette and returns 0. Locals: 0=bytes, 1=out, 2=src_base, 3=x, 4=dst,
    5=palette_offset, 6=palette_entries, 7=idx -/
theorem ni_bmp_decode_indexed_pixel_ok_exs (m : Mem) (d obl : List UInt8)
    (bd ob : Nat) (hm : m bd = some d) (hd : d.length < 2 ^ 64)
    (hob : m ob = some obl) (src_base x dst palette_offset palette_entries : Nat)
    (hd0 : bd ≠ ob) (h2ob : 2 ≠ ob)
    (hs : src_base + x < d.length)
    (hp : palette_offset + byteAt d (src_base + x) * 4 + 3 ≤ d.length)
    (hd2 : dst + 3 ≤ obl.length) (hclt : byteAt d (src_base + x) < palette_entries)
    (hlen : obl.length < 2 ^ 64)
    (ro : Bool) (hro : ro = false) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals [0, 1, 2, 3, 4, 5, 6] ([.ptr bd 0, .ptr ob 0, .int ⟨64, false⟩ src_base, .int ⟨64, false⟩ x, .int ⟨64, false⟩ dst, .int ⟨64, false⟩ palette_offset, .int ⟨64, false⟩ palette_entries] : List Val), m, ro⟩
      Gen.ni_bmp_decode_indexed_pixel.body
      (.ret (some (.int ⟨32, true⟩ 0))) s' ∧
    s'.mem ob = some
      (obl.take dst
        ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2))
        ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1))
        ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4))
        ++ obl.drop (dst + 3)) ∧
    s'.mem bd = some d ∧
    s'.mem 2 = m 2 := by
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  have hblt : byteAt d (src_base + x) < 256 := byteAt_lt d (src_base + x)
  let s0 : State := { locals := frameLocals [0, 1, 2, 3, 4, 5, 6] ([.ptr bd 0, .ptr ob 0, .int ⟨64, false⟩ src_base, .int ⟨64, false⟩ x, .int ⟨64, false⟩ dst, .int ⟨64, false⟩ palette_offset, .int ⟨64, false⟩ palette_entries] : List Val), mem := m, ro := ro }
  have hl0 : s0.locals 0 = some (.ptr bd 0) := rfl
  have hl1 : s0.locals 1 = some (.ptr ob 0) := rfl
  have hl2 : s0.locals 2 = some (.int ⟨64, false⟩ src_base) := rfl
  have hl3 : s0.locals 3 = some (.int ⟨64, false⟩ x) := rfl
  have hl4 : s0.locals 4 = some (.int ⟨64, false⟩ dst) := rfl
  have hl5 : s0.locals 5 = some (.int ⟨64, false⟩ palette_offset) := rfl
  have hl6 : s0.locals 6 = some (.int ⟨64, false⟩ palette_entries) := rfl
  have hSro : s0.ro = false := hro
  -- ==== load the index byte, cast to u64, set local 7 ====
  have hSrcX : EvE Gen.prog s0 (.bin .add (some ⟨64, false⟩) (.var 2) (.var 3)) (.int ⟨64, false⟩ (src_base + x)) :=
    EvE.bin (EvE.var hl2) (EvE.var hl3) (bin_u64_add src_base x (by omega))
  have hIdx : EvE Gen.prog s0 (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2) (.var 3)) 1))
      (.int ⟨8, false⟩ (byteAt d (src_base + x))) :=
    EvE.load (EvE.index (EvE.var hl0) hSrcX (ptrAddN_ok hm (by omega)))
      (load_byte_at m bd d hm (src_base + x) (by omega))
  have hCastIdx : evalCast ⟨64, false⟩ (.int ⟨8, false⟩ (byteAt d (src_base + x))) = .ok (.int ⟨64, false⟩ (byteAt d (src_base + x))) := by
    simp [evalCast, IntTy.modulus, IntTy.wrap, Int.ofNat_lt, show byteAt d (src_base + x) < 18446744073709551616 from by omega]
  have hIdx64 : EvE Gen.prog s0 (.cast ⟨64, false⟩ (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2) (.var 3)) 1)))
      (.int ⟨64, false⟩ (byteAt d (src_base + x))) :=
    EvE.cast hIdx hCastIdx
  have hSet : ExS Gen.prog s0 (.set 7 (.cast ⟨64, false⟩ (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2) (.var 3)) 1))))
      .normal { s0 with locals := s0.locals.upd 7 (.int ⟨64, false⟩ (byteAt d (src_base + x))) } :=
    ExS.set hIdx64
  let s1 : State := { s0 with locals := s0.locals.upd 7 (.int ⟨64, false⟩ (byteAt d (src_base + x))) }
  have hl0_1 : s1.locals 0 = some (.ptr bd 0) := rfl
  have hl1_1 : s1.locals 1 = some (.ptr ob 0) := rfl
  have hl2_1 : s1.locals 2 = some (.int ⟨64, false⟩ src_base) := rfl
  have hl3_1 : s1.locals 3 = some (.int ⟨64, false⟩ x) := rfl
  have hl4_1 : s1.locals 4 = some (.int ⟨64, false⟩ dst) := rfl
  have hl5_1 : s1.locals 5 = some (.int ⟨64, false⟩ palette_offset) := rfl
  have hl6_1 : s1.locals 6 = some (.int ⟨64, false⟩ palette_entries) := rfl
  have hl7_1 : s1.locals 7 = some (.int ⟨64, false⟩ (byteAt d (src_base + x))) := rfl
  -- ==== idx < palette_entries, so the error branch is not taken ====
  have hge_false : EvE Gen.prog s1 (.bin .ge (some ⟨64, false⟩) (.var 7) (.var 6)) (boolVal false) := by
    have h := bin_u64_ge (byteAt d (src_base + x)) palette_entries
    rw [show decide (byteAt d (src_base + x) ≥ palette_entries) = false from decide_eq_false (by omega)] at h
    exact EvE.bin (EvE.var hl7_1) (EvE.var hl6_1) h
  have hIfSkip : ExS Gen.prog s1
      (.ite (.bin .ge (some ⟨64, false⟩) (.var 7) (.var 6)) (.ret (some (.const (.int ⟨32, true⟩ 11)))) .skip)
      .normal s1 :=
    ExS.ite hge_false truthy_false ExS.skip
  -- ==== shared palette addressing facts ====
  have hcast0 : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ 0) = .ok (.int ⟨64, false⟩ 0) := u32_u64_cast 0 (by omega)
  have hcast1 : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ 1) = .ok (.int ⟨64, false⟩ 1) := u32_u64_cast 1 (by omega)
  have hcast2 : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ 2) = .ok (.int ⟨64, false⟩ 2) := u32_u64_cast 2 (by omega)
  have hcast4 : evalCast ⟨64, false⟩ (.int ⟨32, false⟩ 4) = .ok (.int ⟨64, false⟩ 4) := u32_u64_cast 4 (by omega)
  have hMul : EvE Gen.prog s1 (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))) (.int ⟨64, false⟩ (byteAt d (src_base + x) * 4)) :=
    EvE.bin (EvE.var hl7_1) (EvE.cast (EvE.const _) hcast4) (bin_u64_mul _ _ (by omega))
  have hP0 : EvE Gen.prog s1 (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.int ⟨64, false⟩ (palette_offset + byteAt d (src_base + x) * 4)) :=
    EvE.bin (EvE.var hl5_1) hMul (bin_u64_add palette_offset _ (by omega))
  have hAddrP0 : EvE Gen.prog s1 (.bin .add (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) (.int ⟨64, false⟩ (palette_offset + byteAt d (src_base + x) * 4 + 0)) :=
    EvE.bin hP0 (EvE.cast (EvE.const _) hcast0) (bin_u64_add _ 0 (by omega))
  have hAddrP1 : EvE Gen.prog s1 (.bin .add (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) (.int ⟨64, false⟩ (palette_offset + byteAt d (src_base + x) * 4 + 1)) :=
    EvE.bin hP0 (EvE.cast (EvE.const _) hcast1) (bin_u64_add _ 1 (by omega))
  have hAddrP2 : EvE Gen.prog s1 (.bin .add (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 2)))) (.int ⟨64, false⟩ (palette_offset + byteAt d (src_base + x) * 4 + 2)) :=
    EvE.bin hP0 (EvE.cast (EvE.const _) hcast2) (bin_u64_add _ 2 (by omega))
  have hByteP0 : EvE Gen.prog s1 (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) 1))
      (.int ⟨8, false⟩ (byteAt d (palette_offset + byteAt d (src_base + x) * 4))) :=
    EvE.load (EvE.index (EvE.var hl0_1) hAddrP0 (ptrAddN_ok hm (by omega)))
      (load_byte_at m bd d hm _ (by omega))
  have hByteP1 : EvE Gen.prog s1 (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) 1))
      (.int ⟨8, false⟩ (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1))) :=
    EvE.load (EvE.index (EvE.var hl0_1) hAddrP1 (ptrAddN_ok hm (by omega)))
      (load_byte_at m bd d hm _ (by omega))
  have hByteP2 : EvE Gen.prog s1 (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 2)))) 1))
      (.int ⟨8, false⟩ (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2))) :=
    EvE.load (EvE.index (EvE.var hl0_1) hAddrP2 (ptrAddN_ok hm (by omega)))
      (load_byte_at m bd d hm _ (by omega))
  -- ==== store 0: out[dst] = bytes[p0 + 2] ====
  have hAddrO0 : EvE Gen.prog s1 (.index (.var 1)
      (.bin .add (some ⟨64, false⟩) (.var 4)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) 1) (.ptr ob (0 + (dst + 0) * 1)) :=
    EvE.index (EvE.var hl1_1)
      (EvE_u64_add_const (i := 4) (k := 0) hl4_1 (by omega) (by omega))
      (ptrAddN_ok hob (by omega))
  have hStore0 : ExS Gen.prog s1
      (.store (.int ⟨8, false⟩) (.index (.var 1)
        (.bin .add (some ⟨64, false⟩) (.var 4)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) 1)
        (.load (.int ⟨8, false⟩) (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 2)))) 1)))
      .normal { s1 with mem := s1.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)) } :=
    ExS.store hAddrO0 hByteP2 (by rw [show s1.ro = s0.ro from rfl]; exact hSro)
      (store_byte_at s1.mem ob obl (by rw [show s1.mem ob = m ob from rfl]; exact hob) dst (by omega) (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) (byteAt_lt d _))
  let s2 : State := { s1 with mem := s1.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)) }
  have hMem2bd : s2.mem bd = some d := by
    show ((s1.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1))) bd) = some d
    exact mem_upd_neq s1.mem ob bd (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)) d (by rw [show s1.mem bd = m bd from rfl]; exact hm) hd0
  have hMem2 : s2.mem ob = some (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)) := by
    show ((s1.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1))) ob) = some (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1))
    exact mem_upd_eq s1.mem ob (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1))
  have hlen_blk0 : (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).length = obl.length := by
    rw [List.length_append, List.length_append, List.length_drop, List.length_take_of_le (by omega)]
    rw [NANO.C.encodeLE_length]
    omega
  -- ==== store 1: out[dst + 1] = bytes[p0 + 1] ====
  have hAddrO1 : EvE Gen.prog s2 (.index (.var 1)
      (.bin .add (some ⟨64, false⟩) (.var 4)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) 1) (.ptr ob (0 + (dst + 1) * 1)) :=
    EvE.index (EvE.var (show s2.locals 1 = some (.ptr ob 0) from rfl))
      (EvE_u64_add_const (i := 4) (k := 1) (show s2.locals 4 = some (.int ⟨64, false⟩ dst) from rfl) (by omega) (by omega))
      (ptrAddN_ok hMem2 (by rw [hlen_blk0]; omega))
  have hMul_2 : EvE Gen.prog s2 (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))) (.int ⟨64, false⟩ (byteAt d (src_base + x) * 4)) :=
    EvE.bin (EvE.var (show s2.locals 7 = some (.int ⟨64, false⟩ (byteAt d (src_base + x))) from rfl)) (EvE.cast (EvE.const _) hcast4) (bin_u64_mul _ _ (by omega))
  have hP0_2 : EvE Gen.prog s2 (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.int ⟨64, false⟩ (palette_offset + byteAt d (src_base + x) * 4)) :=
    EvE.bin (EvE.var (show s2.locals 5 = some (.int ⟨64, false⟩ palette_offset) from rfl)) hMul_2 (bin_u64_add palette_offset _ (by omega))
  have hAddrP1_2 : EvE Gen.prog s2 (.bin .add (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) (.int ⟨64, false⟩ (palette_offset + byteAt d (src_base + x) * 4 + 1)) :=
    EvE.bin hP0_2 (EvE.cast (EvE.const _) hcast1) (bin_u64_add _ 1 (by omega))
  have hByteP1s2 : EvE Gen.prog s2 (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) 1))
      (.int ⟨8, false⟩ (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1))) :=
    EvE.load (EvE.index (EvE.var (show s2.locals 0 = some (.ptr bd 0) from rfl)) hAddrP1_2 (ptrAddN_ok hMem2bd (by omega)))
      (load_byte_at s2.mem bd d hMem2bd _ (by omega))
  have hStore1 : ExS Gen.prog s2
      (.store (.int ⟨8, false⟩) (.index (.var 1)
        (.bin .add (some ⟨64, false⟩) (.var 4)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) 1)
        (.load (.int ⟨8, false⟩) (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 1)))) 1)))
      .normal { s2 with mem := s2.mem.upd ob ((obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).drop (dst + 2)) } :=
    ExS.store hAddrO1 hByteP1s2 (by rw [show s2.ro = s0.ro from rfl]; exact hSro)
      (store_byte_at s2.mem ob (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)) hMem2 (dst + 1) (by rw [hlen_blk0]; omega) (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) (byteAt_lt d _))
  let s3 : State := { s2 with mem := s2.mem.upd ob ((obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).drop (dst + 2)) }
  have hMem3bd : s3.mem bd = some d := by
    show ((s2.mem.upd ob ((obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).drop (dst + 2))) bd) = some d
    exact mem_upd_neq s2.mem ob bd ((obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).drop (dst + 2)) d hMem2bd hd0
  have hblk1 := splice_enc_3 obl (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) dst (by omega)
  have hMem3 : s3.mem ob = some ((obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).drop (dst + 2)) := by
    show ((s2.mem.upd ob ((obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).drop (dst + 2))) ob) = some ((obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).drop (dst + 2))
    exact mem_upd_eq s2.mem ob ((obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).drop (dst + 2))
  have hMem3flat : s3.mem ob = some (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ obl.drop (dst + 2)) := by
    rw [hblk1] at hMem3; exact hMem3
  have hlen_blk1 : (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ obl.drop (dst + 2)).length = obl.length := by
    simp only [List.length_append, List.length_drop, List.length_take_of_le (by omega : dst ≤ obl.length), NANO.C.encodeLE_length]
    omega
  -- ==== store 2: out[dst + 2] = bytes[p0] ====
  have hMul_3 : EvE Gen.prog s3 (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4)))) (.int ⟨64, false⟩ (byteAt d (src_base + x) * 4)) :=
    EvE.bin (EvE.var (show s3.locals 7 = some (.int ⟨64, false⟩ (byteAt d (src_base + x))) from rfl)) (EvE.cast (EvE.const _) hcast4) (bin_u64_mul _ _ (by omega))
  have hP0_3 : EvE Gen.prog s3 (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.int ⟨64, false⟩ (palette_offset + byteAt d (src_base + x) * 4)) :=
    EvE.bin (EvE.var (show s3.locals 5 = some (.int ⟨64, false⟩ palette_offset) from rfl)) hMul_3 (bin_u64_add palette_offset _ (by omega))
  have hAddrP0_3 : EvE Gen.prog s3 (.bin .add (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) (.int ⟨64, false⟩ (palette_offset + byteAt d (src_base + x) * 4 + 0)) :=
    EvE.bin hP0_3 (EvE.cast (EvE.const _) hcast0) (bin_u64_add _ 0 (by omega))
  have hByteP0s3 : EvE Gen.prog s3 (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) 1))
      (.int ⟨8, false⟩ (byteAt d (palette_offset + byteAt d (src_base + x) * 4))) :=
    EvE.load (EvE.index (EvE.var (show s3.locals 0 = some (.ptr bd 0) from rfl)) hAddrP0_3 (ptrAddN_ok hMem3bd (by omega)))
      (load_byte_at s3.mem bd d hMem3bd _ (by omega))
  have hAddrO2 : EvE Gen.prog s3 (.index (.var 1)
      (.bin .add (some ⟨64, false⟩) (.var 4)
        (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 2)))) 1) (.ptr ob (0 + (dst + 2) * 1)) :=
    EvE.index (EvE.var (show s3.locals 1 = some (.ptr ob 0) from rfl))
      (EvE_u64_add_const (i := 4) (k := 2) (show s3.locals 4 = some (.int ⟨64, false⟩ dst) from rfl) (by omega) (by omega))
      (ptrAddN_ok hMem3flat (by rw [hlen_blk1]; omega))
  have hL2 : (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1))).length = dst + 2 := by
    rw [List.length_append, List.length_append, List.length_take_of_le (by omega)]
    rw [NANO.C.encodeLE_length, NANO.C.encodeLE_length]
  have htake2 : List.take (dst + 2) (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ obl.drop (dst + 2)) = obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) := by
    rw [show dst + 2 = (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1))).length from hL2.symm]
    exact List.take_append_length
  have hdrop2 : List.drop (dst + 2 + 1) (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ obl.drop (dst + 2)) = obl.drop (dst + 3) := by
    rw [show dst + 2 + 1 = (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1))).length + 1 from by rw [hL2]]
    rw [drop_append_length (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1))) (obl.drop (dst + 2)) 1]
    rw [List.drop_drop]
    rw [hL2]
  have hMem2_final : store s3.mem (.int ⟨8, false⟩) (.ptr ob (0 + (dst + 2) * 1)) (.int ⟨8, false⟩ (byteAt d (palette_offset + byteAt d (src_base + x) * 4))) = .ok (s3.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4)) ++ obl.drop (dst + 3))) := by
    rw [store_byte_at s3.mem ob (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ obl.drop (dst + 2)) hMem3flat (dst + 2) (by rw [hlen_blk1]; omega) (byteAt d (palette_offset + byteAt d (src_base + x) * 4)) (byteAt_lt d _)]
    rw [htake2, hdrop2]
  have hStore2 : ExS Gen.prog s3
      (.store (.int ⟨8, false⟩) (.index (.var 1)
        (.bin .add (some ⟨64, false⟩) (.var 4)
          (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 2)))) 1)
        (.load (.int ⟨8, false⟩) (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.bin .add (some ⟨64, false⟩) (.var 5) (.bin .mul (some ⟨64, false⟩) (.var 7) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 4))))) (.cast ⟨64, false⟩ (.const (.int ⟨32, false⟩ 0)))) 1)))
      .normal { s3 with mem := s3.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4)) ++ obl.drop (dst + 3)) } :=
    ExS.store hAddrO2 hByteP0s3 (by rw [show s3.ro = s0.ro from rfl]; exact hSro) hMem2_final
  let s4 : State := { s3 with mem := s3.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4)) ++ obl.drop (dst + 3)) }
  refine ⟨s4, ?_, ?_, ?_, ?_⟩
  · show ExS Gen.prog s0 Gen.ni_bmp_decode_indexed_pixel.body (.ret (some (.int ⟨32, true⟩ 0))) s4
    exact ExS.seq hSet (ExS.seq hIfSkip (ExS.seq hStore0 (ExS.seq hStore1 (ExS.seq hStore2 (ExS.ret (EvE.const _))))))
  · show ((s3.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4)) ++ obl.drop (dst + 3))) ob) = some _
    rw [mem_upd_eq]
  · show ((s3.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4)) ++ obl.drop (dst + 3))) bd) = some d
    rw [mem_upd_other s3.mem ob bd _ hd0]
    exact hMem3bd
  · show ((s3.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4)) ++ obl.drop (dst + 3))) 2) = m 2
    rw [mem_upd_other s3.mem ob 2 _ h2ob]
    show ((s2.mem.upd ob ((obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).take (dst + 1) ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 1)) ++ (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1)).drop (dst + 2))) 2) = m 2
    rw [mem_upd_other s2.mem ob 2 _ h2ob]
    show ((s1.mem.upd ob (obl.take dst ++ encodeLE 1 (byteAt d (palette_offset + byteAt d (src_base + x) * 4 + 2)) ++ obl.drop (dst + 1))) 2) = m 2
    rw [mem_upd_other s1.mem ob 2 _ h2ob]

/-- `ni_bmp_decode_indexed_pixel` with an out-of-range index returns 11 and
    leaves memory unchanged. Locals: 0=bytes, 1=out, 2=src_base, 3=x, 4=dst,
    5=palette_offset, 6=palette_entries, 7=idx -/
theorem ni_bmp_decode_indexed_pixel_err_exs (m : Mem) (d obl : List UInt8)
    (bd ob : Nat) (hm : m bd = some d) (hd : d.length < 2 ^ 64)
    (hob : m ob = some obl) (src_base x dst palette_offset palette_entries : Nat)
    (hd0 : bd ≠ ob) (h2ob : 2 ≠ ob)
    (hs : src_base + x < d.length)
    (hge : palette_entries ≤ byteAt d (src_base + x))
    (ro : Bool) (hro : ro = false) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals [0, 1, 2, 3, 4, 5, 6] ([.ptr bd 0, .ptr ob 0, .int ⟨64, false⟩ src_base, .int ⟨64, false⟩ x, .int ⟨64, false⟩ dst, .int ⟨64, false⟩ palette_offset, .int ⟨64, false⟩ palette_entries] : List Val), m, ro⟩
      Gen.ni_bmp_decode_indexed_pixel.body
      (.ret (some (.int ⟨32, true⟩ 11))) s' ∧
    s'.mem ob = some obl ∧ s'.mem bd = some d ∧ s'.mem 2 = m 2 := by
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  let s0 : State := { locals := frameLocals [0, 1, 2, 3, 4, 5, 6] ([.ptr bd 0, .ptr ob 0, .int ⟨64, false⟩ src_base, .int ⟨64, false⟩ x, .int ⟨64, false⟩ dst, .int ⟨64, false⟩ palette_offset, .int ⟨64, false⟩ palette_entries] : List Val), mem := m, ro := ro }
  have hl0 : s0.locals 0 = some (.ptr bd 0) := rfl
  have hl2 : s0.locals 2 = some (.int ⟨64, false⟩ src_base) := rfl
  have hl3 : s0.locals 3 = some (.int ⟨64, false⟩ x) := rfl
  have hSrcX : EvE Gen.prog s0 (.bin .add (some ⟨64, false⟩) (.var 2) (.var 3)) (.int ⟨64, false⟩ (src_base + x)) :=
    EvE.bin (EvE.var hl2) (EvE.var hl3) (bin_u64_add src_base x (by omega))
  have hIdx : EvE Gen.prog s0 (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2) (.var 3)) 1))
      (.int ⟨8, false⟩ (byteAt d (src_base + x))) :=
    EvE.load (EvE.index (EvE.var hl0) hSrcX (ptrAddN_ok hm (by omega)))
      (load_byte_at m bd d hm (src_base + x) (by omega))
  have hCastIdx : evalCast ⟨64, false⟩ (.int ⟨8, false⟩ (byteAt d (src_base + x))) = .ok (.int ⟨64, false⟩ (byteAt d (src_base + x))) := by
    have hblt : byteAt d (src_base + x) < 256 := byteAt_lt d (src_base + x)
    simp [evalCast, IntTy.modulus, IntTy.wrap, Int.ofNat_lt, show byteAt d (src_base + x) < 18446744073709551616 from by omega]
  have hIdx64 : EvE Gen.prog s0 (.cast ⟨64, false⟩ (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2) (.var 3)) 1)))
      (.int ⟨64, false⟩ (byteAt d (src_base + x))) :=
    EvE.cast hIdx hCastIdx
  have hSet : ExS Gen.prog s0 (.set 7 (.cast ⟨64, false⟩ (.load (.int ⟨8, false⟩)
      (.index (.var 0) (.bin .add (some ⟨64, false⟩) (.var 2) (.var 3)) 1))))
      .normal { s0 with locals := s0.locals.upd 7 (.int ⟨64, false⟩ (byteAt d (src_base + x))) } :=
    ExS.set hIdx64
  let s1 : State := { s0 with locals := s0.locals.upd 7 (.int ⟨64, false⟩ (byteAt d (src_base + x))) }
  have hl6_1 : s1.locals 6 = some (.int ⟨64, false⟩ palette_entries) := rfl
  have hl7_1 : s1.locals 7 = some (.int ⟨64, false⟩ (byteAt d (src_base + x))) := rfl
  -- ==== idx ≥ palette_entries, so the error branch is taken ====
  have hge_true : EvE Gen.prog s1 (.bin .ge (some ⟨64, false⟩) (.var 7) (.var 6)) (boolVal true) := by
    have h := bin_u64_ge (byteAt d (src_base + x)) palette_entries
    rw [show decide (byteAt d (src_base + x) ≥ palette_entries) = true from decide_eq_true (by omega)] at h
    exact EvE.bin (EvE.var hl7_1) (EvE.var hl6_1) h
  have hIf11 : ExS Gen.prog s1
      (.ite (.bin .ge (some ⟨64, false⟩) (.var 7) (.var 6)) (.ret (some (.const (.int ⟨32, true⟩ 11)))) .skip)
      (.ret (some (.int ⟨32, true⟩ 11))) s1 :=
    ExS.ite hge_true truthy_true (ExS.ret (EvE.const _))
  refine ⟨s1, ?_, ?_, ?_, ?_⟩
  · show ExS Gen.prog s0 Gen.ni_bmp_decode_indexed_pixel.body (.ret (some (.int ⟨32, true⟩ 11))) s1
    exact ExS.seq hSet (ExS.seq_ret hIf11)
  · show (s1.mem ob) = some obl
    exact hob
  · show (s1.mem bd) = some d
    exact hm
  · show (s1.mem 2) = m 2
    rfl

end NANO.C.Proofs
