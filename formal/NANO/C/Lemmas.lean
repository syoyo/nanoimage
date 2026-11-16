/-
  Lemmas for symbolic execution of MiniC programs.
-/
import NANO.C.Semantics
import NANO.Basic
namespace NANO.C

set_option maxRecDepth 8000000


theorem decodeLE_take_one_drop (d : List UInt8) (o : Nat) (h : o < d.length) :
    decodeLE (List.take 1 (List.drop o d)) = NANO.byteAt d o := by
  unfold NANO.byteAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  have : List.drop o d = d[o] :: List.drop (o + 1) d := by
    rw [List.drop_eq_getElem_cons h]
  rw [this, List.take_succ_cons, List.take_zero]
  simp only [decodeLE]; omega

theorem byteAt_lt (d : List UInt8) (o : Nat) : NANO.byteAt d o < 256 := by
  unfold NANO.byteAt; exact UInt8.toNat_lt _

/-- `a ||| b * 2^k = a + b * 2^k` when `a < 2^k`. -/
theorem or_mul_two_pow {a b k : Nat} (h : a < 2 ^ k) : a ||| b * 2 ^ k = a + b * 2 ^ k := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt h]; omega

theorem rd32_lt (d : List UInt8) (o : Nat) : NANO.rd32le d o < 2 ^ 32 := by
  unfold NANO.rd32le
  have := byteAt_lt d o; have := byteAt_lt d (o + 1)
  have := byteAt_lt d (o + 2); have := byteAt_lt d (o + 3)
  omega

theorem rd64_lt (d : List UInt8) (o : Nat) : NANO.rd64le d o < 2 ^ 64 := by
  unfold NANO.rd64le
  have := rd32_lt d o; have := rd32_lt d (o + 4)
  omega

/-- The value computed by `tg3__rd_u32le`'s expression tree. -/
theorem rd32_or (d : List UInt8) (o : Nat) :
    NANO.byteAt d o ||| NANO.byteAt d (o + 1) * 256 % 4294967296 |||
      NANO.byteAt d (o + 2) * 65536 % 4294967296 |||
      NANO.byteAt d (o + 3) * 16777216 % 4294967296 = NANO.rd32le d o := by
  have b0 := byteAt_lt d o; have b1 := byteAt_lt d (o + 1)
  have b2 := byteAt_lt d (o + 2); have b3 := byteAt_lt d (o + 3)
  rw [Nat.mod_eq_of_lt (by omega : NANO.byteAt d (o + 1) * 256 < 4294967296),
      Nat.mod_eq_of_lt (by omega : NANO.byteAt d (o + 2) * 65536 < 4294967296),
      Nat.mod_eq_of_lt (by omega : NANO.byteAt d (o + 3) * 16777216 < 4294967296)]
  rw [show (256 : Nat) = 2 ^ 8 by rfl, or_mul_two_pow (by omega)]
  rw [show (65536 : Nat) = 2 ^ 16 by rfl, or_mul_two_pow (by omega)]
  rw [show (16777216 : Nat) = 2 ^ 24 by rfl, or_mul_two_pow (by omega)]
  unfold NANO.rd32le; omega

theorem rd64_or (d : List UInt8) (o : Nat) :
    NANO.rd32le d o ||| NANO.rd32le d (o + 4) * 4294967296 % 18446744073709551616 = NANO.rd64le d o := by
  have := rd32_lt d o; have := rd32_lt d (o + 4)
  rw [Nat.mod_eq_of_lt (by omega : NANO.rd32le d (o + 4) * 4294967296 < 18446744073709551616)]
  rw [show (4294967296 : Nat) = 2 ^ 32 by rfl, or_mul_two_pow (by omega)]
  unfold NANO.rd64le; omega



@[simp] theorem byteAt_mod32 (d : List UInt8) (o : Nat) :
    NANO.byteAt d o % 4294967296 = NANO.byteAt d o :=
  Nat.mod_eq_of_lt (by have := byteAt_lt d o; omega)

@[simp] theorem encodeLE_length (k n : Nat) : (encodeLE k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [encodeLE, ih]

theorem decodeLE_encodeLE (k n : Nat) : decodeLE (encodeLE k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [encodeLE, decodeLE, Nat.mod_one]
  | succ k ih =>
    simp only [encodeLE, decodeLE, ih]
    have h1 : ((n % 256).toUInt8).toNat = n % 256 := by
      simp [Nat.toUInt8, UInt8.toNat_ofNat]
    rw [h1, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]


@[simp] theorem rd32_mod64 (d : List UInt8) (o : Nat) :
    NANO.rd32le d o % 18446744073709551616 = NANO.rd32le d o :=
  Nat.mod_eq_of_lt (by have := rd32_lt d o; omega)
@[simp] theorem rd32_mod32 (d : List UInt8) (o : Nat) :
    NANO.rd32le d o % 4294967296 = NANO.rd32le d o :=
  Nat.mod_eq_of_lt (by have := rd32_lt d o; omega)
@[simp] theorem rd64_mod64 (d : List UInt8) (o : Nat) :
    NANO.rd64le d o % 18446744073709551616 = NANO.rd64le d o :=
  Nat.mod_eq_of_lt (by have := rd64_lt d o; omega)

@[simp] theorem Mem.upd_same (m : Mem) (b : Nat) (x : Block) : (m.upd b x) b = some x := by
  simp [Mem.upd]
@[simp] theorem Mem.upd_ne (m : Mem) {b b' : Nat} (x : Block) (h : b' ≠ b) : (m.upd b x) b' = m b' := by
  simp [Mem.upd, h]
@[simp] theorem Mem.upd_upd (m : Mem) (b : Nat) (x y : Block) : (m.upd b x).upd b y = m.upd b y := by
  funext b'; simp only [Mem.upd]; split <;> rfl
@[simp] theorem Locals.upd_same (l : Locals) (i : Nat) (v : Val) : (l.upd i v) i = some v := by
  simp [Locals.upd]
@[simp] theorem Locals.upd_ne (l : Locals) {i j : Nat} (v : Val) (h : j ≠ i) : (l.upd i v) j = l j := by
  simp [Locals.upd, h]
@[simp] theorem Locals.upd_upd (l : Locals) (i : Nat) (v w : Val) : (l.upd i v).upd i w = l.upd i w := by
  funext j; simp only [Locals.upd]; split <;> rfl
@[simp] theorem frameLocals_apply (ps : List Nat) (vs : List Val) (i : Nat) :
    frameLocals ps vs i = (match ps.idxOf? i with | some k => vs[k]? | none => none) := rfl
@[simp] theorem wrap_zero (t : IntTy) : t.wrap 0 = 0 := by simp [IntTy.wrap]
@[simp] theorem wrap_ofNat (t : IntTy) (n : Nat) : t.wrap (n : Int) = n % t.modulus := by
  simp only [IntTy.wrap]; omega

@[simp] theorem and_three (x : Nat) : x &&& 3 = x % 4 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 2
  simpa using this

@[simp] theorem mod4_le4 (x : Nat) : x % 4 ≤ 4 := Nat.le_of_lt (Nat.mod_lt _ (by decide))

theorem decodeLE_take_one (d : List UInt8) (h : 0 < d.length) :
    decodeLE (List.take 1 d) = NANO.byteAt d 0 := by
  have := decodeLE_take_one_drop d 0 h
  simpa using this

theorem decodeLE_take_one_tail (d : List UInt8) (h : 1 < d.length) :
    decodeLE (List.take 1 d.tail) = NANO.byteAt d 1 := by
  have := decodeLE_take_one_drop d 1 h
  simpa using this


/-! ## Big/little-endian byte-reader expression lemmas (nanoimage core) -/


/-- The value computed by `ni_read_u16le`'s expression tree. -/
theorem rd16le_or (d : List UInt8) (o : Nat) :
    NANO.byteAt d o ||| NANO.byteAt d (o + 1) * 256 % 4294967296 = NANO.rd16le d o := by
  have b0 := byteAt_lt d o; have b1 := byteAt_lt d (o + 1)
  rw [Nat.mod_eq_of_lt (by omega : NANO.byteAt d (o + 1) * 256 < 4294967296),
      show (256 : Nat) = 2 ^ 8 by rfl, or_mul_two_pow (by omega : NANO.byteAt d o < 2 ^ 8)]
  unfold NANO.rd16le; omega

/-- The value computed by `ni_read_u16be`'s expression tree. -/
theorem rd16be_or (d : List UInt8) (o : Nat) :
    NANO.byteAt d o * 256 ||| NANO.byteAt d (o + 1) = NANO.rd16be d o := by
  have b0 := byteAt_lt d o; have b1 := byteAt_lt d (o + 1)
  rw [Nat.or_comm, or_mul_two_pow (by omega : NANO.byteAt d (o + 1) < 2 ^ 8)]
  unfold NANO.rd16be; omega

private theorem mul_two_pow_add (x : Nat) (m n : Nat) : x * 2 ^ m * 2 ^ n = x * 2 ^ (m + n) := by
  rw [Nat.mul_assoc, ← Nat.pow_add]

/-- The value computed by `ni_read_u32be`'s expression tree. -/
theorem rd32be_or (d : List UInt8) (o : Nat) :
    NANO.byteAt d o * 16777216 % 4294967296 ||| NANO.byteAt d (o + 1) * 65536 % 4294967296 |||
      NANO.byteAt d (o + 2) * 256 % 4294967296 ||| NANO.byteAt d (o + 3) = NANO.rd32be d o := by
  have b0 := byteAt_lt d o; have b1 := byteAt_lt d (o + 1)
  have b2 := byteAt_lt d (o + 2); have b3 := byteAt_lt d (o + 3)
  rw [Nat.mod_eq_of_lt (by omega : NANO.byteAt d o * 16777216 < 4294967296),
      Nat.mod_eq_of_lt (by omega : NANO.byteAt d (o + 1) * 65536 < 4294967296),
      Nat.mod_eq_of_lt (by omega : NANO.byteAt d (o + 2) * 256 < 4294967296),
      show (16777216 : Nat) = 2 ^ 24 by rfl, show (65536 : Nat) = 2 ^ 16 by rfl,
      show (256 : Nat) = 2 ^ 8 by rfl]
  unfold NANO.rd32be
  have e1 : NANO.byteAt d o * 2 ^ 24 ||| NANO.byteAt d (o + 1) * 2 ^ 16 =
      NANO.byteAt d o * 2 ^ 24 + NANO.byteAt d (o + 1) * 2 ^ 16 := by
    rw [Nat.or_comm, or_mul_two_pow (show NANO.byteAt d (o + 1) * 2 ^ 16 < 2 ^ 24 by omega)]
    ac_rfl
  have e2 : (NANO.byteAt d o * 2 ^ 24 + NANO.byteAt d (o + 1) * 2 ^ 16) ||| NANO.byteAt d (o + 2) * 2 ^ 8 =
      NANO.byteAt d o * 2 ^ 24 + NANO.byteAt d (o + 1) * 2 ^ 16 + NANO.byteAt d (o + 2) * 2 ^ 8 := by
    have hX : (NANO.byteAt d o * 2 ^ 8 + NANO.byteAt d (o + 1)) * 2 ^ 16 =
        NANO.byteAt d o * 2 ^ 24 + NANO.byteAt d (o + 1) * 2 ^ 16 := by
      rw [Nat.add_mul, mul_two_pow_add]
    rw [← hX, Nat.or_comm, or_mul_two_pow (show NANO.byteAt d (o + 2) * 2 ^ 8 < 2 ^ 16 by omega), hX]
    ac_rfl
  have e3 : (NANO.byteAt d o * 2 ^ 24 + NANO.byteAt d (o + 1) * 2 ^ 16 + NANO.byteAt d (o + 2) * 2 ^ 8) |||
        NANO.byteAt d (o + 3) =
      NANO.byteAt d o * 2 ^ 24 + NANO.byteAt d (o + 1) * 2 ^ 16 + NANO.byteAt d (o + 2) * 2 ^ 8 +
        NANO.byteAt d (o + 3) := by
    have hY : (NANO.byteAt d o * 2 ^ 16 + NANO.byteAt d (o + 1) * 2 ^ 8 + NANO.byteAt d (o + 2)) * 2 ^ 8 =
        NANO.byteAt d o * 2 ^ 24 + NANO.byteAt d (o + 1) * 2 ^ 16 + NANO.byteAt d (o + 2) * 2 ^ 8 := by
      rw [Nat.add_mul, Nat.add_mul, mul_two_pow_add, mul_two_pow_add]
    rw [← hY, Nat.or_comm,
        or_mul_two_pow (show NANO.byteAt d (o + 3) < 2 ^ 8 by omega), hY]
    ac_rfl
  rw [e1, e2, e3]




@[simp] theorem rd16le_lt (d : List UInt8) (o : Nat) : NANO.rd16le d o < 65536 := by
  have b0 := byteAt_lt d o; have b1 := byteAt_lt d (o + 1)
  unfold NANO.rd16le; omega

@[simp] theorem rd16be_lt (d : List UInt8) (o : Nat) : NANO.rd16be d o < 65536 := by
  have b0 := byteAt_lt d o; have b1 := byteAt_lt d (o + 1)
  unfold NANO.rd16be; omega

@[simp] theorem rd32be_lt (d : List UInt8) (o : Nat) : NANO.rd32be d o < 4294967296 := by
  have b0 := byteAt_lt d o; have b1 := byteAt_lt d (o + 1)
  have b2 := byteAt_lt d (o + 2); have b3 := byteAt_lt d (o + 3)
  unfold NANO.rd32be; omega




/-- `IntTy.inRange` for small non-negative ints (covers the promoted-u8 path). -/
theorem inRange_i32_small {z : Int} (h1 : 0 ≤ z) (h2 : z < 2147483648) :
    IntTy.inRange IntTy.i32 z = true := by
  rw [show IntTy.inRange IntTy.i32 z = (decide (-2147483648 ≤ z) && decide (z ≤ 2147483647)) from rfl]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem arith_i32_small {z : Int} (h1 : 0 ≤ z) (h2 : z < 2147483648) :
    arith IntTy.i32 z = .ok (.int IntTy.i32 (IntTy.wrap IntTy.i32 z)) := by
  simp [arith, inRange_i32_small h1 h2]

@[simp] theorem wrap_i32_small {z : Int} (h1 : 0 ≤ z) (h2 : z < 2147483648) :
    IntTy.wrap IntTy.i32 z = z.toNat := by
  show (z % 4294967296).toNat = z.toNat
  omega

@[simp] theorem wrap_i32_ofNat {n : Nat} (h : n < 2147483648) :
    IntTy.wrap IntTy.i32 (n : Int) = n := by
  show ((n : Int) % 4294967296).toNat = n
  have h3 : (n : Int) % 4294967296 = (n : Int) := by omega
  rw [h3]
  omega




@[simp] theorem wrap_u16_ofNat2 {n : Nat} (h : n < 65536) :
    (⟨16, false⟩ : IntTy).wrap (n : Int) = n := by
  show ((n : Int) % 65536).toNat = n
  have e : (n : Int) % (65536 : Int) = (n : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  rw [e]
  omega

theorem wrap_i32_byte_mul {b : Nat} (h : b < 256) :
    (⟨32, true⟩ : IntTy).wrap ((↑b : Int) * 256) = b * 256 := by
  have h0 : (0 : Int) ≤ (↑b : Int) * 256 := by omega
  have h1 : (↑b : Int) * 256 < 4294967296 := by omega
  have e : (↑b : Int) * 256 % ((⟨32, true⟩ : IntTy).modulus : Int) = ↑b * 256 := by
    exact Int.emod_eq_of_lt h0 h1
  rw [IntTy.wrap, e]
  omega




theorem rd16le_or' (d : List UInt8) (o : Nat) :
    NANO.byteAt d o ||| NANO.byteAt d (o + 1) * 2 ^ 8 = NANO.rd16le d o := by
  have b0 := byteAt_lt d o
  rw [or_mul_two_pow (show NANO.byteAt d o < 2 ^ 8 by omega)]
  rfl




theorem rd16le_or'' (d : List UInt8) (o : Nat) :
    NANO.byteAt d o ||| NANO.byteAt d (o + 1) * 256 = NANO.rd16le d o := by
  have b0 := byteAt_lt d o
  rw [or_mul_two_pow (show NANO.byteAt d o < 2 ^ 8 by omega)]
  rfl




/-- i32 comparisons on `Val.int` operands (signed interpretation). -/
theorem bin_i32_lt (n k : Nat) : evalBin .lt (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ k)
    = .ok (boolVal (decide (IntTy.toInt ⟨32, true⟩ n < IntTy.toInt ⟨32, true⟩ k))) := rfl

theorem bin_i32_gt (n k : Nat) : evalBin .gt (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ k)
    = .ok (boolVal (decide (IntTy.toInt ⟨32, true⟩ n > IntTy.toInt ⟨32, true⟩ k))) := rfl

theorem bin_i32_le (n k : Nat) : evalBin .le (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ k)
    = .ok (boolVal (decide (IntTy.toInt ⟨32, true⟩ n ≤ IntTy.toInt ⟨32, true⟩ k))) := rfl

theorem toInt_i32_zero : IntTy.toInt ⟨32, true⟩ 0 = 0 := rfl

theorem toInt_i32_bounds (n : Nat) (hn : n < 4294967296) :
    -2147483648 ≤ IntTy.toInt ⟨32, true⟩ n ∧ IntTy.toInt ⟨32, true⟩ n ≤ 2147483647 := by
  have hm : (⟨32, true⟩ : IntTy).modulus = 4294967296 := rfl
  have hw : (⟨32, true⟩ : IntTy).width = 32 := rfl
  unfold IntTy.toInt
  simp only [hm, hw, IntTy.signed]
  have h31 : (2 : Nat) ^ (32 - 1) = 2147483648 := rfl
  split <;> simp only [true_and, h31] at * <;> omega

theorem wrap_u8_range {z : Int} (h0 : 0 ≤ z) (h1 : z ≤ 255) :
    IntTy.wrap ⟨8, false⟩ z = z.toNat := by
  have hm : (⟨8, false⟩ : IntTy).modulus = 256 := rfl
  show (z % ((⟨8, false⟩ : IntTy).modulus : Int)).toNat = z.toNat
  rw [hm, Int.emod_eq_of_lt h0 (by omega)]


theorem and_seven (x : Nat) : x &&& 7 = x % 8 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 3
  simpa using this

theorem pow2_le256 {bd : Nat} (h : bd ≤ 8) : 2 ^ bd ≤ 256 := by
  have := Nat.pow_le_pow_right (show 2 > 0 by decide) h
  have h8 : (2 : Nat) ^ 8 = 256 := rfl
  omega

theorem toInt_i32_small {n : Nat} (h : n < 2147483648) : IntTy.toInt ⟨32, true⟩ n = n := by
  unfold IntTy.toInt
  have hw : (⟨32, true⟩ : IntTy).width = 32 := rfl
  have hs : (⟨32, true⟩ : IntTy).signed = true := rfl
  rw [hw, hs]
  have h31 : (2 : Nat) ^ (32 - 1) = 2147483648 := rfl
  rw [if_neg (by rw [h31]; omega)]

theorem int_div_two_pow (x k : Nat) : (x : Int) / (2 : Int) ^ k = ((x / 2 ^ k : Nat) : Int) := by
  have h : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by push_cast; rfl
  rw [← h]
  exact Int.ofNat_ediv_ofNat

theorem int_mod_two_pow (x k : Nat) : (x : Int) % (2 : Int) ^ k = ((x % 2 ^ k : Nat) : Int) := by
  have h : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by push_cast; rfl
  rw [← h]
  exact Int.ofNat_mod_ofNat x (2 ^ k)

theorem div_pow_lt_231 {x k : Nat} (hx : x < 256) : x / 2 ^ k < 2147483648 := by
  have := Nat.div_le_self x (2 ^ k)
  omega

theorem mod_pow_lt_256 {y bd : Nat} (hp : 2 ^ bd ≤ 256) : y % 2 ^ bd < 256 := by
  have hpos : 0 < 2 ^ bd := Nat.two_pow_pos bd
  have := Nat.mod_lt y hpos
  omega

theorem wrap_u32_small {n : Nat} (h : n < 2147483648) :
    IntTy.wrap ⟨32, false⟩ (n : Int) = n := by
  have hm : (⟨32, false⟩ : IntTy).modulus = 4294967296 := rfl
  show ((n : Int) % ((⟨32, false⟩ : IntTy).modulus : Int)).toNat = n
  rw [hm, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem bin_shr_i32 {x k : Nat} (hx : x < 2147483648) (hk : k < 32) :
    evalBin .shr (some ⟨32, true⟩) (.int ⟨32, true⟩ x) (.int ⟨32, true⟩ k)
      = .ok (.int ⟨32, true⟩ (x / 2 ^ k)) := by
  have hk' : IntTy.toInt ⟨32, true⟩ k = (k : Int) := toInt_i32_small (by omega)
  have hx' : IntTy.toInt ⟨32, true⟩ x = (x : Int) := toInt_i32_small hx
  have hk2 : (IntTy.toInt ⟨32, true⟩ k).toNat = k := by rw [hk']; omega
  have hw : (x : Int) / (2 : Int) ^ k = ((x / 2 ^ k : Nat) : Int) := int_div_two_pow x k
  have hwrap : IntTy.wrap ⟨32, true⟩ ((x / 2 ^ k : Nat) : Int) = x / 2 ^ k :=
    wrap_i32_ofNat (Nat.lt_of_le_of_lt (Nat.div_le_self x _) hx)
  simp only [evalBin, evalBinInt, binInt, intOf, isPtr, C.guard, hk', hx', hk2, ↓reduceIte,
    Bool.and_self, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true, reduceCtorEq, Res.bind_ok, Res.bind_eq,
    pure, Res.ok, Res.bind]
  rw [if_pos (by omega)]
  show Res.ok (Val.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ ((x : Int) / (2 : Int) ^ (k : Int).toNat)))
    = Res.ok (Val.int ⟨32, true⟩ (x / 2 ^ k))
  rw [Int.toNat_natCast, hw, hwrap]


theorem inRange_i32_rng {z : Int} (h1 : -2147483648 ≤ z) (h2 : z ≤ 2147483647) :
    IntTy.inRange ⟨32, true⟩ z = true := by
  rw [show IntTy.inRange ⟨32, true⟩ z = (decide (-2147483648 ≤ z) && decide (z ≤ 2147483647)) from rfl]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem arith_i32_rng {z : Int} (h1 : -2147483648 ≤ z) (h2 : z ≤ 2147483647) :
    arith ⟨32, true⟩ z = .ok (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ z)) := by
  unfold arith
  rw [if_pos rfl, if_pos (inRange_i32_rng h1 h2)]

theorem toInt_wrap_i32 {z : Int} (h1 : -2147483648 ≤ z) (h2 : z ≤ 2147483647) :
    IntTy.toInt ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ z) = z := by
  have hm : (⟨32, true⟩ : IntTy).modulus = 4294967296 := rfl
  have hw : (⟨32, true⟩ : IntTy).width = 32 := rfl
  have h31 : (2 : Nat) ^ (32 - 1) = 2147483648 := rfl
  unfold IntTy.toInt IntTy.wrap
  rw [hm, hw, show (⟨32, true⟩ : IntTy).signed = true from rfl]
  simp only [true_and]
  split
  · rename_i hc
    have h31' : ((2 : Nat) ^ (32 - 1) : Nat) = 2147483648 := h31
    rw [h31'] at hc
    omega
  · omega

theorem bin_i32_add (n k : Nat) : evalBin .add (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ k)
    = arith ⟨32, true⟩ (IntTy.toInt ⟨32, true⟩ n + IntTy.toInt ⟨32, true⟩ k) := rfl

theorem bin_i32_sub (n k : Nat) : evalBin .sub (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ k)
    = arith ⟨32, true⟩ (IntTy.toInt ⟨32, true⟩ n - IntTy.toInt ⟨32, true⟩ k) := rfl



theorem Int.natCast_add_of (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + b := Int.natCast_add a b
theorem Int.natCast_mul_of (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * b := Int.natCast_mul a b
theorem wrap_u16_bytes (a b : Nat) (ha : a < 256) (hb : b < 256) :
    (⟨16, false⟩ : IntTy).wrap ((a : Int) * 256 + (b : Int)) = a * 256 + b := by
  have h := wrap_u16_ofNat2 (show a * 256 + b < 65536 by omega)
  have h2 : ((a * 256 + b : Nat) : Int) = (a : Int) * 256 + (b : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul]
    rfl
  rw [← h2, wrap_u16_ofNat2 (show a * 256 + b < 65536 by omega)]

theorem bin_i32_ge (n k : Nat) : evalBin .ge (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ k)
    = .ok (boolVal (decide (IntTy.toInt ⟨32, true⟩ n ≥ IntTy.toInt ⟨32, true⟩ k))) := rfl
theorem bin_u64_ge (n k : Nat) : evalBin .ge (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ k)
    = .ok (boolVal (decide (n ≥ k))) := rfl
theorem bin_i32_ge_bytes (n k : Nat) (hn : n < 256) (hk : k < 256) :
    evalBin .ge (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ k)
      = .ok (boolVal (decide (n ≥ k))) := by
  have h1 : (⟨32, true⟩ : IntTy).toInt n = (n : Int) := by
    unfold IntTy.toInt
    simp [show (2 : Nat) ^ (32 - 1) = 2147483648 from rfl, ite_eq_right (show ¬ (2147483648 ≤ n) from by omega)]
  have h2 : (⟨32, true⟩ : IntTy).toInt k = (k : Int) := by
    unfold IntTy.toInt
    simp [show (2 : Nat) ^ (32 - 1) = 2147483648 from rfl, ite_eq_right (show ¬ (2147483648 ≤ k) from by omega)]
  simp [evalBin, evalBinInt, binInt, intOf, isPtr, boolVal, h1, h2, decide_eq_true_eq]
theorem bin_i32_le_bytes (n k : Nat) (hn : n < 256) (hk : k < 256) :
    evalBin .le (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ k)
      = .ok (boolVal (decide (n ≤ k))) := by
  have h1 : (⟨32, true⟩ : IntTy).toInt n = (n : Int) := by
    unfold IntTy.toInt
    simp [show (2 : Nat) ^ (32 - 1) = 2147483648 from rfl, ite_eq_right (show ¬ (2147483648 ≤ n) from by omega)]
  have h2 : (⟨32, true⟩ : IntTy).toInt k = (k : Int) := by
    unfold IntTy.toInt
    simp [show (2 : Nat) ^ (32 - 1) = 2147483648 from rfl, ite_eq_right (show ¬ (2147483648 ≤ k) from by omega)]
  simp [evalBin, evalBinInt, binInt, intOf, isPtr, ptrEq, boolVal, h1, h2]
theorem bin_i32_eq_bytes (n k : Nat) (hn : n < 256) (hk : k < 256) :
    evalBin .eq (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ k)
      = .ok (boolVal (decide (n = k))) := by
  have h1 : (⟨32, true⟩ : IntTy).toInt n = (n : Int) := by
    unfold IntTy.toInt
    simp [show (2 : Nat) ^ (32 - 1) = 2147483648 from rfl, ite_eq_right (show ¬ (2147483648 ≤ n) from by omega)]
  have h2 : (⟨32, true⟩ : IntTy).toInt k = (k : Int) := by
    unfold IntTy.toInt
    simp [show (2 : Nat) ^ (32 - 1) = 2147483648 from rfl, ite_eq_right (show ¬ (2147483648 ≤ k) from by omega)]
  simp [evalBin, evalBinInt, binInt, intOf, isPtr, boolVal, h1, h2, Int.ofNat_inj, decide_eq_true_eq]
theorem bin_i32_ge_bytes_true (n k : Nat) (hn : n < 256) (hk : k < 256) (h : n ≥ k) :
    evalBin .ge (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ k) = .ok (boolVal true) := by
  rw [bin_i32_ge_bytes n k hn hk]
  simp [decide_eq_true_eq, h]
theorem bin_i32_ge_bytes_false (n k : Nat) (hn : n < 256) (hk : k < 256) (h : n < k) :
    evalBin .ge (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ k) = .ok (boolVal false) := by
  rw [bin_i32_ge_bytes n k hn hk]
  simp [decide_eq_false_iff_not, show ¬ n ≥ k from by omega]
theorem bin_i32_eq_bytes_true (n k : Nat) (hn : n < 256) (hk : k < 256) (h : n = k) :
    evalBin .eq (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ k) = .ok (boolVal true) := by
  rw [bin_i32_eq_bytes n k hn hk]
  simp [decide_eq_true_eq, h]
theorem bin_i32_eq_bytes_false (n k : Nat) (hn : n < 256) (hk : k < 256) (h : n ≠ k) :
    evalBin .eq (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ k) = .ok (boolVal false) := by
  rw [bin_i32_eq_bytes n k hn hk]
  simp [decide_eq_false_iff_not, h]
theorem truthy_boolVal (y : Bool) : truthy (boolVal y) = .ok y := by
  cases y <;> simp [truthy, boolVal]

theorem bin_u64_ge_true (n k : Nat) (h : n ≥ k) :
    evalBin .ge (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ k) = .ok (boolVal true) := by
  rw [bin_u64_ge]
  simp [decide_eq_true_eq, h]
theorem bin_u64_ge_false (n k : Nat) (h : n < k) :
    evalBin .ge (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ k) = .ok (boolVal false) := by
  rw [bin_u64_ge]
  simp [decide_eq_false_iff_not, show ¬ n ≥ k from by omega]

/-- Unsigned u32 comparison. -/
theorem bin_u32_lt (n k : Nat) : evalBin .lt (some ⟨32, false⟩) (.int ⟨32, false⟩ n) (.int ⟨32, false⟩ k)
    = .ok (boolVal (decide (n < k))) := rfl

/-- Unsigned u64 comparisons and addition. -/
theorem bin_u64_lt (n k : Nat) : evalBin .lt (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ k)
    = .ok (boolVal (decide (n < k))) := rfl

theorem bin_u64_gt (n k : Nat) : evalBin .gt (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ k)
    = .ok (boolVal (decide (n > k))) := rfl

theorem bin_u64_add (n k : Nat) (h : n + k < 2 ^ 64) :
    evalBin .add (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ k)
      = .ok (.int ⟨64, false⟩ (n + k)) := by
  simp [evalBin, evalBinInt, binInt, IntTy.modulus, isPtr, ptrEq, intOf, Int.ofNat_lt, h]

/-- Casting an unsigned u16 to u64 preserves the value. -/
theorem u16_u64_cast (n : Nat) (h : n < 65536) :
    evalCast ⟨64, false⟩ (.int ⟨16, false⟩ n) = .ok (.int ⟨64, false⟩ n) := by
  simp [evalCast, IntTy.modulus, IntTy.wrap, Int.ofNat_lt, show (n : Nat) < 18446744073709551616 from by omega]

/-- Casting an unsigned u32 to u64 preserves the value. -/
theorem u32_u64_cast (n : Nat) (h : n < 2 ^ 32) :
    evalCast ⟨64, false⟩ (.int ⟨32, false⟩ n) = .ok (.int ⟨64, false⟩ n) := by
  simp [evalCast, IntTy.modulus, IntTy.wrap, Int.ofNat_lt, show (n : Nat) < 18446744073709551616 from by omega]

/-- Casting a small signed i32 literal to u64 preserves the value. -/
theorem i32_u64_cast_small (n : Nat) (h : n < 2147483648) :
    evalCast ⟨64, false⟩ (.int ⟨32, true⟩ n) = .ok (.int ⟨64, false⟩ n) := by
  have h2 : IntTy.toInt ⟨32, true⟩ n = (n : Int) := toInt_i32_small h
  have h3 : (n : Int) % (18446744073709551616 : Int) = ↑n := Int.emod_eq_of_lt (by omega) (by omega)
  simp [evalCast, IntTy.modulus, IntTy.wrap, h2, h3, Int.toNat_natCast]

/-- Cast of a struct field offset value to u64 (reads as unsigned). -/
theorem u64_cast_u32 (n : Nat) (h : n < 2 ^ 32) :
    evalCast ⟨64, false⟩ (.int ⟨32, false⟩ n) = .ok (.int ⟨64, false⟩ n) :=
  u32_u64_cast n h

theorem bin_u64_eq (n k : Nat) : evalBin .eq (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ k)
    = .ok (boolVal (decide (n = k))) := rfl
theorem bin_u64_le (n k : Nat) : evalBin .le (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ k)
    = .ok (boolVal (decide (n ≤ k))) := rfl
theorem bin_u64_div (n k : Nat) (hk : k ≠ 0) :
    evalBin .div (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ k)
      = .ok (.int ⟨64, false⟩ (n / k)) := by
  simp [evalBin, evalBinInt, binInt, intOf, IntTy.modulus, isPtr, arith, hk]

/-- `.ne` on unsigned u32/u16 is raw `decide (a ≠ b)`. -/
theorem bin_u32_ne (n k : Nat) : evalBin .ne (some ⟨32, false⟩) (.int ⟨32, false⟩ n) (.int ⟨32, false⟩ k)
    = .ok (boolVal (decide (n ≠ k))) := rfl
theorem bin_u32_eq (n k : Nat) : evalBin .eq (some ⟨32, false⟩) (.int ⟨32, false⟩ n) (.int ⟨32, false⟩ k)
    = .ok (boolVal (decide (n = k))) := rfl
theorem bin_u32_le (n k : Nat) : evalBin .le (some ⟨32, false⟩) (.int ⟨32, false⟩ n) (.int ⟨32, false⟩ k)
    = .ok (boolVal (decide (n ≤ k))) := rfl
theorem bin_u32_ltu (n k : Nat) : evalBin .lt (some ⟨32, false⟩) (.int ⟨32, false⟩ n) (.int ⟨32, false⟩ k)
    = .ok (boolVal (decide (n < k))) := rfl

theorem bin_i32_eq (n k : Nat) : evalBin .eq (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ k)
    = .ok (boolVal (decide (IntTy.toInt ⟨32, true⟩ n = IntTy.toInt ⟨32, true⟩ k))) := by
  simp [evalBin, evalBinInt, binInt, intOf, isPtr, ptrEq, IntTy.toInt]

/-- Signed i32 `.ne`. -/
theorem bin_i32_ne (n k : Nat) : evalBin .ne (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ k)
    = .ok (boolVal (decide (IntTy.toInt ⟨32, true⟩ n ≠ IntTy.toInt ⟨32, true⟩ k))) := by
  simp [evalBin, evalBinInt, binInt, intOf, isPtr, ptrEq, IntTy.toInt]

/-- Signed i32 `.eq`/`.lt` against literal `0`. -/
theorem bin_i32_eq0 (n : Nat) : evalBin .eq (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ 0)
    = .ok (boolVal (decide (IntTy.toInt ⟨32, true⟩ n = IntTy.toInt ⟨32, true⟩ 0))) := rfl
theorem bin_i32_le0 (n : Nat) : evalBin .le (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ 0)
    = .ok (boolVal (decide (IntTy.toInt ⟨32, true⟩ n ≤ 0))) := by
  have h0 : IntTy.toInt ⟨32, true⟩ 0 = 0 := by
    simp [IntTy.toInt]
  simp [evalBin, evalBinInt, binInt, intOf, isPtr, ptrEq, IntTy.toInt, h0]

/-- Signed i32 `.lt` against literal `0`. -/
theorem bin_i32_lt0 (n : Nat) : evalBin .lt (some ⟨32, true⟩) (.int ⟨32, true⟩ n) (.int ⟨32, true⟩ 0)
    = .ok (boolVal (decide (IntTy.toInt ⟨32, true⟩ n < 0))) := by
  have h0 : IntTy.toInt ⟨32, true⟩ 0 = 0 := by
    simp [IntTy.toInt]
  simp [evalBin, evalBinInt, binInt, intOf, isPtr, ptrEq, IntTy.toInt, h0]

/-- The BMP "toInt32" interpretation of a 32-bit word, with sign reading
    as in the C `int32_t` cast. This is the same as `IntTy.toInt ⟨32, true⟩`. -/
def toInt32 (n : Nat) : Int := if n ≥ 2 ^ 31 then (n : Int) - 2 ^ 32 else (n : Int)

theorem toInt32_eq (n : Nat) (h : n < 4294967296) :
    toInt32 n = IntTy.toInt ⟨32, true⟩ n := by
  unfold toInt32 IntTy.toInt IntTy.modulus
  simp [IntTy.signed, IntTy.width]

/-- Signed-to-unsigned cast preserves Nat for any word in range. -/
theorem cast_u32_i32 (n : Nat) (h : n < 4294967296) :
    evalCast ⟨32, false⟩ (.int ⟨32, true⟩ n) = .ok (.int ⟨32, false⟩ n) := by
  have hol : ((⟨32, false⟩ : IntTy).wrap (IntTy.toInt ⟨32, true⟩ n)) = n := by
    unfold IntTy.wrap IntTy.toInt IntTy.modulus IntTy.width
    simp [show (2 : Nat) ^ (32 - 1) = 2147483648 from rfl]
    by_cases hn : 2147483648 ≤ n
    · simp [hn]
      omega
    · simp [hn]
      omega
  simp [evalCast, IntTy.signed, hol]

theorem u16_u32_cast (n : Nat) (h : n < 65536) :
    evalCast ⟨32, false⟩ (.int ⟨16, false⟩ n) = .ok (.int ⟨32, false⟩ n) := by
  simp [evalCast, IntTy.modulus, Nat.mod_eq_of_lt (show n < 4294967296 from by omega)]


/-- Split `inRange` for i32 into two decide facts. -/
theorem inRange_i32_split (x : Int) (hn : IntTy.inRange ⟨32, true⟩ x = true) :
    -2147483648 ≤ x ∧ x ≤ 2147483647 := by
  rw [show IntTy.inRange ⟨32, true⟩ x =
      (decide (-2147483648 ≤ x) && decide (x ≤ 2147483647)) from rfl] at hn
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
  exact ⟨hn.1, hn.2⟩

/-- `(int32_t)(-(int32_t)n)`: `.un .neg` of a 32-bit signed value with
`inRange` true — the equation `arith` needs. -/
theorem evalUnNegI32 (n : Nat)
    (hn : IntTy.inRange ⟨32, true⟩ (-IntTy.toInt ⟨32, true⟩ n) = true) :
    evalUn .neg ⟨32, true⟩ (.int ⟨32, true⟩ n) =
    .ok (.int ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ (-IntTy.toInt ⟨32, true⟩ n))) := by
  obtain ⟨h1, h2⟩ := inRange_i32_split (-IntTy.toInt ⟨32, true⟩ n) hn
  have heq : evalUn .neg ⟨32, true⟩ (.int ⟨32, true⟩ n) =
      arith ⟨32, true⟩ (-IntTy.toInt ⟨32, true⟩ n) := rfl
  rw [heq]
  exact arith_i32_rng h1 h2


/-- Unsigned u64 multiplication (wrapping; hypothesis rules out overflow). -/
theorem bin_u64_mul (n k : Nat) (h : n * k < 2 ^ 64) :
    evalBin .mul (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ k)
      = .ok (.int ⟨64, false⟩ (n * k)) := by
  simp [evalBin, evalBinInt, binInt, intOf, IntTy.modulus, isPtr, h]

/-- Unsigned u64 right shift by literal 5 (used by the row-stride round-up). -/
theorem bin_u64_shr_5 (n : Nat) :
    evalBin .shr (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ 5)
      = .ok (.int ⟨64, false⟩ (n / 2 ^ 5)) := by
  have h5 : IntTy.toInt ⟨64, false⟩ 5 = 5 := rfl
  simp [evalBin, evalBinInt, binInt, intOf, IntTy.modulus, isPtr, h5, C.guard]

/-- Unsigned u64 left shift by literal 2 (multiply by 4, wrapping excluded
    by the hypothesis). -/
theorem bin_u64_shl_2 (n : Nat) (h : n * 4 < 2 ^ 64) :
    evalBin .shl (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ 2)
      = .ok (.int ⟨64, false⟩ (n * 4)) := by
  have h2 : IntTy.toInt ⟨64, false⟩ 2 = 2 := rfl
  have hM : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [hM] at h
  simp [evalBin, evalBinInt, binInt, intOf, IntTy.modulus, isPtr, h2, C.guard, h]


/-- Unsigned u64 right shift by a 32-bit literal 5. -/
theorem bin_u64_shr_5_c32 (n : Nat) :
    evalBin .shr (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨32, false⟩ 5)
      = .ok (.int ⟨64, false⟩ (n / 2 ^ 5)) := by
  have h5 : IntTy.toInt ⟨32, false⟩ 5 = 5 := rfl
  simp [evalBin, evalBinInt, binInt, intOf, IntTy.modulus, isPtr, h5, C.guard]

/-- Unsigned u64 left shift by a 32-bit literal 2. -/
theorem bin_u64_shl_2_c32 (n : Nat) (h : n * 4 < 2 ^ 64) :
    evalBin .shl (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨32, false⟩ 2)
      = .ok (.int ⟨64, false⟩ (n * 4)) := by
  have h2 : IntTy.toInt ⟨32, false⟩ 2 = 2 := rfl
  have hM : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [hM] at h
  simp [evalBin, evalBinInt, binInt, intOf, IntTy.modulus, isPtr, h2, C.guard, h]


theorem bin_u64_sub (n k : Nat) (h : k ≤ n) :
    evalBin .sub (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ k)
      = .ok (.int ⟨64, false⟩ (n - k)) := by
  simp [evalBin, evalBinInt, binInt, intOf, IntTy.modulus, isPtr, h]

theorem bin_u64_lor_bool (n k : Nat) :
    evalBin .bor (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ k)
      = .ok (.int ⟨64, false⟩ (n ||| k)) := by
  simp [evalBin, evalBinInt, binInt, intOf, IntTy.modulus, isPtr]

theorem bin_u64_add_wrap (n k : Nat) :
    evalBin .add (some ⟨64, false⟩) (.int ⟨64, false⟩ n) (.int ⟨64, false⟩ k)
      = .ok (.int ⟨64, false⟩ ((n + k) % 18446744073709551616)) := by
  simp [evalBin, evalBinInt, binInt, intOf, IntTy.modulus, isPtr]

/-- Casting u64 to u32: keeps the low 32 bits (modular), value unchanged. -/
theorem u64_u32_trunc_cast (n : Nat) (h : n < 4294967296) :
    evalCast ⟨32, false⟩ (.int ⟨64, false⟩ n) = .ok (.int ⟨32, false⟩ n) := by
  simp [evalCast, IntTy.modulus, Nat.mod_eq_of_lt (show n < 4294967296 from h)]

end NANO.C
