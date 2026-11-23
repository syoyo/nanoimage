/-
  Spec-side materialisation lemmas for the TGA loader.
-/
import NANO.Basic
import NANO.Tga

namespace NANO

theorem getD_eq_getElem {l : List UInt8} {n : Nat} (h : n < l.length) : l.getD n 0 = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem take_snoc_getD (l : List UInt8) (n : Nat) (h : n < l.length) :
    l.take n ++ [l.getD n 0] = l.take (n + 1) := by
  rw [List.take_succ_eq_append_getElem h, getD_eq_getElem h]

theorem fold_set_range_aux (buf bs : List UInt8) (i n : Nat)
    (hn : n ≤ bs.length) (hb : i + n ≤ buf.length) :
    (List.range n).foldl (fun b k => b.set (i + k) (bs.getD k 0)) buf
      = buf.take i ++ bs.take n ++ buf.drop (i + n) := by
  induction n with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, List.take_zero, List.append_nil, Nat.add_zero]
    exact (List.take_append_drop i buf).symm
  | succ n ih =>
    have hn' : n ≤ bs.length := by omega
    have hb' : i + n ≤ buf.length := by omega
    have hih := ih hn' hb'
    have hln : n < bs.length := by omega
    have hA : (buf.take i).length = i := by rw [List.length_take, Nat.min_eq_left (by omega)]
    have hB : (bs.take n).length = n := by rw [List.length_take, Nat.min_eq_left (by omega)]
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hih]
    have hLlen : (buf.take i ++ bs.take n ++ buf.drop (i + n)).length = buf.length := by
      simp [List.length_append, List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
      omega
    have hlt : i + n < (buf.take i ++ bs.take n ++ buf.drop (i + n)).length := by rw [hLlen]; omega
    have hlenAB : (buf.take i ++ bs.take n).length = i + n := by simp [List.length_append, hA, hB]
    have htake : (buf.take i ++ bs.take n ++ buf.drop (i + n)).take (i + n) = buf.take i ++ bs.take n := by
      conv => lhs; rw [show i + n = (buf.take i ++ bs.take n).length from hlenAB.symm]
      rw [List.take_append_length]
    have hdrop : (buf.take i ++ bs.take n ++ buf.drop (i + n)).drop (i + n + 1) = buf.drop (i + n + 1) := by
      conv => lhs; rw [show i + n + 1 = (buf.take i ++ bs.take n).length + 1 from by rw [hlenAB]]
      rw [List.drop_length_add_append, List.drop_drop]
    have hsnoc : bs.take n ++ (bs.getD n 0 :: List.drop (i + n + 1) buf)
        = bs.take (n + 1) ++ List.drop (i + n + 1) buf := by
      rw [show bs.getD n 0 :: List.drop (i + n + 1) buf = [bs.getD n 0] ++ List.drop (i + n + 1) buf from rfl,
          ← List.append_assoc, take_snoc_getD bs n hln]
    rw [List.set_eq_take_append_cons_drop, if_pos hlt, htake, hdrop]
    simp only [List.append_assoc]
    rw [hsnoc]
    rw [show i + n + 1 = i + (n + 1) by omega]

theorem tgaWriteAt_eq (buf : List UInt8) (i : Nat) (bs : List UInt8)
    (h : i + bs.length ≤ buf.length) :
    tgaWriteAt buf (i, bs) = buf.take i ++ bs ++ buf.drop (i + bs.length) := by
  simp only [tgaWriteAt]
  rw [fold_set_range_aux buf bs i bs.length (Nat.le_refl _) h, List.take_length]

end NANO

namespace NANO

theorem fold_set_range_length (buf bs : List UInt8) (i n : Nat) :
    ((List.range n).foldl (fun b k => b.set (i + k) (bs.getD k 0)) buf).length = buf.length := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [List.length_set, ih]

theorem tgaWriteAt_length (buf : List UInt8) (i : Nat) (bs : List UInt8) :
    (tgaWriteAt buf (i, bs)).length = buf.length := by
  simp only [tgaWriteAt]
  exact fold_set_range_length buf bs i bs.length

theorem tgaMaterialize_snoc (n : Nat) (ws : List TgaWrite) (w : TgaWrite) :
    tgaMaterialize n (ws ++ [w]) = tgaWriteAt (tgaMaterialize n ws) w := by
  simp only [tgaMaterialize, List.foldl_append, List.foldl_cons, List.foldl_nil]

end NANO

namespace NANO

theorem tgaWriteAt_append (buf : List UInt8) (i : Nat) (bs cs : List UInt8)
    (h : i + bs.length + cs.length ≤ buf.length) :
    tgaWriteAt (tgaWriteAt buf (i, bs)) (i + bs.length, cs)
      = buf.take i ++ bs ++ cs ++ buf.drop (i + bs.length + cs.length) := by
  have h1 : i + bs.length ≤ buf.length := by omega
  have inner := tgaWriteAt_eq buf i bs h1
  have hlen : (buf.take i ++ bs).length = i + bs.length := by
    rw [List.length_append, List.length_take, Nat.min_eq_left (by omega)]
  have htake : (buf.take i ++ bs ++ buf.drop (i + bs.length)).take (i + bs.length) = buf.take i ++ bs := by
    conv => lhs; rw [show i + bs.length = (buf.take i ++ bs).length from hlen.symm]
    rw [List.take_append_length]
  have hdrop : (buf.take i ++ bs ++ buf.drop (i + bs.length)).drop (i + bs.length + cs.length)
      = buf.drop (i + bs.length + cs.length) := by
    conv => lhs; rw [show i + bs.length + cs.length = (buf.take i ++ bs).length + cs.length from by rw [hlen]]
    rw [List.drop_length_add_append, List.drop_drop]
  have h2 : i + bs.length + cs.length ≤ (buf.take i ++ bs ++ buf.drop (i + bs.length)).length := by
    have : (buf.take i ++ bs ++ buf.drop (i + bs.length)).length = buf.length := by
      simp [List.length_append, List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
      omega
    rw [this]; omega
  rw [inner]
  rw [tgaWriteAt_eq (buf.take i ++ bs ++ buf.drop (i + bs.length)) (i + bs.length) cs h2]
  rw [htake, hdrop]

end NANO

namespace NANO
open NANO

/-- Fold `i` successive writes of the same bytes at the RLE pixel offsets. -/
def tgaFoldI (obl : List UInt8) (h : TgaInfo) (p0 : Nat) (bytes : List UInt8) : Nat → List UInt8
  | 0 => obl
  | i + 1 => tgaWriteAt (tgaFoldI obl h p0 bytes i) (tgaDstIndex h (p0 + i), bytes)

theorem tgaFoldI_succ (obl : List UInt8) (h : TgaInfo) (p0 : Nat) (bytes : List UInt8) (i : Nat) :
    tgaFoldI obl h p0 bytes (i + 1)
      = tgaWriteAt (tgaFoldI obl h p0 bytes i) (tgaDstIndex h (p0 + i), bytes) := rfl

theorem tgaFoldI_length (obl : List UInt8) (h : TgaInfo) (p0 : Nat) (bytes : List UInt8) (i : Nat) :
    (tgaFoldI obl h p0 bytes i).length = obl.length := by
  induction i with
  | zero => rfl
  | succ i ih => rw [tgaFoldI_succ, tgaWriteAt_length, ih]

end NANO

namespace NANO
open NANO

/-- Fold `i` successive uncompressed writes: pixel `j` reads bytes at
    `off0 + j*ch` and lands at `tgaDstIndex h (p0+j)`. -/
def tgaFoldRaw (obl : List UInt8) (h : TgaInfo) (p0 off0 ch : Nat) (dat : List UInt8) : Nat → List UInt8
  | 0 => obl
  | i + 1 => tgaWriteAt (tgaFoldRaw obl h p0 off0 ch dat i)
      (tgaDstIndex h (p0 + i),
       tgaPixelOut ch (UInt8.ofNat (byteAt dat (off0 + i * ch))) (UInt8.ofNat (byteAt dat (off0 + i * ch + 1)))
         (UInt8.ofNat (byteAt dat (off0 + i * ch + 2))) (UInt8.ofNat (byteAt dat (off0 + i * ch + 3))))

theorem tgaFoldRaw_succ (obl : List UInt8) (h : TgaInfo) (p0 off0 ch : Nat) (dat : List UInt8) (i : Nat) :
    tgaFoldRaw obl h p0 off0 ch dat (i + 1)
      = tgaWriteAt (tgaFoldRaw obl h p0 off0 ch dat i)
          (tgaDstIndex h (p0 + i),
           tgaPixelOut ch (UInt8.ofNat (byteAt dat (off0 + i * ch))) (UInt8.ofNat (byteAt dat (off0 + i * ch + 1)))
             (UInt8.ofNat (byteAt dat (off0 + i * ch + 2))) (UInt8.ofNat (byteAt dat (off0 + i * ch + 3)))) := rfl

theorem tgaFoldRaw_length (obl : List UInt8) (h : TgaInfo) (p0 off0 ch : Nat) (dat : List UInt8) (i : Nat) :
    (tgaFoldRaw obl h p0 off0 ch dat i).length = obl.length := by
  induction i with
  | zero => rfl
  | succ i ih => rw [tgaFoldRaw_succ, tgaWriteAt_length, ih]

end NANO
