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
