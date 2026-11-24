import NANO.Tga
import NANO.TgaWrites

/-
  Spec-side (reference `tgaWritesAux`) per-packet unfolding lemmas.

  `tgaWritesAux` processes one packet per recursive step: an (optional) header
  read, a count check, an (optional) pixel-byte read, then a `count`-iteration
  inner fold.  These lemmas expose one such step for the RLE-run and raw packet
  forms, with the runtime header value `byteAt dat off`, so the machine-side
  loop-1 fuel induction can match the buffer step-for-step.
-/

namespace NANO
open NANO

/-- One RLE-run packet step of `tgaWritesAux` (header high bit set): appends
    `count` copies of the packet pixel. -/
theorem tgaWritesAux_rle_pkt (dat : List UInt8) (h : TgaInfo) (fuel left off : Nat) (acc : List TgaWrite)
    (hrne : h.rle ≠ 0) (hleft : left ≠ 0) (hoff : off < dat.length)
    (hcnt : (byteAt dat off &&& 0x7f) + 1 ≤ left)
    (hbit : (byteAt dat off &&& 0x80) ≠ 0)
    (hbnd : off + 1 + h.channels ≤ dat.length) :
    tgaWritesAux dat h (fuel + 1) left off acc
      = tgaWritesAux dat h fuel (left - ((byteAt dat off &&& 0x7f) + 1)) (off + 1 + h.channels)
          (acc ++ (List.range ((byteAt dat off &&& 0x7f) + 1)).map
            (fun i => (tgaDstIndex h (h.width * h.height - left + i),
              tgaPixelOut h.channels (dat.getD (off+1) 0) (dat.getD (off+2) 0) (dat.getD (off+3) 0) (dat.getD (off+4) 0)))) := by
  conv => lhs; rw [tgaWritesAux]
  simp only [if_neg hleft, if_pos hrne, if_neg (by omega : ¬ off ≥ dat.length),
    if_neg (by omega : ¬ left < (byteAt dat off &&& 0x7f) + 1), pure_bind,
    if_neg (by omega : ¬ (byteAt dat off &&& 0x7f) + 1 > left),
    if_neg (by omega : ¬ off + 1 + h.channels > dat.length),
    if_pos (by simp [hbit] : (h.rle = 0 ∨ byteAt dat off &&& 0x80 ≠ 0)),
    if_neg (by simp [hbit] : ¬ (h.rle ≠ 0 ∧ byteAt dat off &&& 0x80 = 0))]
  rw [foldlM_rle_writes]
  rfl

/-- The guarded raw-packet write step: read a pixel, or throw 11 on overrun. -/
def tgaHawStep (h : TgaInfo) (dat : List UInt8) (p0 : Nat) (i : Nat) :
    Nat × List TgaWrite → Except Nat (Nat × List TgaWrite) := fun st =>
  if st.1 + h.channels > dat.length then throw 11
  else pure (st.1 + h.channels, st.2 ++ [(tgaDstIndex h (p0 + i),
    tgaPixelOut h.channels (dat.getD st.1 0) (dat.getD (st.1 + 1) 0)
      (dat.getD (st.1 + 2) 0) (dat.getD (st.1 + 3) 0))])

/-- One raw packet step of `tgaWritesAux` (header high bit clear): reads a
    pixel per index, advancing the data cursor by `channels` each time. -/
theorem tgaWritesAux_raw_pkt (dat : List UInt8) (h : TgaInfo) (fuel left off : Nat) (acc : List TgaWrite)
    (hrne : h.rle ≠ 0) (hleft : left ≠ 0) (hoff : off < dat.length)
    (hcnt : (byteAt dat off &&& 0x7f) + 1 ≤ left)
    (hbit : (byteAt dat off &&& 0x80) = 0)
    (hbnd : ∀ i, i < (byteAt dat off &&& 0x7f) + 1 → off + 1 + i * h.channels + h.channels ≤ dat.length) :
    tgaWritesAux dat h (fuel + 1) left off acc
      = tgaWritesAux dat h fuel (left - ((byteAt dat off &&& 0x7f) + 1))
          (off + 1 + ((byteAt dat off &&& 0x7f) + 1) * h.channels)
          (acc ++ (List.range ((byteAt dat off &&& 0x7f) + 1)).map
            (fun i => (tgaDstIndex h (h.width * h.height - left + i),
              tgaPixelOut h.channels (dat.getD (off + 1 + i * h.channels) 0) (dat.getD (off + 1 + i * h.channels + 1) 0)
                (dat.getD (off + 1 + i * h.channels + 2) 0) (dat.getD (off + 1 + i * h.channels + 3) 0)))) := by
  conv => lhs; rw [tgaWritesAux]
  simp only [if_neg hleft, if_pos hrne, if_neg (by omega : ¬ off ≥ dat.length),
    if_neg (by omega : ¬ left < (byteAt dat off &&& 0x7f) + 1), pure_bind,
    if_neg (by omega : ¬ (byteAt dat off &&& 0x7f) + 1 > left),
    if_neg (by simp [hrne, hbit] : ¬ (h.rle = 0 ∨ byteAt dat off &&& 0x80 ≠ 0))]
  have htrue : (h.rle ≠ 0 ∧ byteAt dat off &&& 0x80 = 0) = True := by simp [hrne, hbit]
  have hle : ¬ (off + 1 + h.channels > dat.length) := by
    have := hbnd 0 (Nat.succ_pos _); omega
  simp only [htrue, if_true, hle, if_false]
  have hcont := foldlM_raw_cont ((byteAt dat off &&& 0x7f) + 1) (off + 1) h.channels dat
      (fun o i => (tgaDstIndex h (h.width * h.height - left + i),
        tgaPixelOut h.channels (dat.getD o 0) (dat.getD (o + 1) 0) (dat.getD (o + 2) 0) (dat.getD (o + 3) 0))) acc
      (by intro i hi; exact hbnd i hi)
      (fun o acc' => tgaWritesAux dat h fuel (left - ((byteAt dat off &&& 0x7f) + 1)) o acc')
  exact hcont


/-- One uncompressed (rle=0) packet step of `tgaWritesAux`: exactly one write,
    cursor advances by `channels`. -/
theorem tgaWritesAux_rle0_pkt (dat : List UInt8) (h : TgaInfo) (fuel left off : Nat) (acc : List TgaWrite)
    (hrle0 : h.rle = 0) (hleft : left ≠ 0)
    (hbnd : off + h.channels ≤ dat.length) :
    tgaWritesAux dat h (fuel + 1) left off acc
      = tgaWritesAux dat h fuel (left - 1) (off + h.channels)
          (acc ++ [(tgaDstIndex h (h.width * h.height - left),
            tgaPixelOut h.channels (dat.getD off 0) (dat.getD (off + 1) 0) (dat.getD (off + 2) 0) (dat.getD (off + 3) 0))]) := by
  rw [tgaWritesAux.eq_def]
  simp only [Nat.reduceEqDiff, ↓reduceIte, hrle0, hleft, Bool.false_eq_true, reduceCtorEq, Nat.not_le, Nat.not_lt]
  simp (config := { maxSteps := 2000000 })
  rw [if_neg hleft]
  rw [if_neg (show ¬ (dat.length < off + h.channels) from by omega)]

theorem tgaWritesAux_rle0_walk (dat : List UInt8) (h : TgaInfo) (hrle0 : h.rle = 0) :
    ∀ (d : Nat) (acc : List TgaWrite), d ≤ h.width * h.height →
    (∀ i, i < d → (h.dataOffset + (h.width * h.height - d) * h.channels + i * h.channels) + h.channels ≤ dat.length) →
    tgaWritesAux dat h d d (h.dataOffset + (h.width * h.height - d) * h.channels) acc
      = Except.ok (acc ++ (List.range d).map (fun i =>
          (tgaDstIndex h (h.width * h.height - d + i),
           tgaPixelOut h.channels (dat.getD (h.dataOffset + (h.width * h.height - d) * h.channels + i * h.channels) 0)
             (dat.getD (h.dataOffset + (h.width * h.height - d) * h.channels + i * h.channels + 1) 0)
             (dat.getD (h.dataOffset + (h.width * h.height - d) * h.channels + i * h.channels + 2) 0)
             (dat.getD (h.dataOffset + (h.width * h.height - d) * h.channels + i * h.channels + 3) 0)))) := by
  intro d
  induction d with
  | zero =>
    intro acc _ _
    rw [show tgaWritesAux dat h 0 0 (h.dataOffset + (h.width * h.height - 0) * h.channels) acc = Except.ok acc from rfl]
    simp
  | succ d ih =>
    intro acc hd hbnd
    have hb0 : (h.dataOffset + (h.width * h.height - (d+1)) * h.channels) + h.channels ≤ dat.length := by
      have := hbnd 0 (by omega); rw [Nat.zero_mul, Nat.add_zero] at this
      rw [show h.width * h.height - (d+1) = h.width * h.height - d - 1 from by omega] at this ⊢; omega
    rw [tgaWritesAux_rle0_pkt dat h d (d+1) (h.dataOffset + (h.width * h.height - (d+1)) * h.channels) acc hrle0 (by omega) hb0]
    rw [show d + 1 - 1 = d from by omega]
    have hcur : (h.dataOffset + (h.width * h.height - (d+1)) * h.channels) + h.channels
        = h.dataOffset + (h.width * h.height - d) * h.channels := by
      have : h.width * h.height - d = (h.width * h.height - (d+1)) + 1 := by omega
      rw [this, Nat.succ_mul]; omega
    rw [hcur]
    rw [ih (acc ++ [(tgaDstIndex h (h.width * h.height - (d+1)),
        tgaPixelOut h.channels (dat.getD (h.dataOffset + (h.width * h.height - (d+1)) * h.channels) 0)
          (dat.getD (h.dataOffset + (h.width * h.height - (d+1)) * h.channels + 1) 0)
          (dat.getD (h.dataOffset + (h.width * h.height - (d+1)) * h.channels + 2) 0)
          (dat.getD (h.dataOffset + (h.width * h.height - (d+1)) * h.channels + 3) 0))])
      (by omega)
      (fun i hi => by
        have := hbnd (i+1) (by omega)
        rw [show h.dataOffset + (h.width * h.height - d) * h.channels + i * h.channels + h.channels
              = h.dataOffset + (h.width * h.height - (d+1)) * h.channels + (i+1) * h.channels + h.channels from by
          rw [show h.width * h.height - d = h.width * h.height - (d+1) + 1 from by omega, Nat.succ_mul, Nat.add_mul]; omega]
        exact this)]
    have hlist : ([(tgaDstIndex h (h.width * h.height - (d+1)),
        tgaPixelOut h.channels (dat.getD (h.dataOffset + (h.width * h.height - (d+1)) * h.channels) 0)
          (dat.getD (h.dataOffset + (h.width * h.height - (d+1)) * h.channels + 1) 0)
          (dat.getD (h.dataOffset + (h.width * h.height - (d+1)) * h.channels + 2) 0)
          (dat.getD (h.dataOffset + (h.width * h.height - (d+1)) * h.channels + 3) 0))] ++
        (List.range d).map (fun i =>
          (tgaDstIndex h (h.width * h.height - d + i),
           tgaPixelOut h.channels (dat.getD (h.dataOffset + (h.width * h.height - d) * h.channels + i * h.channels) 0)
             (dat.getD (h.dataOffset + (h.width * h.height - d) * h.channels + i * h.channels + 1) 0)
             (dat.getD (h.dataOffset + (h.width * h.height - d) * h.channels + i * h.channels + 2) 0)
             (dat.getD (h.dataOffset + (h.width * h.height - d) * h.channels + i * h.channels + 3) 0))))
      = (List.range (d+1)).map (fun i =>
          (tgaDstIndex h (h.width * h.height - (d+1) + i),
           tgaPixelOut h.channels (dat.getD (h.dataOffset + (h.width * h.height - (d+1)) * h.channels + i * h.channels) 0)
             (dat.getD (h.dataOffset + (h.width * h.height - (d+1)) * h.channels + i * h.channels + 1) 0)
             (dat.getD (h.dataOffset + (h.width * h.height - (d+1)) * h.channels + i * h.channels + 2) 0)
             (dat.getD (h.dataOffset + (h.width * h.height - (d+1)) * h.channels + i * h.channels + 3) 0))) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.zero_mul, Nat.add_zero]
      rw [List.singleton_append]
      congr 1
      apply List.map_congr_left
      intro a ha
      simp only [Function.comp_apply]
      rw [Prod.mk.injEq]
      constructor
      · rw [show h.width * h.height - (d+1) + (a+1) = h.width * h.height - d + a from by omega]
      · rw [show h.dataOffset + (h.width * h.height - (d+1)) * h.channels + (a+1) * h.channels
              = h.dataOffset + (h.width * h.height - d) * h.channels + a * h.channels from by
          rw [show h.width * h.height - d = h.width * h.height - (d+1) + 1 from by omega, Nat.succ_mul, Nat.add_mul]; omega]
    rw [List.append_assoc]
    rw [hlist]

theorem tgaWritesAux_ok_off {dat : List UInt8} {h : TgaInfo} {fuel left off : Nat} {acc res : List TgaWrite}
    (hrne : h.rle ≠ 0) (hleft : left ≠ 0)
    (hok : tgaWritesAux dat h (fuel + 1) left off acc = Except.ok res) :
    off < dat.length := by
  by_cases hlt : off < dat.length
  · exact hlt
  · exfalso
    have hge : off ≥ dat.length := Nat.le_of_not_lt hlt
    rw [tgaWritesAux.eq_def] at hok
    simp only [Nat.succ_ne_zero, if_neg hleft, if_pos hrne, if_pos hge, Except.bind, Except.pure] at hok
    cases hok


theorem tgaWritesAux_ok_cnt {dat : List UInt8} {h : TgaInfo} {fuel left off : Nat} {acc res : List TgaWrite}
    (hrne : h.rle ≠ 0) (hleft : left ≠ 0) (hoff : off < dat.length)
    (hok : tgaWritesAux dat h (fuel + 1) left off acc = Except.ok res) :
    (byteAt dat off &&& 0x7f) + 1 ≤ left := by
  by_cases hc : (byteAt dat off &&& 0x7f) + 1 ≤ left
  · exact hc
  · exfalso
    rw [tgaWritesAux.eq_def] at hok
    simp only [Nat.succ_ne_zero, if_neg hleft, if_pos hrne,
      show ¬ (off ≥ dat.length) from by omega, if_false, pure_bind] at hok
    rw [if_pos (show (byteAt dat off &&& 0x7f) + 1 > left from Nat.lt_of_not_le hc)] at hok
    exact absurd hok (by intro h2; cases h2)

def TgaOkW (dat : List UInt8) (h : TgaInfo) : Nat → Nat → Nat → Prop
  | 0, _, _ => True
  | fuel + 1, left, off =>
      left = 0 ∨
      ((h.rle = 0 ∨ off < dat.length) ∧
       (if h.rle = 0 then 1 else (byteAt dat off &&& 0x7f) + 1) ≤ left ∧
       ((h.rle = 0 ∨ (byteAt dat off &&& 0x80) ≠ 0) →
         (if h.rle = 0 then off else off + 1) + h.channels ≤ dat.length) ∧
       ((h.rle ≠ 0 ∧ (byteAt dat off &&& 0x80) = 0) →
         (∀ i, i < (byteAt dat off &&& 0x7f) + 1 →
           off + 1 + i * h.channels + h.channels ≤ dat.length)) ∧
       TgaOkW dat h fuel
         (left - (if h.rle = 0 then 1 else (byteAt dat off &&& 0x7f) + 1))
         (if h.rle = 0 ∨ (byteAt dat off &&& 0x80) ≠ 0
          then (if h.rle = 0 then off else off + 1) + h.channels
          else off + 1 + (if h.rle = 0 then 1 else (byteAt dat off &&& 0x7f) + 1) * h.channels))

theorem tgaWritesAux_ok_of_TgaOkW (dat : List UInt8) (h : TgaInfo) (fuel left off : Nat) (acc : List TgaWrite)
    (hok : TgaOkW dat h fuel left off) :
    ∃ res, tgaWritesAux dat h fuel left off acc = Except.ok res := by
  induction fuel generalizing left off acc with
  | zero => exact ⟨acc, rfl⟩
  | succ fuel ih =>
    simp only [TgaOkW] at hok
    rcases hok with hl | ⟨hdr, hcnt, hbyte, hraw, hrec⟩
    · exact ⟨acc, by rw [tgaWritesAux.eq_def]; simp only [hl, if_true]; rfl⟩
    · by_cases hrle : h.rle = 0
      · have hb : off + h.channels ≤ dat.length := by
          have := hbyte (Or.inl hrle); simpa [hrle] using this
        have hc1 : 1 ≤ left := by have := hcnt; simpa [hrle] using this
        have hne : left ≠ 0 := by omega
        rw [tgaWritesAux_rle0_pkt dat h fuel left off acc hrle hne hb]
        exact ih (left - 1) (off + h.channels) _ (by simpa [hrle] using hrec)
      · have hoff : off < dat.length := by
          rcases hdr with h0 | hlt
          · omega
          · exact hlt
        have hcnt' : (byteAt dat off &&& 0x7f) + 1 ≤ left := by
          have := hcnt; simpa [hrle] using this
        have hne : left ≠ 0 := by omega
        by_cases hbit : (byteAt dat off &&& 0x80) ≠ 0
        · have hb : off + 1 + h.channels ≤ dat.length := by
            have := hbyte (Or.inr hbit); simpa [hrle] using this
          rw [tgaWritesAux_rle_pkt dat h fuel left off acc hrle hne hoff hcnt' hbit hb]
          exact ih _ (off + 1 + h.channels) _ (by simpa [hrle, hbit, if_true] using hrec)
        · have hbit0 : (byteAt dat off &&& 0x80) = 0 := Classical.not_not.mp hbit
          have hrawb := hraw ⟨by omega, hbit0⟩
          rw [tgaWritesAux_raw_pkt dat h fuel left off acc hrle hne hoff hcnt' hbit0 hrawb]
          exact ih _ (off + 1 + ((byteAt dat off &&& 0x7f) + 1) * h.channels) _
            (by simpa [hrle, hbit0, if_false, if_true, Or.inr] using hrec)

theorem TgaOkW_rle0_dbnd (dat : List UInt8) (h : TgaInfo) (hrle0 : h.rle = 0) :
    ∀ (n off : Nat), TgaOkW dat h n n off →
      ∀ i, i < n → off + i * h.channels + h.channels ≤ dat.length := by
  intro n
  induction n with
  | zero => intro off _ i hi; omega
  | succ n ih =>
    intro off hok i hi
    simp only [TgaOkW] at hok
    rcases hok with hz | ⟨_, _, hbyte, _, hrec⟩
    · omega
    · have hb0 : off + h.channels ≤ dat.length := by
        have := hbyte (Or.inl hrle0); simpa [hrle0] using this
      have hrec' : TgaOkW dat h n n (off + h.channels) := by
        simpa [hrle0] using hrec
      have := ih (off + h.channels) hrec'
      cases i with
      | zero => simpa using hb0
      | succ j =>
        have hi' : j < n := by omega
        have := ih (off + h.channels) hrec' j hi'
        rw [Nat.succ_mul]
        omega


end NANO
