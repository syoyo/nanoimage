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

end NANO
