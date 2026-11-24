import NANO.Tga
import NANO.TgaWrites
import NANO.TgaSpec

/-
  Component lemmas for the compressed (rle≠0) loop-1 fuel induction.
-/

namespace NANO
open NANO

/-- `tgaPixelOut` depends only on the channel count: when `ch = 1` only the first
    byte matters; when `ch = 3` or `4` the first three; the fourth is ignored
    unless `ch = 4`.  Used to match the machine's per-packet pixel against the
    spec's `d.getD`-based pixel. -/
theorem tgaPixelOut_ext (ch : Nat) (a b c d b' c' d' : UInt8)
    (hb : ch ≠ 1 → b = b') (hc : ch ≠ 1 → c = c') (hd : ch ≠ 1 → ch ≠ 3 → d = d') :
    tgaPixelOut ch a b c d = tgaPixelOut ch a b' c' d' := by
  by_cases h1 : ch = 1
  · simp [tgaPixelOut, h1]
  · by_cases h3 : ch = 3
    · simp [tgaPixelOut, h1, h3, hb h1, hc h1]
    · by_cases h4 : ch = 4
      · simp [tgaPixelOut, h1, h3, h4, hb h1, hc h1, hd h1 h3]
      · simp [tgaPixelOut, h1, h3, h4]


/-- `tgaPixelOut` agrees when the bytes it actually reads agree: `s1` is read
    only when `1 < ch`, `s2` when `2 < ch`, `s3` when `3 < ch`. -/
theorem tgaPixelOut_congr (ch : Nat) (a b c d b' c' d' : UInt8)
    (hb : 1 < ch → b = b') (hc : 2 < ch → c = c') (hd : 3 < ch → d = d') :
    tgaPixelOut ch a b c d = tgaPixelOut ch a b' c' d' := by
  by_cases e1 : ch = 1
  · simp [tgaPixelOut, e1]
  · by_cases e3 : ch = 3
    · simp [tgaPixelOut, e1, e3, hb (by omega), hc (by omega)]
    · by_cases e4 : ch = 4
      · simp [tgaPixelOut, e1, e3, e4, hb (by omega), hc (by omega), hd (by omega)]
      · simp [tgaPixelOut, e1, e3, e4]

/-- The machine's packet pixel (byteAt/ofNat form, as read by the RLE packet
    prologue) equals the spec's getD form. -/
theorem tgaPixelOut_byteAt_eq (d : List UInt8) (ch o : Nat) :
    tgaPixelOut ch (UInt8.ofNat (byteAt d (o + 1)))
        (UInt8.ofNat (if 1 < ch then byteAt d (o + 2) else 0))
        (UInt8.ofNat (if 2 < ch then byteAt d (o + 3) else 0))
        (UInt8.ofNat (if 3 < ch then byteAt d (o + 4) else 255))
      = tgaPixelOut ch (d.getD (o + 1) 0) (d.getD (o + 2) 0) (d.getD (o + 3) 0) (d.getD (o + 4) 0) := by
  have h1 : UInt8.ofNat (byteAt d (o + 1)) = d.getD (o + 1) 0 := ofNat_byteAt d (o + 1)
  rw [h1]
  refine tgaPixelOut_congr ch _ _ _ _ _ _ _ ?_ ?_ ?_
  · intro e; rw [if_pos e, ofNat_byteAt]
  · intro e; rw [if_pos e, ofNat_byteAt]
  · intro e; rw [if_pos e, ofNat_byteAt]


/-- The machine's raw pixel for index `i` (ofNat/byteAt form) equals the spec's
    getD form. -/
theorem tgaPixelOut_raw_byteAt_eq (d : List UInt8) (ch off i : Nat) :
    tgaPixelOut ch (UInt8.ofNat (byteAt d (off + i * ch)))
        (UInt8.ofNat (byteAt d (off + i * ch + 1)))
        (UInt8.ofNat (byteAt d (off + i * ch + 2)))
        (UInt8.ofNat (byteAt d (off + i * ch + 3)))
      = tgaPixelOut ch (d.getD (off + i * ch) 0) (d.getD (off + i * ch + 1) 0)
          (d.getD (off + i * ch + 2) 0) (d.getD (off + i * ch + 3) 0) := by
  rw [ofNat_byteAt, ofNat_byteAt, ofNat_byteAt, ofNat_byteAt]

end NANO
