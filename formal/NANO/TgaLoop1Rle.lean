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

end NANO
