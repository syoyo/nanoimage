/-
  Destination-offset geometry for the TGA decode loop (`tgaDstIndex`).
-/
import NANO.Basic
import NANO.Tga

namespace NANO

def tgaDstX (h : TgaInfo) (p : Nat) : Nat :=
  if h.rightOrigin ≠ 0 then h.width - 1 - p % h.width else p % h.width

def tgaDstY (h : TgaInfo) (p : Nat) : Nat :=
  if h.topOrigin ≠ 0 then p / h.width else h.height - 1 - p / h.width

theorem tgaDstIndex_eq (h : TgaInfo) (p : Nat) :
    tgaDstIndex h p = (tgaDstY h p * h.width + tgaDstX h p) * h.channels := by
  simp only [tgaDstIndex, tgaDstY, tgaDstX]

theorem tgaDstX_lt (h : TgaInfo) (p : Nat) (hw : 0 < h.width) : tgaDstX h p < h.width := by
  have hx := Nat.mod_lt p hw
  simp only [tgaDstX]
  split
  · have : h.width - 1 - p % h.width ≤ h.width - 1 := Nat.sub_le _ _
    omega
  · exact hx

theorem tgaDstY_lt (h : TgaInfo) (p : Nat) (hh : 0 < h.height) (hp : p < h.width * h.height) :
    tgaDstY h p < h.height := by
  have hd : p / h.width < h.height := Nat.div_lt_of_lt_mul hp
  simp only [tgaDstY]
  split
  · exact hd
  · have : h.height - 1 - p / h.width ≤ h.height - 1 := Nat.sub_le _ _
    omega

theorem tgaDstIndex_lt (h : TgaInfo) (p : Nat) (hw : 0 < h.width) (hh : 0 < h.height)
    (hp : p < h.width * h.height) :
    tgaDstIndex h p + h.channels ≤ h.width * h.height * h.channels := by
  rw [tgaDstIndex_eq]
  have hX := tgaDstX_lt h p hw
  have hY := tgaDstY_lt h p hh hp
  have hkey : tgaDstY h p * h.width + tgaDstX h p + 1 ≤ h.width * h.height := by
    have hlt : tgaDstY h p * h.width + tgaDstX h p < h.width * h.height := by
      have hs : tgaDstY h p * h.width + tgaDstX h p < tgaDstY h p * h.width + h.width := by omega
      have hle : (tgaDstY h p + 1) * h.width ≤ h.height * h.width :=
        Nat.mul_le_mul_right h.width (by omega)
      have hle' : tgaDstY h p * h.width + h.width ≤ h.height * h.width := by
        rw [Nat.succ_mul] at hle; exact hle
      have hcomm : h.height * h.width = h.width * h.height := Nat.mul_comm _ _
      omega
    omega
  calc (tgaDstY h p * h.width + tgaDstX h p) * h.channels + h.channels
      = (tgaDstY h p * h.width + tgaDstX h p + 1) * h.channels := by
        simp only [Nat.add_mul, Nat.one_mul]
    _ ≤ (h.width * h.height) * h.channels := Nat.mul_le_mul_right h.channels hkey

end NANO

namespace NANO

theorem tgaDstX_inj (h : TgaInfo) (p q : Nat) (hp : p % h.width < h.width)
    (hq : q % h.width < h.width) (he : tgaDstX h p = tgaDstX h q) :
    p % h.width = q % h.width := by
  simp only [tgaDstX] at he
  split at he
  · omega
  · exact he

theorem tgaDstY_inj (h : TgaInfo) (p q : Nat) (hp : p / h.width < h.height)
    (hq : q / h.width < h.height) (he : tgaDstY h p = tgaDstY h q) :
    p / h.width = q / h.width := by
  simp only [tgaDstY] at he
  split at he
  · exact he
  · omega

theorem tgaDstIndex_inj (h : TgaInfo) (p q : Nat) (hc : 0 < h.channels) (hw : 0 < h.width)
    (hp : p < h.width * h.height) (hq : q < h.width * h.height)
    (he : tgaDstIndex h p = tgaDstIndex h q) : p = q := by
  rw [tgaDstIndex_eq, tgaDstIndex_eq] at he
  have he' : tgaDstY h p * h.width + tgaDstX h p = tgaDstY h q * h.width + tgaDstX h q :=
    Nat.mul_right_cancel hc he
  have hh : 0 < h.height := by
    rcases Nat.eq_zero_or_pos h.height with h0 | h0
    · rw [h0, Nat.mul_zero] at hp; omega
    · exact h0
  have hXp := tgaDstX_lt h p hw
  have hXq := tgaDstX_lt h q hw
  have hYp := tgaDstY_lt h p hh hp
  have hYq := tgaDstY_lt h q hh hq
  have hdiv : ((tgaDstY h p * h.width + tgaDstX h p) / h.width) = tgaDstY h p := by
    rw [Nat.mul_comm (tgaDstY h p) h.width, Nat.mul_add_div hw, Nat.div_eq_of_lt hXp, Nat.add_zero]
  have hdivq : ((tgaDstY h q * h.width + tgaDstX h q) / h.width) = tgaDstY h q := by
    rw [Nat.mul_comm (tgaDstY h q) h.width, Nat.mul_add_div hw, Nat.div_eq_of_lt hXq, Nat.add_zero]
  have hYeq : tgaDstY h p = tgaDstY h q := by rw [← hdiv, he', hdivq]
  have hXeq : tgaDstX h p = tgaDstX h q := by
    have : tgaDstY h q * h.width + tgaDstX h p = tgaDstY h q * h.width + tgaDstX h q := by
      rw [← he', hYeq]
    exact Nat.add_left_cancel this
  have hx := tgaDstX_inj h p q (Nat.mod_lt p hw) (Nat.mod_lt q hw) hXeq
  have hy := tgaDstY_inj h p q (Nat.div_lt_of_lt_mul hp) (Nat.div_lt_of_lt_mul hq) hYeq
  calc p = p / h.width * h.width + p % h.width := (Nat.div_add_mod' p h.width).symm
    _ = q / h.width * h.width + q % h.width := by rw [hy, hx]
    _ = q := Nat.div_add_mod' q h.width

end NANO
