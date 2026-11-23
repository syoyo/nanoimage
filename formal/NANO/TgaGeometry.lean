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
