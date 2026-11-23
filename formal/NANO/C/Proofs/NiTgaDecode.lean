/-
  `ni_tga_decode_into` refinement — loop helpers.
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Lemmas
import NANO.Spec
import NANO.Tga
import NANO.TgaWrites
import NANO.TgaGeometry
import NANO.C.Proofs.Core
import NANO.C.Proofs.NiGeometryTail
import NANO.C.Proofs.NiBmpDecode
import NANO.C.Proofs.NiTgaHeader
import NANO.C.Proofs.NiTgaWritePixel

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 4000000

namespace NANO.C.Proofs
open NANO NANO.C

abbrev tgaPix (channels s0 s1 s2 s3 : Nat) : List UInt8 :=
  tgaPixelOut channels (UInt8.ofNat s0) (UInt8.ofNat s1) (UInt8.ofNat s2) (UInt8.ofNat s3)

/-- Statement-level `ni_tga_write_pixel` call: writes one pixel into the output
    buffer at `base`, sets local 26 to 1, keeps other memory. -/
theorem ni_tga_write_pixel_stmt_exs (s : State) (ob : Nat) (obl : List UInt8)
    (hm : s.mem ob = some obl) (base : Nat) (hbase : base < 2 ^ 64) (hlobl : obl.length < 2 ^ 64)
    (channels s0 s1 s2 s3 : Nat)
    (hc : channels = 1 ∨ channels = 3 ∨ channels = 4)
    (hs0 : s0 < 256) (hs1 : s1 < 256) (hs2 : s2 < 256) (hs3 : s3 < 256)
    (hlen : base + (tgaPixelOut channels (UInt8.ofNat s0) (UInt8.ofNat s1) (UInt8.ofNat s2) (UInt8.ofNat s3)).length ≤ obl.length)
    (hro : s.ro = false)
    (l3 : s.locals 3 = some (.ptr ob 0)) (l25 : s.locals 25 = some (.int u64 base))
    (l8 : s.locals 8 = some (.int u8 channels)) (l17 : s.locals 17 = some (.int u8 s0))
    (l18 : s.locals 18 = some (.int u8 s1)) (l19 : s.locals 19 = some (.int u8 s2))
    (l20 : s.locals 20 = some (.int u8 s3)) :
    ExS Gen.prog s (.call (some 26) 22 [(.var 3), (.var 25), (.var 8), (.var 17), (.var 18), (.var 19), (.var 20)]) .normal
      ⟨s.locals.upd 26 (.int i32 1),
       s.mem.upd ob (obl.take base ++ tgaPixelOut channels (UInt8.ofNat s0) (UInt8.ofNat s1) (UInt8.ofNat s2) (UInt8.ofNat s3) ++ obl.drop (base + (tgaPixelOut channels (UInt8.ofNat s0) (UInt8.ofNat s1) (UInt8.ofNat s2) (UInt8.ofNat s3)).length)),
       s.ro⟩ := by
  have hargs : EvArgs Gen.prog s [(.var 3), (.var 25), (.var 8), (.var 17), (.var 18), (.var 19), (.var 20)]
      [.ptr ob 0, .int u64 base, .int u8 channels, .int u8 s0, .int u8 s1, .int u8 s2, .int u8 s3] :=
    EvArgs.cons (EvE.var l3) (EvArgs.cons (EvE.var l25) (EvArgs.cons (EvE.var l8)
      (EvArgs.cons (EvE.var l17) (EvArgs.cons (EvE.var l18) (EvArgs.cons (EvE.var l19)
      (EvArgs.cons (EvE.var l20) EvArgs.nil))))))
  obtain ⟨s', hexs, hmem, hother⟩ :=
    ni_tga_write_pixel_exs s.mem ob obl hm base hbase hlobl channels s0 s1 s2 s3 hc hs0 hs1 hs2 hs3 hlen s.ro hro
  have hblk : s'.mem = s.mem.upd ob (obl.take base ++ tgaPixelOut channels (UInt8.ofNat s0) (UInt8.ofNat s1) (UInt8.ofNat s2) (UInt8.ofNat s3) ++ obl.drop (base + (tgaPixelOut channels (UInt8.ofNat s0) (UInt8.ofNat s1) (UInt8.ofNat s2) (UInt8.ofNat s3)).length)) := by
    funext j
    rw [Mem.upd]
    by_cases hj : j = ob
    · rw [if_pos hj, hj]; exact hmem
    · rw [if_neg hj]; exact hother j hj
  rw [← hblk]
  exact ExS.call_dst (d := 26) (f := 22) hargs
    (show Gen.prog 22 = some Gen.ni_tga_write_pixel from rfl)
    (show Gen.ni_tga_write_pixel.params.length = 7 from rfl) hexs

end NANO.C.Proofs
