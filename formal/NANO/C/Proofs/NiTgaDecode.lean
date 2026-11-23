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

namespace NANO.C.Proofs
open NANO NANO.C

abbrev tgaDecodePre : Stmt :=
  .seq (.set 8 (.load (.int u8) (.field (.var 2) 24)))
  (.seq (.set 9 (.load (.int u8) (.field (.var 2) 25)))
  (.seq (.set 5 (.bin .mul (some u64) (.cast u64 (.load (.int u32) (.field (.var 2) 16)))
                            (.cast u64 (.load (.int u32) (.field (.var 2) 20)))))
  (.seq (.set 7 (.load (.int u64) (.field (.var 2) 8)))
        (.set 6 (.cast u64 (.const (.int i32 0)))))))

theorem ni_tga_decode_preamble (m : Mem) (bd : Nat) (size : Nat) (ob : Nat) (outCap : Nat)
    (obl : List UInt8) (hm : m 3 = some obl) (h32 : obl.length = 32)
    (ro : Bool) (hro : ro = false) (channels rle width height dataOffset : Nat)
    (hw32 : width < 2 ^ 32) (hh32 : height < 2 ^ 32)
    (hl8 : load m (.int u8) (.ptr 3 24) = .ok (.int u8 channels))
    (hl9 : load m (.int u8) (.ptr 3 25) = .ok (.int u8 rle))
    (hl16 : load m (.int u32) (.ptr 3 16) = .ok (.int u32 width))
    (hl20 : load m (.int u32) (.ptr 3 20) = .ok (.int u32 height))
    (hl7 : load m (.int u64) (.ptr 3 8) = .ok (.int u64 dataOffset))
    (hwh : width * height < 2 ^ 64) :
    ExS Gen.prog
      ⟨frameLocals [0, 1, 2, 3, 4] [.ptr bd 0, .int u64 size, .ptr 3 0, .ptr ob 0, .int u64 outCap], m, ro⟩
      tgaDecodePre .normal
      ⟨(frameLocals [0, 1, 2, 3, 4] [.ptr bd 0, .int u64 size, .ptr 3 0, .ptr ob 0, .int u64 outCap]).upd 8 (.int u8 channels)
        |>.upd 9 (.int u8 rle) |>.upd 5 (.int u64 (width * height))
        |>.upd 7 (.int u64 dataOffset) |>.upd 6 (.int u64 0), m, ro⟩ := by
  let s0 : State := ⟨frameLocals [0, 1, 2, 3, 4] [.ptr bd 0, .int u64 size, .ptr 3 0, .ptr ob 0, .int u64 outCap], m, ro⟩
  have l20 : s0.locals 2 = some (.ptr 3 0) := rfl
  have F (st : State) (h2 : st.locals 2 = some (.ptr 3 0)) (hmm : st.mem 3 = some obl)
      (o : Nat) (ho : o ≤ obl.length) : EvE Gen.prog st (.field (.var 2) o) (.ptr 3 (0 + o)) :=
    EvE.field (EvE.var h2) (ptrAddN_ok hmm (by omega))
  have h8 : EvE Gen.prog s0 (.load (.int u8) (.field (.var 2) 24)) (.int u8 channels) :=
    EvE.load (F s0 l20 hm 24 (by omega)) (by simpa using hl8)
  have hs8 : ExS Gen.prog s0 (.set 8 (.load (.int u8) (.field (.var 2) 24))) .normal
      { s0 with locals := s0.locals.upd 8 (.int u8 channels) } := ExS.set h8
  let s1 : State := { s0 with locals := s0.locals.upd 8 (.int u8 channels) }
  have l21 : s1.locals 2 = some (.ptr 3 0) := by
    show (s0.locals.upd 8 (.int u8 channels)) 2 = some (.ptr 3 0)
    simpa [Locals.upd_ne] using l20
  have hm1 : s1.mem 3 = some obl := by simpa using hm
  have h9 : EvE Gen.prog s1 (.load (.int u8) (.field (.var 2) 25)) (.int u8 rle) :=
    EvE.load (F s1 l21 hm1 25 (by omega)) (by simpa using hl9)
  have hs9 : ExS Gen.prog s1 (.set 9 (.load (.int u8) (.field (.var 2) 25))) .normal
      { s1 with locals := s1.locals.upd 9 (.int u8 rle) } := ExS.set h9
  let s2 : State := { s1 with locals := s1.locals.upd 9 (.int u8 rle) }
  have l22 : s2.locals 2 = some (.ptr 3 0) := by
    show (s1.locals.upd 9 (.int u8 rle)) 2 = some (.ptr 3 0)
    simpa [Locals.upd_ne] using l21
  have hm2 : s2.mem 3 = some obl := by simpa using hm
  have h16 : EvE Gen.prog s2 (.load (.int u32) (.field (.var 2) 16)) (.int u32 width) :=
    EvE.load (F s2 l22 hm2 16 (by omega)) (by simpa using hl16)
  have h20 : EvE Gen.prog s2 (.load (.int u32) (.field (.var 2) 20)) (.int u32 height) :=
    EvE.load (F s2 l22 hm2 20 (by omega)) (by simpa using hl20)
  have hs5 : ExS Gen.prog s2 (.set 5 (.bin .mul (some u64) (.cast u64 (.load (.int u32) (.field (.var 2) 16)))
        (.cast u64 (.load (.int u32) (.field (.var 2) 20))))) .normal
      { s2 with locals := s2.locals.upd 5 (.int u64 (width * height)) } :=
    ExS.set (EvE.bin (EvE.cast h16 (u32_u64_cast width hw32)) (EvE.cast h20 (u32_u64_cast height hh32))
      (bin_u64_mul width height hwh))
  let s3 : State := { s2 with locals := s2.locals.upd 5 (.int u64 (width * height)) }
  have l23 : s3.locals 2 = some (.ptr 3 0) := by
    show (s2.locals.upd 5 (.int u64 (width * height))) 2 = some (.ptr 3 0)
    simpa [Locals.upd_ne] using l22
  have hm3 : s3.mem 3 = some obl := by simpa using hm
  have h7 : EvE Gen.prog s3 (.load (.int u64) (.field (.var 2) 8)) (.int u64 dataOffset) :=
    EvE.load (F s3 l23 hm3 8 (by omega)) (by simpa using hl7)
  have hs7 : ExS Gen.prog s3 (.set 7 (.load (.int u64) (.field (.var 2) 8))) .normal
      { s3 with locals := s3.locals.upd 7 (.int u64 dataOffset) } := ExS.set h7
  let s4 : State := { s3 with locals := s3.locals.upd 7 (.int u64 dataOffset) }
  have h6 : EvE Gen.prog s4 (.cast u64 (.const (.int i32 0))) (.int u64 0) :=
    EvE.cast (EvE.const (v := .int i32 0)) (i32_u64_cast 0 (by omega))
  have hs6 : ExS Gen.prog s4 (.set 6 (.cast u64 (.const (.int i32 0)))) .normal
      { s4 with locals := s4.locals.upd 6 (.int u64 0) } := ExS.set h6
  exact ExS.seq hs8 (ExS.seq hs9 (ExS.seq hs5 (ExS.seq hs7 hs6)))

end NANO.C.Proofs
