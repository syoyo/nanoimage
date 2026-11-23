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
import NANO.TgaArith

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

namespace NANO.C.Proofs
open NANO NANO.C

abbrev tgaDstCompute : Stmt :=
  (.seq (.set 21 (.cast u32 (.bin .mod (some u64) (.var 6) (.cast u64 (.load (.int u32) (.field (.var 2) 16))))))
  (.seq (.set 22 (.cast u32 (.bin .div (some u64) (.var 6) (.cast u64 (.load (.int u32) (.field (.var 2) 16))))))
  (.seq (.set 23 (.cond (.bin .ne (some u32) (.cast u32 (.load (.int u8) (.field (.var 2) 27))) (.const (.int u32 0)))
                        (.bin .sub (some u32) (.bin .sub (some u32) (.load (.int u32) (.field (.var 2) 16)) (.const (.int u32 1))) (.var 21))
                        (.var 21)))
  (.seq (.set 24 (.cond (.bin .ne (some u32) (.cast u32 (.load (.int u8) (.field (.var 2) 26))) (.const (.int u32 0)))
                        (.var 22)
                        (.bin .sub (some u32) (.bin .sub (some u32) (.load (.int u32) (.field (.var 2) 20)) (.const (.int u32 1))) (.var 22))))
        (.set 25 (.bin .mul (some u64) (.bin .add (some u64) (.bin .mul (some u64) (.cast u64 (.var 24)) (.cast u64 (.load (.int u32) (.field (.var 2) 16)))) (.cast u64 (.var 23))) (.cast u64 (.var 8))))))))

theorem ni_tga_dst_compute (s : State) (h : TgaInfo) (p : Nat) (obl : List UInt8)
    (hm : s.mem 3 = some obl) (h32 : obl.length = 32)
    (l2 : s.locals 2 = some (.ptr 3 0)) (l6 : s.locals 6 = some (.int u64 p))
    (l8 : s.locals 8 = some (.int u8 h.channels))
    (hl16 : load s.mem (.int u32) (.ptr 3 16) = .ok (.int u32 h.width))
    (hl20 : load s.mem (.int u32) (.ptr 3 20) = .ok (.int u32 h.height))
    (hl26 : load s.mem (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin))
    (hl27 : load s.mem (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin))
    (hw32 : h.width < 2 ^ 32) (hh32 : h.height < 2 ^ 32) (hwpos : 0 < h.width)
    (hpw : p / h.width < 2 ^ 32) (hch : h.channels < 256)
    (hro8 : h.rightOrigin < 256) (hto8 : h.topOrigin < 256) (hp : p < 2 ^ 64)
    (hhpos : 0 < h.height) (hpp : p < h.width * h.height)
    (hmul : tgaDstY h p * h.width < 2 ^ 64)
    (hadd : tgaDstY h p * h.width + tgaDstX h p < 2 ^ 64)
    (hidx : (tgaDstY h p * h.width + tgaDstX h p) * h.channels < 2 ^ 64) :
    ∃ s', ExS Gen.prog s tgaDstCompute .normal s' ∧
      s'.locals 21 = some (.int u32 (p % h.width)) ∧
      s'.locals 22 = some (.int u32 (p / h.width)) ∧
      s'.locals 23 = some (.int u32 (tgaDstX h p)) ∧
      s'.locals 24 = some (.int u32 (tgaDstY h p)) ∧
      s'.locals 25 = some (.int u64 (tgaDstIndex h p)) ∧ s'.mem = s.mem := by
  have hpl : p % h.width < h.width := Nat.mod_lt _ hwpos
  have hqp : p / h.width ≤ p := Nat.div_le_self _ _
  have hpwh : p / h.width < h.height := Nat.div_lt_of_lt_mul hpp
  let s1 : State := { s with locals := s.locals.upd 21 (.int u32 (p % h.width)) }
  let s2 : State := { s1 with locals := s1.locals.upd 22 (.int u32 (p / h.width)) }
  let s3 : State := { s2 with locals := s2.locals.upd 23 (.int u32 (tgaDstX h p)) }
  let s4 : State := { s3 with locals := s3.locals.upd 24 (.int u32 (tgaDstY h p)) }
  let s5 : State := { s4 with locals := s4.locals.upd 25 (.int u64 (tgaDstIndex h p)) }
  have m1 : s1.mem = s.mem := rfl
  have m2 : s2.mem = s.mem := rfl
  have m3 : s3.mem = s.mem := rfl
  have m4 : s4.mem = s.mem := rfl
  have ld : ∀ (st : State), st.locals 2 = some (.ptr 3 0) → st.mem = s.mem →
      ∀ (o : Nat), o ≤ obl.length → ∀ (ty : Ty) (v : Val), load st.mem ty (.ptr 3 o) = .ok v →
      EvE Gen.prog st (.load ty (.field (.var 2) o)) v := by
    intro st h2 hmst o ho ty v hl
    exact EvE.load (EvE.field (EvE.var h2) (ptrAddN_ok (by rw [hmst]; exact hm) (by omega))) (by simpa using hl)
  have l2_1 : s1.locals 2 = some (.ptr 3 0) := by simp [s1, Locals.upd_ne, l2]
  have l2_2 : s2.locals 2 = some (.ptr 3 0) := by simp [s2, Locals.upd_ne, l2_1]
  have l2_3 : s3.locals 2 = some (.ptr 3 0) := by simp [s3, Locals.upd_ne, l2_2]
  have l2_4 : s4.locals 2 = some (.ptr 3 0) := by simp [s4, Locals.upd_ne, l2_3]
  have l6_1 : s1.locals 6 = some (.int u64 p) := by simp [s1, Locals.upd_ne, l6]
  have v21 : s1.locals 21 = some (.int u32 (p % h.width)) := by simp [s1, Locals.upd_same]
  have v21' : s2.locals 21 = some (.int u32 (p % h.width)) := by simp [s2, Locals.upd_ne, v21]
  have v22 : s2.locals 22 = some (.int u32 (p / h.width)) := by simp [s2, Locals.upd_same]
  have v22' : s3.locals 22 = some (.int u32 (p / h.width)) := by simp [s3, Locals.upd_ne, v22]
  have h24s : s4.locals 24 = some (.int u32 (tgaDstY h p)) := by simp [s4, Locals.upd_same]
  have h23s : s3.locals 23 = some (.int u32 (tgaDstX h p)) := by simp [s3, Locals.upd_same]
  have h8s : s4.locals 8 = some (.int u8 h.channels) := by simp [s4, s3, s2, s1, Locals.upd_ne, l8]
  -- set 21
  have h21 : EvE Gen.prog s (.cast u32 (.bin .mod (some u64) (.var 6) (.cast u64 (.load (.int u32) (.field (.var 2) 16))))) (.int u32 (p % h.width)) :=
    EvE.cast (EvE.bin (EvE.var l6) (EvE.cast (ld s l2 rfl 16 (by omega) (.int u32) (.int u32 h.width) hl16) (u32_u64_cast h.width hw32))
      (bin_u64_mod p h.width (by omega) hp)) (u64_u32_trunc_cast (p % h.width) (by omega))
  -- set 22
  have h22 : EvE Gen.prog s1 (.cast u32 (.bin .div (some u64) (.var 6) (.cast u64 (.load (.int u32) (.field (.var 2) 16))))) (.int u32 (p / h.width)) :=
    EvE.cast (EvE.bin (EvE.var l6_1) (EvE.cast (ld s1 l2_1 m1 16 (by omega) (.int u32) (.int u32 h.width) hl16) (u32_u64_cast h.width hw32))
      (bin_u64_div p h.width (by omega))) (u64_u32_trunc_cast (p / h.width) hpw)
  -- set 23
  have hc23 : EvE Gen.prog s2 (.bin .ne (some u32) (.cast u32 (.load (.int u8) (.field (.var 2) 27))) (.const (.int u32 0))) (boolVal (decide (h.rightOrigin ≠ 0))) :=
    EvE.bin (EvE.cast (ld s2 l2_2 m2 27 (by omega) (.int u8) (.int u8 h.rightOrigin) hl27) (u8_u32_cast h.rightOrigin hro8)) (EvE.const (v := .int u32 0)) (bin_u32_ne h.rightOrigin 0)
  have h23i : s2.locals 21 = some (.int u32 (p % h.width)) := v21'
  have h23 : EvE Gen.prog s2 (.cond (.bin .ne (some u32) (.cast u32 (.load (.int u8) (.field (.var 2) 27))) (.const (.int u32 0)))
        (.bin .sub (some u32) (.bin .sub (some u32) (.load (.int u32) (.field (.var 2) 16)) (.const (.int u32 1))) (.var 21)) (.var 21)) (.int u32 (tgaDstX h p)) := by
    rw [tgaDstX]
    by_cases hr : h.rightOrigin ≠ 0
    · rw [if_pos hr]
      refine EvE.cond hc23 (by rw [decide_eq_true hr]; exact truthy_boolVal true) ?_
      exact EvE.bin (EvE.bin (ld s2 l2_2 m2 16 (by omega) (.int u32) (.int u32 h.width) hl16) (EvE.const (v := .int u32 1)) (bin_u32_sub h.width 1 (by omega)))
        (EvE.var h23i) (bin_u32_sub (h.width - 1) (p % h.width) (by omega))
    · rw [if_neg hr]
      refine EvE.cond hc23 (by rw [decide_eq_false hr]; exact truthy_boolVal false) ?_
      exact EvE.var h23i
  -- set 24
  have hc24 : EvE Gen.prog s3 (.bin .ne (some u32) (.cast u32 (.load (.int u8) (.field (.var 2) 26))) (.const (.int u32 0))) (boolVal (decide (h.topOrigin ≠ 0))) :=
    EvE.bin (EvE.cast (ld s3 l2_3 m3 26 (by omega) (.int u8) (.int u8 h.topOrigin) hl26) (u8_u32_cast h.topOrigin hto8)) (EvE.const (v := .int u32 0)) (bin_u32_ne h.topOrigin 0)
  have h24i : s3.locals 22 = some (.int u32 (p / h.width)) := v22'
  have h24 : EvE Gen.prog s3 (.cond (.bin .ne (some u32) (.cast u32 (.load (.int u8) (.field (.var 2) 26))) (.const (.int u32 0)))
        (.var 22) (.bin .sub (some u32) (.bin .sub (some u32) (.load (.int u32) (.field (.var 2) 20)) (.const (.int u32 1))) (.var 22))) (.int u32 (tgaDstY h p)) := by
    rw [tgaDstY]
    by_cases ht : h.topOrigin ≠ 0
    · rw [if_pos ht]
      refine EvE.cond hc24 (by rw [decide_eq_true ht]; exact truthy_boolVal true) ?_
      exact EvE.var h24i
    · rw [if_neg ht]
      refine EvE.cond hc24 (by rw [decide_eq_false ht]; exact truthy_boolVal false) ?_
      exact EvE.bin (EvE.bin (ld s3 l2_3 m3 20 (by omega) (.int u32) (.int u32 h.height) hl20) (EvE.const (v := .int u32 1)) (bin_u32_sub h.height 1 (by omega)))
        (EvE.var h24i) (bin_u32_sub (h.height - 1) (p / h.width) (by omega))
  -- set 25
  have h25 : EvE Gen.prog s4 (.bin .mul (some u64) (.bin .add (some u64) (.bin .mul (some u64) (.cast u64 (.var 24)) (.cast u64 (.load (.int u32) (.field (.var 2) 16)))) (.cast u64 (.var 23))) (.cast u64 (.var 8))) (.int u64 (tgaDstIndex h p)) := by
    rw [tgaDstIndex_eq]
    exact EvE.bin
      (EvE.bin
        (EvE.bin (EvE.cast (EvE.var h24s) (u32_u64_cast (tgaDstY h p) (by have := tgaDstY_lt h p hhpos hpp; omega)))
          (EvE.cast (ld s4 l2_4 m4 16 (by omega) (.int u32) (.int u32 h.width) hl16) (u32_u64_cast h.width hw32))
          (bin_u64_mul (tgaDstY h p) h.width hmul))
        (EvE.cast (EvE.var h23s) (u32_u64_cast (tgaDstX h p) (by have := tgaDstX_lt h p hwpos; omega)))
        (bin_u64_add (tgaDstY h p * h.width) (tgaDstX h p) hadd))
      (EvE.cast (EvE.var h8s) (u8_u64_cast h.channels hch))
      (bin_u64_mul (tgaDstY h p * h.width + tgaDstX h p) h.channels hidx)
  refine ⟨s5, ExS.seq (ExS.set h21) (ExS.seq (ExS.set h22) (ExS.seq (ExS.set h23) (ExS.seq (ExS.set h24) (ExS.set h25)))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  · simp [s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  · simp [s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  · simp [s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  · simp [s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  · rfl

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- The decode's `if (!write_ok) return 12` check: with `wr = 1` it falls through. -/
theorem ni_tga_decode_wr_check (s : State) (l26 : s.locals 26 = some (.int i32 1)) :
    ExS Gen.prog s
      (.ite (.un .lnot i32 (.var 26)) (.ret (some (.const (.int i32 12)))) .skip) .normal s := by
  have hev : EvE Gen.prog s (.un .lnot i32 (.var 26)) (boolVal false) :=
    EvE.un (EvE.var l26) (by simp [evalUn, truthy, boolVal])
  exact ExS.ite hev (truthy_boolVal false) ExS.skip

end NANO.C.Proofs
