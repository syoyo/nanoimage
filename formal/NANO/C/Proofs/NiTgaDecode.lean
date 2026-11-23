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
      s'.locals 25 = some (.int u64 (tgaDstIndex h p)) ∧
      s'.locals 3 = s.locals 3 ∧ s'.locals 8 = s.locals 8 ∧
      s'.locals 17 = s.locals 17 ∧ s'.locals 18 = s.locals 18 ∧
      s'.locals 19 = s.locals 19 ∧ s'.locals 20 = s.locals 20 ∧
      s'.locals 6 = s.locals 6 ∧ s'.locals 7 = s.locals 7 ∧
      s'.mem = s.mem ∧ s'.ro = s.ro := by
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
  refine ⟨s5, ExS.seq (ExS.set h21) (ExS.seq (ExS.set h22) (ExS.seq (ExS.set h23) (ExS.seq (ExS.set h24) (ExS.set h25)))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | rfl
    | simp [s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]

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

namespace NANO.C.Proofs
open NANO NANO.C

abbrev tgaRawRead : Stmt :=
  (.seq (.ite (.bin .gt (some u64) (.bin .add (some u64) (.var 7) (.cast u64 (.var 8))) (.var 1))
              (.ret (some (.const (.int i32 11)))) .skip)
  (.seq (.set 17 (.load (.int u8) (.index (.var 0) (.var 7) 1)))
  (.seq (.ite (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 1)))
              (.set 18 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 1)))) 1))) .skip)
  (.seq (.ite (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 2)))
              (.set 19 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 2)))) 1))) .skip)
  (.seq (.ite (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 3)))
              (.set 20 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 3)))) 1))) .skip)
        (.set 7 (.cast u64 (.bin .add (some u64) (.cast u64 (.var 7)) (.cast u64 (.cast u64 (.var 8)))))))))))

theorem ni_tga_raw_read (s : State) (bd : Nat) (bs : List UInt8) (hm : s.mem bd = some bs)
    (l0 : s.locals 0 = some (.ptr bd 0)) (l1 : s.locals 1 = some (.int u64 bs.length))
    (off channels r1p r2p r3p : Nat) (l7 : s.locals 7 = some (.int u64 off))
    (l8 : s.locals 8 = some (.int u8 channels))
    (l18 : s.locals 18 = some (.int u8 r1p)) (l19 : s.locals 19 = some (.int u8 r2p))
    (l20 : s.locals 20 = some (.int u8 r3p))
    (hch : channels < 256) (hcp : 0 < channels) (hb : off + channels ≤ bs.length)
    (h64 : off + channels < 2 ^ 64) :
    ExS Gen.prog s tgaRawRead .normal
      ⟨s.locals.upd 17 (.int u8 (byteAt bs off))
         |>.upd 18 (if 1 < channels then .int u8 (byteAt bs (off + 1)) else .int u8 r1p)
         |>.upd 19 (if 2 < channels then .int u8 (byteAt bs (off + 2)) else .int u8 r2p)
         |>.upd 20 (if 3 < channels then .int u8 (byteAt bs (off + 3)) else .int u8 r3p)
         |>.upd 7 (.int u64 (off + channels)),
       s.mem, s.ro⟩ := by
  have hoffLt : off < bs.length := by omega
  have hadd : EvE Gen.prog s (.bin .add (some u64) (.var 7) (.cast u64 (.var 8))) (.int u64 (off + channels)) :=
    EvE.bin (EvE.var l7) (EvE.cast (EvE.var l8) (u8_u64_cast channels hch)) (bin_u64_add off channels h64)
  have hgt : EvE Gen.prog s (.bin .gt (some u64) (.bin .add (some u64) (.var 7) (.cast u64 (.var 8))) (.var 1)) (boolVal false) :=
    EvE.bin hadd (EvE.var l1) (by rw [bin_u64_gt, decide_eq_false (by omega)])
  have hguard : ExS Gen.prog s (.ite (.bin .gt (some u64) (.bin .add (some u64) (.var 7) (.cast u64 (.var 8))) (.var 1))
      (.ret (some (.const (.int i32 11)))) .skip) .normal s :=
    ExS.ite hgt (truthy_boolVal false) ExS.skip
  have hb0 : EvE Gen.prog s (.load (.int u8) (.index (.var 0) (.var 7) 1)) (.int u8 (byteAt bs off)) :=
    EvE.load (EvE.index (EvE.var l0) (EvE.var l7) (ptrAddN_ok hm (by omega)))
      (by simpa using load_byte_dyn s.mem bd bs hm off hoffLt)
  let s1 : State := { s with locals := s.locals.upd 17 (.int u8 (byteAt bs off)) }
  have readK : ∀ (k : Nat) (hk : 0 < k) (hkc : k < channels) (st : State)
      (l0' : st.locals 0 = some (.ptr bd 0)) (lik : st.locals 7 = some (.int u64 off))
      (hmm : st.mem = s.mem),
      EvE Gen.prog st (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 k)))) 1)) (.int u8 (byteAt bs (off + k))) := by
    intro k hk hkc st l0' lik hmm
    have hbs : st.mem bd = some bs := by rw [hmm]; exact hm
    have hok : 0 + (off + k) * 1 ≤ bs.length := by omega
    have hk0 : EvE Gen.prog st (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 k)))) (.int u64 (off + k)) :=
      EvE.bin (EvE.var lik) (EvE.cast (EvE.const (v := .int u32 k)) (u32_u64_cast k (by omega)))
        (bin_u64_add off k (by omega))
    exact EvE.load (EvE.index (EvE.var l0') hk0 (ptrAddN_ok hbs hok))
      (by simpa using load_byte_dyn st.mem bd bs hbs (off + k) (by omega))
  have l7_1 : s1.locals 7 = some (.int u64 off) := by simp [s1, Locals.upd_ne, l7]
  have l8_1 : s1.locals 8 = some (.int u8 channels) := by simp [s1, Locals.upd_ne, l8]
  have cond1 : EvE Gen.prog s1 (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 1))) (boolVal (decide (channels > 1))) :=
    EvE.bin (EvE.cast (EvE.var l8_1) (u8_u32_cast channels hch)) (EvE.const (v := .int u32 1)) (bin_u32_gt channels 1)
  let s2 : State := { s1 with locals := s1.locals.upd 18 (if 1 < channels then .int u8 (byteAt bs (off + 1)) else .int u8 r1p) }
  have h18 : ExS Gen.prog s1 (.ite (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 1)))
        (.set 18 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 1)))) 1))) .skip) .normal s2 := by
    by_cases hc1 : 1 < channels
    · have hv : EvE Gen.prog s1 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 1)))) 1)) (.int u8 (byteAt bs (off + 1))) :=
        readK 1 (by omega) hc1 s1 (by simp [s1, Locals.upd_ne, l0]) l7_1 rfl
      have heq : s2 = { s1 with locals := s1.locals.upd 18 (.int u8 (byteAt bs (off + 1))) } := by simp [s2, if_pos hc1]
      rw [heq]
      refine ExS.ite (bc := true) cond1 (by rw [decide_eq_true hc1]; exact truthy_boolVal true) ?_
      exact ExS.set (i := 18) hv
    · have l18_1 : s1.locals 18 = some (.int u8 r1p) := by simp [s1, Locals.upd_ne, l18]
      have heq : s2 = s1 := by simp [s2, if_neg hc1, Locals.upd_of_eq s1.locals 18 (.int u8 r1p) l18_1]
      rw [heq]
      refine ExS.ite (bc := false) cond1 (by rw [decide_eq_false hc1]; exact truthy_boolVal false) ?_
      exact ExS.skip
  have l7_2 : s2.locals 7 = some (.int u64 off) := by simp [s2, Locals.upd_ne, l7_1]
  have l8_2 : s2.locals 8 = some (.int u8 channels) := by simp [s2, Locals.upd_ne, l8_1]
  have l19_2 : s2.locals 19 = some (.int u8 r2p) := by simp [s2, s1, Locals.upd_ne, l19]
  have l20_2 : s2.locals 20 = some (.int u8 r3p) := by simp [s2, s1, Locals.upd_ne, l20]
  have cond2 : EvE Gen.prog s2 (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 2))) (boolVal (decide (channels > 2))) :=
    EvE.bin (EvE.cast (EvE.var l8_2) (u8_u32_cast channels hch)) (EvE.const (v := .int u32 2)) (bin_u32_gt channels 2)
  let s3 : State := { s2 with locals := s2.locals.upd 19 (if 2 < channels then .int u8 (byteAt bs (off + 2)) else .int u8 r2p) }
  have h19 : ExS Gen.prog s2 (.ite (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 2)))
        (.set 19 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 2)))) 1))) .skip) .normal s3 := by
    by_cases hc2 : 2 < channels
    · have hv : EvE Gen.prog s2 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 2)))) 1)) (.int u8 (byteAt bs (off + 2))) :=
        readK 2 (by omega) hc2 s2 (by simp [s2, s1, Locals.upd_ne, l0]) l7_2 rfl
      have heq : s3 = { s2 with locals := s2.locals.upd 19 (.int u8 (byteAt bs (off + 2))) } := by simp [s3, if_pos hc2]
      rw [heq]
      refine ExS.ite (bc := true) cond2 (by rw [decide_eq_true hc2]; exact truthy_boolVal true) ?_
      exact ExS.set (i := 19) hv
    · have l19_1 : s2.locals 19 = some (.int u8 r2p) := l19_2
      have heq : s3 = s2 := by simp [s3, if_neg hc2, Locals.upd_of_eq s2.locals 19 (.int u8 r2p) l19_1]
      rw [heq]
      refine ExS.ite (bc := false) cond2 (by rw [decide_eq_false hc2]; exact truthy_boolVal false) ?_
      exact ExS.skip
  have l7_3 : s3.locals 7 = some (.int u64 off) := by simp [s3, Locals.upd_ne, l7_2]
  have l8_3 : s3.locals 8 = some (.int u8 channels) := by simp [s3, Locals.upd_ne, l8_2]
  have l20_3 : s3.locals 20 = some (.int u8 r3p) := by simp [s3, s2, s1, Locals.upd_ne, l20]
  have cond3 : EvE Gen.prog s3 (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 3))) (boolVal (decide (channels > 3))) :=
    EvE.bin (EvE.cast (EvE.var l8_3) (u8_u32_cast channels hch)) (EvE.const (v := .int u32 3)) (bin_u32_gt channels 3)
  let s4 : State := { s3 with locals := s3.locals.upd 20 (if 3 < channels then .int u8 (byteAt bs (off + 3)) else .int u8 r3p) }
  have h20 : ExS Gen.prog s3 (.ite (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 3)))
        (.set 20 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 3)))) 1))) .skip) .normal s4 := by
    by_cases hc3 : 3 < channels
    · have hv : EvE Gen.prog s3 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 3)))) 1)) (.int u8 (byteAt bs (off + 3))) :=
        readK 3 (by omega) hc3 s3 (by simp [s3, s2, s1, Locals.upd_ne, l0]) l7_3 rfl
      have heq : s4 = { s3 with locals := s3.locals.upd 20 (.int u8 (byteAt bs (off + 3))) } := by simp [s4, if_pos hc3]
      rw [heq]
      refine ExS.ite (bc := true) cond3 (by rw [decide_eq_true hc3]; exact truthy_boolVal true) ?_
      exact ExS.set (i := 20) hv
    · have l20_3' : s3.locals 20 = some (.int u8 r3p) := l20_3
      have heq : s4 = s3 := by simp [s4, if_neg hc3, Locals.upd_of_eq s3.locals 20 (.int u8 r3p) l20_3']
      rw [heq]
      refine ExS.ite (bc := false) cond3 (by rw [decide_eq_false hc3]; exact truthy_boolVal false) ?_
      exact ExS.skip
  have l7_4 : s4.locals 7 = some (.int u64 off) := by simp [s4, Locals.upd_ne, l7_3]
  have l8_4 : s4.locals 8 = some (.int u8 channels) := by simp [s4, Locals.upd_ne, l8_3]
  have h7 : EvE Gen.prog s4 (.cast u64 (.bin .add (some u64) (.cast u64 (.var 7)) (.cast u64 (.cast u64 (.var 8))))) (.int u64 (off + channels)) := by
    have e7 : EvE Gen.prog s4 (.cast u64 (.var 7)) (.int u64 off) := EvE.cast (EvE.var l7_4) (u64_u64_cast off (by omega))
    have e8 : EvE Gen.prog s4 (.cast u64 (.cast u64 (.var 8))) (.int u64 channels) :=
      EvE.cast (EvE.cast (EvE.var l8_4) (u8_u64_cast channels hch)) (u64_u64_cast channels (by omega))
    exact EvE.cast (EvE.bin e7 e8 (bin_u64_add off channels h64)) (u64_u64_cast (off + channels) h64)
  have hset7 : ExS Gen.prog s4 (.set 7 (.cast u64 (.bin .add (some u64) (.cast u64 (.var 7)) (.cast u64 (.cast u64 (.var 8)))))) .normal { s4 with locals := s4.locals.upd 7 (.int u64 (off + channels)) } := ExS.set h7
  have hcomp := ExS.seq hguard (ExS.seq (ExS.set hb0) (ExS.seq h18 (ExS.seq h19 (ExS.seq h20 hset7))))
  simpa [tgaRawRead, s4, s3, s2, s1] using hcomp

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- RLE-clear raw-packet test: `rle ≠ 0 ∧ (header & 0x80) = 0`. -/
abbrev tgaRawCond : Expr :=
  .land (.bin .ne (some u32) (.cast u32 (.var 9)) (.const (.int u32 0)))
        (.bin .eq (some u32) (.bin .band (some u32) (.cast u32 (.var 11)) (.const (.int u32 128))) (.const (.int u32 0)))

abbrev tgaCall : Stmt :=
  .call (some 26) 22 [(.var 3), (.var 25), (.var 8), (.var 17), (.var 18), (.var 19), (.var 20)]

abbrev tgaWrCheck : Stmt :=
  .ite (.un .lnot i32 (.var 26)) (.ret (some (.const (.int i32 12)))) .skip

abbrev tgaPixelInc : Stmt :=
  .set 6 (.cast u64 (.bin .add (some u64) (.cast u64 (.var 6)) (.cast u64 (.cast u64 (.const (.int u32 1))))))

abbrev tgaPixelBody : Stmt :=
  .seq (.set 17 (.var 12))
  (.seq (.set 18 (.var 13))
  (.seq (.set 19 (.var 14))
  (.seq (.set 20 (.var 15))
  (.seq (.ite tgaRawCond tgaRawRead .skip)
  (.seq tgaDstCompute
  (.seq tgaCall
  (.seq tgaWrCheck tgaPixelInc)))))))

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem ni_tga_pixel_step_rle (s : State) (h : TgaInfo) (p : Nat) (ob : Nat) (obl : List UInt8)
    (hmob : s.mem ob = some obl) (hlob : obl.length < 2 ^ 64) (hro : s.ro = false) (hob3 : ob ≠ 3)
    (info : List UInt8) (hinfo : s.mem 3 = some info) (h32 : info.length = 32)
    (l2 : s.locals 2 = some (.ptr 3 0)) (l3 : s.locals 3 = some (.ptr ob 0))
    (l6 : s.locals 6 = some (.int u64 p)) (l8 : s.locals 8 = some (.int u8 h.channels))
    (b0 b1 b2 b3 : Nat) (l12 : s.locals 12 = some (.int u8 b0)) (l13 : s.locals 13 = some (.int u8 b1))
    (l14 : s.locals 14 = some (.int u8 b2)) (l15 : s.locals 15 = some (.int u8 b3))
    (rle hdr : Nat) (l9 : s.locals 9 = some (.int u8 rle)) (l11 : s.locals 11 = some (.int u8 hdr))
    (hraw : rle = 0 ∨ (hdr &&& 128) ≠ 0) (hrle8 : rle < 256) (hhdr8 : hdr < 256)
    (hl16 : load s.mem (.int u32) (.ptr 3 16) = .ok (.int u32 h.width))
    (hl20 : load s.mem (.int u32) (.ptr 3 20) = .ok (.int u32 h.height))
    (hl26 : load s.mem (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin))
    (hl27 : load s.mem (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin))
    (hw32 : h.width < 2 ^ 32) (hh32 : h.height < 2 ^ 32) (hwpos : 0 < h.width) (hhpos : 0 < h.height)
    (hpw : p / h.width < 2 ^ 32) (hch : h.channels < 256) (hro8 : h.rightOrigin < 256) (hto8 : h.topOrigin < 256)
    (hp : p < 2 ^ 64) (hpp : p < h.width * h.height) (hwh64 : h.width * h.height < 2 ^ 64)
    (hmul : tgaDstY h p * h.width < 2 ^ 64) (hadd : tgaDstY h p * h.width + tgaDstX h p < 2 ^ 64)
    (hidx : (tgaDstY h p * h.width + tgaDstX h p) * h.channels < 2 ^ 64)
    (hc : h.channels = 1 ∨ h.channels = 3 ∨ h.channels = 4)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hwb : tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)).length ≤ obl.length) :
    ∃ s', ExS Gen.prog s tgaPixelBody .normal s' ∧
      s'.locals 6 = some (.int u64 (p + 1)) ∧
      s'.mem ob = some (obl.take (tgaDstIndex h p) ++ tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3) ++ obl.drop (tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)).length)) ∧
      s'.mem 3 = some info := by
  let s1 : State := { s with locals := s.locals.upd 17 (.int u8 b0) }
  let s2 : State := { s1 with locals := s1.locals.upd 18 (.int u8 b1) }
  let s3 : State := { s2 with locals := s2.locals.upd 19 (.int u8 b2) }
  let s4 : State := { s3 with locals := s3.locals.upd 20 (.int u8 b3) }
  have e17 : ExS Gen.prog s (.set 17 (.var 12)) .normal s1 := ExS.set (EvE.var l12)
  have l13_1 : s1.locals 13 = some (.int u8 b1) := by simp [s1, Locals.upd_ne, l13]
  have e18 : ExS Gen.prog s1 (.set 18 (.var 13)) .normal s2 := ExS.set (EvE.var l13_1)
  have l14_2 : s2.locals 14 = some (.int u8 b2) := by simp [s2, s1, Locals.upd_ne, l14]
  have e19 : ExS Gen.prog s2 (.set 19 (.var 14)) .normal s3 := ExS.set (EvE.var l14_2)
  have l15_3 : s3.locals 15 = some (.int u8 b3) := by simp [s3, s2, s1, Locals.upd_ne, l15]
  have e20 : ExS Gen.prog s3 (.set 20 (.var 15)) .normal s4 := ExS.set (EvE.var l15_3)
  have l9_4 : s4.locals 9 = some (.int u8 rle) := by simp [s4, s3, s2, s1, Locals.upd_ne, l9]
  have l11_4 : s4.locals 11 = some (.int u8 hdr) := by simp [s4, s3, s2, s1, Locals.upd_ne, l11]
  have evA : EvE Gen.prog s4 (.bin .ne (some u32) (.cast u32 (.var 9)) (.const (.int u32 0))) (boolVal (decide (rle ≠ 0))) :=
    EvE.bin (EvE.cast (EvE.var l9_4) (u8_u32_cast rle hrle8)) (EvE.const (v := .int u32 0)) (bin_u32_ne rle 0)
  have evB : EvE Gen.prog s4 (.bin .eq (some u32) (.bin .band (some u32) (.cast u32 (.var 11)) (.const (.int u32 128))) (.const (.int u32 0))) (boolVal (decide ((hdr &&& 128) = 0))) :=
    EvE.bin (EvE.bin (EvE.cast (EvE.var l11_4) (u8_u32_cast hdr hhdr8)) (EvE.const (v := .int u32 128)) (bin_u32_band hdr 128))
      (EvE.const (v := .int u32 0)) (bin_u32_eq (hdr &&& 128) 0)
  have hcond4 : EvE Gen.prog s4 tgaRawCond (boolVal false) := by
    have htT : truthy (boolVal (decide (rle ≠ 0))) = .ok (decide (rle ≠ 0)) := truthy_boolVal _
    rcases hraw with hr0 | hbn
    · have haf : truthy (boolVal (decide (rle ≠ 0))) = .ok false := by
        rw [truthy_boolVal, show decide (rle ≠ 0) = false from decide_eq_false (by omega)]
      exact EvE.land_false evA haf
    · have hb : truthy (boolVal (decide ((hdr &&& 128) = 0))) = .ok false := by
        rw [truthy_boolVal, decide_eq_false hbn]
      by_cases hrle : rle ≠ 0
      · have ht : truthy (boolVal (decide (rle ≠ 0))) = .ok true := by
          rw [truthy_boolVal, decide_eq_true hrle]
        exact EvE.land_true evA ht evB hb
      · have haf : truthy (boolVal (decide (rle ≠ 0))) = .ok false := by
          rw [truthy_boolVal, decide_eq_false hrle]
        exact EvE.land_false evA haf
  have hskip : ExS Gen.prog s4 (.ite tgaRawCond tgaRawRead .skip) .normal s4 :=
    ExS.ite hcond4 (truthy_boolVal false) ExS.skip
  have l2_4 : s4.locals 2 = some (.ptr 3 0) := by simp [s4, s3, s2, s1, Locals.upd_ne, l2]
  have l6_4 : s4.locals 6 = some (.int u64 p) := by simp [s4, s3, s2, s1, Locals.upd_ne, l6]
  have l8_4 : s4.locals 8 = some (.int u8 h.channels) := by simp [s4, s3, s2, s1, Locals.upd_ne, l8]
  have l3_4 : s4.locals 3 = some (.ptr ob 0) := by simp [s4, s3, s2, s1, Locals.upd_ne, l3]
  have l17_4 : s4.locals 17 = some (.int u8 b0) := by simp [s4, s3, s2, s1, Locals.upd_same, Locals.upd_ne]
  have l18_4 : s4.locals 18 = some (.int u8 b1) := by simp [s4, s3, s2, s1, Locals.upd_same, Locals.upd_ne]
  have l19_4 : s4.locals 19 = some (.int u8 b2) := by simp [s4, s3, s2, s1, Locals.upd_same, Locals.upd_ne]
  have l20_4 : s4.locals 20 = some (.int u8 b3) := by simp [s4, s3, s2, s1, Locals.upd_same, Locals.upd_ne]
  have m4 : s4.mem = s.mem := rfl
  obtain ⟨s5, hdst, h21, h22, h23, h24, h25, h3d, h8d, h17d, h18d, h19d, h20d, h6d, h7d, hm5, hro5⟩ :=
    ni_tga_dst_compute s4 h p info (by rw [m4]; exact hinfo) h32 l2_4 l6_4 l8_4
      (by rw [m4]; exact hl16) (by rw [m4]; exact hl20) (by rw [m4]; exact hl26) (by rw [m4]; exact hl27)
      hw32 hh32 hwpos hpw hch hro8 hto8 hp hhpos hpp hmul hadd hidx
  have l3_5 : s5.locals 3 = some (.ptr ob 0) := by rw [h3d]; exact l3_4
  have l8_5 : s5.locals 8 = some (.int u8 h.channels) := by rw [h8d]; exact l8_4
  have l17_5 : s5.locals 17 = some (.int u8 b0) := by rw [h17d]; exact l17_4
  have l18_5 : s5.locals 18 = some (.int u8 b1) := by rw [h18d]; exact l18_4
  have l19_5 : s5.locals 19 = some (.int u8 b2) := by rw [h19d]; exact l19_4
  have l20_5 : s5.locals 20 = some (.int u8 b3) := by rw [h20d]; exact l20_4
  have hmob5 : s5.mem ob = some obl := by rw [hm5]; exact hmob
  have hro5' : s5.ro = false := by rw [hro5]; exact hro
  have hcall : ExS Gen.prog s5 tgaCall .normal
      ⟨s5.locals.upd 26 (.int i32 1), s5.mem.upd ob (obl.take (tgaDstIndex h p) ++ tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3) ++ obl.drop (tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)).length)), s5.ro⟩ :=
    ni_tga_write_pixel_stmt_exs s5 ob obl hmob5 (tgaDstIndex h p) (by rw [tgaDstIndex_eq]; exact hidx) hlob
      h.channels b0 b1 b2 b3 hc hb0 hb1 hb2 hb3 hwb hro5' l3_5 h25 l8_5 l17_5 l18_5 l19_5 l20_5
  let s6 : State := ⟨s5.locals.upd 26 (.int i32 1), s5.mem.upd ob (obl.take (tgaDstIndex h p) ++ tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3) ++ obl.drop (tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)).length)), s5.ro⟩
  have hwr : ExS Gen.prog s6 tgaWrCheck .normal s6 := ni_tga_decode_wr_check s6 rfl
  -- pixel++
  have l6_6 : s6.locals 6 = some (.int u64 p) := by
    show (s5.locals.upd 26 (.int i32 1)) 6 = some (.int u64 p)
    rw [show (s5.locals.upd 26 (.int i32 1)) 6 = s5.locals 6 from by simp [Locals.upd_ne]]
    rw [h6d]; exact l6_4
  have hp1 : p + 1 < 2 ^ 64 := by omega
  have e6 : EvE Gen.prog s6 (.cast u64 (.var 6)) (.int u64 p) := EvE.cast (EvE.var l6_6) (u64_u64_cast p hp)
  have e1 : EvE Gen.prog s6 (.cast u64 (.cast u64 (.const (.int u32 1)))) (.int u64 1) :=
    EvE.cast (EvE.cast (EvE.const (v := .int u32 1)) (u32_u64_cast 1 (by omega))) (u64_u64_cast 1 (by omega))
  have einc : EvE Gen.prog s6 (.cast u64 (.bin .add (some u64) (.cast u64 (.var 6)) (.cast u64 (.cast u64 (.const (.int u32 1)))))) (.int u64 (p + 1)) :=
    EvE.cast (EvE.bin e6 e1 (bin_u64_add p 1 hp1)) (u64_u64_cast (p + 1) hp1)
  let s7 : State := { s6 with locals := s6.locals.upd 6 (.int u64 (p + 1)) }
  have hinc : ExS Gen.prog s6 tgaPixelInc .normal s7 := ExS.set einc
  refine ⟨s7, ?_, ?_, ?_, ?_⟩
  · -- compose
    exact ExS.seq e17 (ExS.seq e18 (ExS.seq e19 (ExS.seq e20 (ExS.seq hskip (ExS.seq hdst (ExS.seq hcall (ExS.seq hwr hinc)))))))
  · show s7.locals 6 = some (.int u64 (p + 1))
    simp [s7, Locals.upd_same]
  · show s7.mem ob = some (obl.take (tgaDstIndex h p) ++ tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3) ++ obl.drop (tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)).length))
    show (s6.mem) ob = _
    show (s5.mem.upd ob _) ob = _
    rw [Mem.upd_same]
  · show s7.mem 3 = some info
    show (s5.mem.upd ob _) 3 = some info
    rw [show (s5.mem.upd ob _) 3 = s5.mem 3 from by rw [Mem.upd_ne (h := by omega)]]
    rw [hm5]; exact hinfo

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- The raw-read pixel bytes (unread channels keep their preset) equal the
    canonical `tgaPixelOut` of the four data bytes, for `channels ∈ {1,3,4}`. -/
theorem tgaPixelOut_raw (channels b1 b2 b3 d0 d1 d2 d3 : Nat)
    (hc : channels = 1 ∨ channels = 3 ∨ channels = 4) :
    tgaPixelOut channels (UInt8.ofNat d0)
        (UInt8.ofNat (if 1 < channels then d1 else b1))
        (UInt8.ofNat (if 2 < channels then d2 else b2))
        (UInt8.ofNat (if 3 < channels then d3 else b3)) =
      tgaPixelOut channels (UInt8.ofNat d0) (UInt8.ofNat d1) (UInt8.ofNat d2) (UInt8.ofNat d3) := by
  rcases hc with rfl | rfl | rfl <;> simp [tgaPixelOut]

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- The dst-compute + write-pixel + wr-check + pixel++ tail, given the pixel
    bytes already in locals 17-20. -/
theorem ni_tga_pixel_suffix (s : State) (h : TgaInfo) (p : Nat) (ob : Nat) (obl : List UInt8)
    (hmob : s.mem ob = some obl) (hlob : obl.length < 2 ^ 64) (hro : s.ro = false) (hob3 : ob ≠ 3)
    (info : List UInt8) (hinfo : s.mem 3 = some info) (h32 : info.length = 32)
    (l2 : s.locals 2 = some (.ptr 3 0)) (l3 : s.locals 3 = some (.ptr ob 0))
    (l6 : s.locals 6 = some (.int u64 p)) (l8 : s.locals 8 = some (.int u8 h.channels))
    (r0v r1v r2v r3v : Nat)
    (l17 : s.locals 17 = some (.int u8 r0v)) (l18 : s.locals 18 = some (.int u8 r1v))
    (l19 : s.locals 19 = some (.int u8 r2v)) (l20 : s.locals 20 = some (.int u8 r3v))
    (hl16 : load s.mem (.int u32) (.ptr 3 16) = .ok (.int u32 h.width))
    (hl20 : load s.mem (.int u32) (.ptr 3 20) = .ok (.int u32 h.height))
    (hl26 : load s.mem (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin))
    (hl27 : load s.mem (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin))
    (hw32 : h.width < 2 ^ 32) (hh32 : h.height < 2 ^ 32) (hwpos : 0 < h.width) (hhpos : 0 < h.height)
    (hpw : p / h.width < 2 ^ 32) (hch : h.channels < 256) (hro8 : h.rightOrigin < 256) (hto8 : h.topOrigin < 256)
    (hp : p < 2 ^ 64) (hpp : p < h.width * h.height) (hwh64 : h.width * h.height < 2 ^ 64)
    (hmul : tgaDstY h p * h.width < 2 ^ 64) (hadd : tgaDstY h p * h.width + tgaDstX h p < 2 ^ 64)
    (hidx : (tgaDstY h p * h.width + tgaDstX h p) * h.channels < 2 ^ 64)
    (hc : h.channels = 1 ∨ h.channels = 3 ∨ h.channels = 4)
    (hr0 : r0v < 256) (hr1 : r1v < 256) (hr2 : r2v < 256) (hr3 : r3v < 256)
    (hwb : tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat r0v) (UInt8.ofNat r1v) (UInt8.ofNat r2v) (UInt8.ofNat r3v)).length ≤ obl.length) :
    ∃ s', ExS Gen.prog s (.seq tgaDstCompute (.seq tgaCall (.seq tgaWrCheck tgaPixelInc))) .normal s' ∧
      s'.locals 6 = some (.int u64 (p + 1)) ∧
      s'.mem ob = some (obl.take (tgaDstIndex h p) ++ tgaPixelOut h.channels (UInt8.ofNat r0v) (UInt8.ofNat r1v) (UInt8.ofNat r2v) (UInt8.ofNat r3v) ++ obl.drop (tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat r0v) (UInt8.ofNat r1v) (UInt8.ofNat r2v) (UInt8.ofNat r3v)).length)) ∧
      s'.mem 3 = some info := by
  obtain ⟨s5, hdst, h21, h22, h23, h24, h25, h3d, h8d, h17d, h18d, h19d, h20d, h6d, h7d, hm5, hro5⟩ :=
    ni_tga_dst_compute s h p info hinfo h32 l2 l6 l8 hl16 hl20 hl26 hl27
      hw32 hh32 hwpos hpw hch hro8 hto8 hp hhpos hpp hmul hadd hidx
  have l3_5 : s5.locals 3 = some (.ptr ob 0) := by rw [h3d]; exact l3
  have l8_5 : s5.locals 8 = some (.int u8 h.channels) := by rw [h8d]; exact l8
  have l17_5 : s5.locals 17 = some (.int u8 r0v) := by rw [h17d]; exact l17
  have l18_5 : s5.locals 18 = some (.int u8 r1v) := by rw [h18d]; exact l18
  have l19_5 : s5.locals 19 = some (.int u8 r2v) := by rw [h19d]; exact l19
  have l20_5 : s5.locals 20 = some (.int u8 r3v) := by rw [h20d]; exact l20
  have hmob5 : s5.mem ob = some obl := by rw [hm5]; exact hmob
  have hro5' : s5.ro = false := by rw [hro5]; exact hro
  have hcall : ExS Gen.prog s5 tgaCall .normal
      ⟨s5.locals.upd 26 (.int i32 1), s5.mem.upd ob (obl.take (tgaDstIndex h p) ++ tgaPixelOut h.channels (UInt8.ofNat r0v) (UInt8.ofNat r1v) (UInt8.ofNat r2v) (UInt8.ofNat r3v) ++ obl.drop (tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat r0v) (UInt8.ofNat r1v) (UInt8.ofNat r2v) (UInt8.ofNat r3v)).length)), s5.ro⟩ :=
    ni_tga_write_pixel_stmt_exs s5 ob obl hmob5 (tgaDstIndex h p) (by rw [tgaDstIndex_eq]; exact hidx) hlob
      h.channels r0v r1v r2v r3v hc hr0 hr1 hr2 hr3 hwb hro5' l3_5 h25 l8_5 l17_5 l18_5 l19_5 l20_5
  let s6 : State := ⟨s5.locals.upd 26 (.int i32 1), s5.mem.upd ob (obl.take (tgaDstIndex h p) ++ tgaPixelOut h.channels (UInt8.ofNat r0v) (UInt8.ofNat r1v) (UInt8.ofNat r2v) (UInt8.ofNat r3v) ++ obl.drop (tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat r0v) (UInt8.ofNat r1v) (UInt8.ofNat r2v) (UInt8.ofNat r3v)).length)), s5.ro⟩
  have hwr : ExS Gen.prog s6 tgaWrCheck .normal s6 := ni_tga_decode_wr_check s6 rfl
  have l6_6 : s6.locals 6 = some (.int u64 p) := by
    show (s5.locals.upd 26 (.int i32 1)) 6 = some (.int u64 p)
    rw [show (s5.locals.upd 26 (.int i32 1)) 6 = s5.locals 6 from by simp [Locals.upd_ne]]
    rw [h6d]; exact l6
  have hp1 : p + 1 < 2 ^ 64 := by omega
  have e6 : EvE Gen.prog s6 (.cast u64 (.var 6)) (.int u64 p) := EvE.cast (EvE.var l6_6) (u64_u64_cast p hp)
  have e1 : EvE Gen.prog s6 (.cast u64 (.cast u64 (.const (.int u32 1)))) (.int u64 1) :=
    EvE.cast (EvE.cast (EvE.const (v := .int u32 1)) (u32_u64_cast 1 (by omega))) (u64_u64_cast 1 (by omega))
  have einc : EvE Gen.prog s6 (.cast u64 (.bin .add (some u64) (.cast u64 (.var 6)) (.cast u64 (.cast u64 (.const (.int u32 1)))))) (.int u64 (p + 1)) :=
    EvE.cast (EvE.bin e6 e1 (bin_u64_add p 1 hp1)) (u64_u64_cast (p + 1) hp1)
  let s7 : State := { s6 with locals := s6.locals.upd 6 (.int u64 (p + 1)) }
  have hinc : ExS Gen.prog s6 tgaPixelInc .normal s7 := ExS.set einc
  refine ⟨s7, ExS.seq hdst (ExS.seq hcall (ExS.seq hwr hinc)), ?_, ?_, ?_⟩
  · show s7.locals 6 = some (.int u64 (p + 1))
    simp [s7, Locals.upd_same]
  · show s7.mem ob = some (obl.take (tgaDstIndex h p) ++ tgaPixelOut h.channels (UInt8.ofNat r0v) (UInt8.ofNat r1v) (UInt8.ofNat r2v) (UInt8.ofNat r3v) ++ obl.drop (tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat r0v) (UInt8.ofNat r1v) (UInt8.ofNat r2v) (UInt8.ofNat r3v)).length))
    show (s6.mem) ob = _
    show (s5.mem.upd ob _) ob = _
    rw [Mem.upd_same]
  · show s7.mem 3 = some info
    show (s5.mem.upd ob _) 3 = some info
    rw [show (s5.mem.upd ob _) 3 = s5.mem 3 from by rw [Mem.upd_ne (h := by omega)]]
    rw [hm5]; exact hinfo

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem ni_tga_pixel_step_raw (s : State) (h : TgaInfo) (p : Nat) (ob bd : Nat) (obl dat : List UInt8)
    (hmob : s.mem ob = some obl) (hlob : obl.length < 2 ^ 64) (hro : s.ro = false)
    (hob3 : ob ≠ 3) (hbd3 : bd ≠ 3)
    (hmbd : s.mem bd = some dat)
    (info : List UInt8) (hinfo : s.mem 3 = some info) (h32 : info.length = 32)
    (l0 : s.locals 0 = some (.ptr bd 0)) (l1 : s.locals 1 = some (.int u64 dat.length))
    (l2 : s.locals 2 = some (.ptr 3 0)) (l3 : s.locals 3 = some (.ptr ob 0))
    (l6 : s.locals 6 = some (.int u64 p)) (l8 : s.locals 8 = some (.int u8 h.channels))
    (off : Nat) (l7 : s.locals 7 = some (.int u64 off))
    (b0 b1 b2 b3 : Nat) (l12 : s.locals 12 = some (.int u8 b0)) (l13 : s.locals 13 = some (.int u8 b1))
    (l14 : s.locals 14 = some (.int u8 b2)) (l15 : s.locals 15 = some (.int u8 b3))
    (rle hdr : Nat) (l9 : s.locals 9 = some (.int u8 rle)) (l11 : s.locals 11 = some (.int u8 hdr))
    (hrawT : rle ≠ 0 ∧ (hdr &&& 128) = 0) (hrle8 : rle < 256) (hhdr8 : hdr < 256)
    (hdberr : off + h.channels ≤ dat.length) (hdob : off + h.channels < 2 ^ 64)
    (hl16 : load s.mem (.int u32) (.ptr 3 16) = .ok (.int u32 h.width))
    (hl20 : load s.mem (.int u32) (.ptr 3 20) = .ok (.int u32 h.height))
    (hl26 : load s.mem (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin))
    (hl27 : load s.mem (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin))
    (hw32 : h.width < 2 ^ 32) (hh32 : h.height < 2 ^ 32) (hwpos : 0 < h.width) (hhpos : 0 < h.height)
    (hpw : p / h.width < 2 ^ 32) (hch : h.channels < 256) (hchp : 0 < h.channels) (hro8 : h.rightOrigin < 256) (hto8 : h.topOrigin < 256)
    (hp : p < 2 ^ 64) (hpp : p < h.width * h.height) (hwh64 : h.width * h.height < 2 ^ 64)
    (hmul : tgaDstY h p * h.width < 2 ^ 64) (hadd : tgaDstY h p * h.width + tgaDstX h p < 2 ^ 64)
    (hidx : (tgaDstY h p * h.width + tgaDstX h p) * h.channels < 2 ^ 64)
    (hc : h.channels = 1 ∨ h.channels = 3 ∨ h.channels = 4)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hwb : tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat (byteAt dat off)) (UInt8.ofNat (byteAt dat (off + 1))) (UInt8.ofNat (byteAt dat (off + 2))) (UInt8.ofNat (byteAt dat (off + 3)))).length ≤ obl.length) :
    ∃ s', ExS Gen.prog s tgaPixelBody .normal s' ∧
      s'.locals 6 = some (.int u64 (p + 1)) ∧
      s'.mem ob = some (obl.take (tgaDstIndex h p) ++ tgaPixelOut h.channels (UInt8.ofNat (byteAt dat off)) (UInt8.ofNat (byteAt dat (off + 1))) (UInt8.ofNat (byteAt dat (off + 2))) (UInt8.ofNat (byteAt dat (off + 3))) ++ obl.drop (tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat (byteAt dat off)) (UInt8.ofNat (byteAt dat (off + 1))) (UInt8.ofNat (byteAt dat (off + 2))) (UInt8.ofNat (byteAt dat (off + 3)))).length)) ∧
      s'.mem 3 = some info := by
  let s1 : State := { s with locals := s.locals.upd 17 (.int u8 b0) }
  let s2 : State := { s1 with locals := s1.locals.upd 18 (.int u8 b1) }
  let s3 : State := { s2 with locals := s2.locals.upd 19 (.int u8 b2) }
  let s4 : State := { s3 with locals := s3.locals.upd 20 (.int u8 b3) }
  have e17 : ExS Gen.prog s (.set 17 (.var 12)) .normal s1 := ExS.set (EvE.var l12)
  have l13_1 : s1.locals 13 = some (.int u8 b1) := by simp [s1, Locals.upd_ne, l13]
  have e18 : ExS Gen.prog s1 (.set 18 (.var 13)) .normal s2 := ExS.set (EvE.var l13_1)
  have l14_2 : s2.locals 14 = some (.int u8 b2) := by simp [s2, s1, Locals.upd_ne, l14]
  have e19 : ExS Gen.prog s2 (.set 19 (.var 14)) .normal s3 := ExS.set (EvE.var l14_2)
  have l15_3 : s3.locals 15 = some (.int u8 b3) := by simp [s3, s2, s1, Locals.upd_ne, l15]
  have e20 : ExS Gen.prog s3 (.set 20 (.var 15)) .normal s4 := ExS.set (EvE.var l15_3)
  have l9_4 : s4.locals 9 = some (.int u8 rle) := by simp [s4, s3, s2, s1, Locals.upd_ne, l9]
  have l11_4 : s4.locals 11 = some (.int u8 hdr) := by simp [s4, s3, s2, s1, Locals.upd_ne, l11]
  have evA : EvE Gen.prog s4 (.bin .ne (some u32) (.cast u32 (.var 9)) (.const (.int u32 0))) (boolVal (decide (rle ≠ 0))) :=
    EvE.bin (EvE.cast (EvE.var l9_4) (u8_u32_cast rle hrle8)) (EvE.const (v := .int u32 0)) (bin_u32_ne rle 0)
  have evB : EvE Gen.prog s4 (.bin .eq (some u32) (.bin .band (some u32) (.cast u32 (.var 11)) (.const (.int u32 128))) (.const (.int u32 0))) (boolVal (decide ((hdr &&& 128) = 0))) :=
    EvE.bin (EvE.bin (EvE.cast (EvE.var l11_4) (u8_u32_cast hdr hhdr8)) (EvE.const (v := .int u32 128)) (bin_u32_band hdr 128))
      (EvE.const (v := .int u32 0)) (bin_u32_eq (hdr &&& 128) 0)
  have hcond4 : EvE Gen.prog s4 tgaRawCond (boolVal true) := by
    have ht : truthy (boolVal (decide (rle ≠ 0))) = .ok true := by rw [truthy_boolVal, decide_eq_true hrawT.1]
    have hb : truthy (boolVal (decide ((hdr &&& 128) = 0))) = .ok true := by rw [truthy_boolVal, decide_eq_true hrawT.2]
    exact EvE.land_true evA ht evB (by simpa using hb)
  have l0_4 : s4.locals 0 = some (.ptr bd 0) := by simp [s4, s3, s2, s1, Locals.upd_ne, l0]
  have l1_4 : s4.locals 1 = some (.int u64 dat.length) := by simp [s4, s3, s2, s1, Locals.upd_ne, l1]
  have l7_4 : s4.locals 7 = some (.int u64 off) := by simp [s4, s3, s2, s1, Locals.upd_ne, l7]
  have l8_4 : s4.locals 8 = some (.int u8 h.channels) := by simp [s4, s3, s2, s1, Locals.upd_ne, l8]
  have l18_4 : s4.locals 18 = some (.int u8 b1) := by simp [s4, s3, s2, s1, Locals.upd_same, Locals.upd_ne]
  have l19_4 : s4.locals 19 = some (.int u8 b2) := by simp [s4, s3, s2, s1, Locals.upd_same, Locals.upd_ne]
  have l20_4 : s4.locals 20 = some (.int u8 b3) := by simp [s4, s3, s2, s1, Locals.upd_same, Locals.upd_ne]
  have m4 : s4.mem = s.mem := rfl
  have hrr := ni_tga_raw_read s4 bd dat (by rw [m4]; exact hmbd) l0_4 l1_4 off h.channels b1 b2 b3 l7_4 l8_4 l18_4 l19_4 l20_4
    hch hchp hdberr hdob
  let sR : State := ⟨s4.locals.upd 17 (.int u8 (byteAt dat off))
        |>.upd 18 (if 1 < h.channels then .int u8 (byteAt dat (off + 1)) else .int u8 b1)
        |>.upd 19 (if 2 < h.channels then .int u8 (byteAt dat (off + 2)) else .int u8 b2)
        |>.upd 20 (if 3 < h.channels then .int u8 (byteAt dat (off + 3)) else .int u8 b3)
        |>.upd 7 (.int u64 (off + h.channels)), s4.mem, s4.ro⟩
  have hrawread : ExS Gen.prog s4 tgaRawRead .normal sR := hrr
  have hite : ExS Gen.prog s4 (.ite tgaRawCond tgaRawRead .skip) .normal sR :=
    ExS.ite (b := .skip) (bc := true) hcond4 (by simp [truthy_boolVal]) hrawread
  -- conditional value names
  let r1v := if 1 < h.channels then byteAt dat (off + 1) else b1
  let r2v := if 2 < h.channels then byteAt dat (off + 2) else b2
  let r3v := if 3 < h.channels then byteAt dat (off + 3) else b3
  have h17 : sR.locals 17 = some (.int u8 (byteAt dat off)) := by simp [sR, Locals.upd_same, Locals.upd_ne]
  have h18 : sR.locals 18 = some (.int u8 r1v) := by
    by_cases hc1 : 1 < h.channels <;> simp [sR, r1v, hc1, Locals.upd_same, Locals.upd_ne]
  have h19 : sR.locals 19 = some (.int u8 r2v) := by
    by_cases hc2 : 2 < h.channels <;> simp [sR, r2v, hc2, Locals.upd_same, Locals.upd_ne]
  have h20 : sR.locals 20 = some (.int u8 r3v) := by
    by_cases hc3 : 3 < h.channels <;> simp [sR, r3v, hc3, Locals.upd_same, Locals.upd_ne]
  have hr0 : byteAt dat off < 256 := byteAt_lt _ _
  have hr1 : r1v < 256 := by
    unfold r1v
    split
    · exact byteAt_lt _ _
    · exact hb1
  have hr2 : r2v < 256 := by
    unfold r2v
    split
    · exact byteAt_lt _ _
    · exact hb2
  have hr3 : r3v < 256 := by
    unfold r3v
    split
    · exact byteAt_lt _ _
    · exact hb3
  have hpix : tgaPixelOut h.channels (UInt8.ofNat (byteAt dat off)) (UInt8.ofNat r1v) (UInt8.ofNat r2v) (UInt8.ofNat r3v)
      = tgaPixelOut h.channels (UInt8.ofNat (byteAt dat off)) (UInt8.ofNat (byteAt dat (off + 1))) (UInt8.ofNat (byteAt dat (off + 2))) (UInt8.ofNat (byteAt dat (off + 3))) :=
    tgaPixelOut_raw h.channels b1 b2 b3 (byteAt dat off) (byteAt dat (off + 1)) (byteAt dat (off + 2)) (byteAt dat (off + 3)) hc
  have hwb' : tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat (byteAt dat off)) (UInt8.ofNat r1v) (UInt8.ofNat r2v) (UInt8.ofNat r3v)).length ≤ obl.length := by
    rw [hpix]; exact hwb
  have l2R : sR.locals 2 = some (.ptr 3 0) := by simp [sR, s4, s3, s2, s1, Locals.upd_ne, l2]
  have l3R : sR.locals 3 = some (.ptr ob 0) := by simp [sR, s4, s3, s2, s1, Locals.upd_ne, l3]
  have l6R : sR.locals 6 = some (.int u64 p) := by simp [sR, s4, s3, s2, s1, Locals.upd_ne, l6]
  have l8R : sR.locals 8 = some (.int u8 h.channels) := by simp [sR, s4, s3, s2, s1, Locals.upd_ne, l8]
  have hmR : sR.mem = s.mem := rfl
  obtain ⟨s', hsuf, h6, hob, hinfo'⟩ :=
    ni_tga_pixel_suffix sR h p ob obl (by rw [hmR]; exact hmob) hlob (by show sR.ro = false; simp [sR]; exact hro)
      hob3 info (by rw [hmR]; exact hinfo) h32 l2R l3R l6R l8R (byteAt dat off) r1v r2v r3v h17 h18 h19 h20
      (by rw [hmR]; exact hl16) (by rw [hmR]; exact hl20) (by rw [hmR]; exact hl26) (by rw [hmR]; exact hl27)
      hw32 hh32 hwpos hhpos hpw hch hro8 hto8 hp hpp hwh64 hmul hadd hidx hc hr0 hr1 hr2 hr3 hwb'
  refine ⟨s', ExS.seq e17 (ExS.seq e18 (ExS.seq e19 (ExS.seq e20 (ExS.seq hite hsuf)))), h6, ?_, ?_⟩
  · rw [hob, hpix]
  · exact hinfo'

end NANO.C.Proofs
