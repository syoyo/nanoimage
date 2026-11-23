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

abbrev tgaSet21 : Stmt := .set 21 (.cast u32 (.bin .mod (some u64) (.var 6) (.cast u64 (.load (.int u32) (.field (.var 2) 16)))))
abbrev tgaSet22 : Stmt := .set 22 (.cast u32 (.bin .div (some u64) (.var 6) (.cast u64 (.load (.int u32) (.field (.var 2) 16)))))
abbrev tgaSet23 : Stmt := .set 23 (.cond (.bin .ne (some u32) (.cast u32 (.load (.int u8) (.field (.var 2) 27))) (.const (.int u32 0)))
                        (.bin .sub (some u32) (.bin .sub (some u32) (.load (.int u32) (.field (.var 2) 16)) (.const (.int u32 1))) (.var 21))
                        (.var 21))
abbrev tgaSet24 : Stmt := .set 24 (.cond (.bin .ne (some u32) (.cast u32 (.load (.int u8) (.field (.var 2) 26))) (.const (.int u32 0)))
                        (.var 22)
                        (.bin .sub (some u32) (.bin .sub (some u32) (.load (.int u32) (.field (.var 2) 20)) (.const (.int u32 1))) (.var 22)))
abbrev tgaSet25 : Stmt := .set 25 (.bin .mul (some u64) (.bin .add (some u64) (.bin .mul (some u64) (.cast u64 (.var 24)) (.cast u64 (.load (.int u32) (.field (.var 2) 16)))) (.cast u64 (.var 23))) (.cast u64 (.var 8)))

abbrev tgaDstCompute : Stmt := .seq tgaSet21 (.seq tgaSet22 (.seq tgaSet23 (.seq tgaSet24 tgaSet25)))
abbrev tgaDstFrame (cont : Stmt) : Stmt := .seq tgaSet21 (.seq tgaSet22 (.seq tgaSet23 (.seq tgaSet24 (.seq tgaSet25 cont))))

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
    ∃ s', (∀ (cont : Stmt) (o : Outcome) (sf : State), ExS Gen.prog s' cont o sf → ExS Gen.prog s (tgaDstFrame cont) o sf) ∧
      (∀ j, j ≠ 21 → j ≠ 22 → j ≠ 23 → j ≠ 24 → j ≠ 25 → s'.locals j = s.locals j) ∧
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
  refine ⟨s5, (fun cont o sf hcont => ExS.seq (ExS.set h21) (ExS.seq (ExS.set h22) (ExS.seq (ExS.set h23) (ExS.seq (ExS.set h24) (ExS.seq (ExS.set h25) hcont))))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j h1 h2 h3 h4 h5
    simp [s5, s4, s3, s2, s1, Locals.upd_ne, h1, h2, h3, h4, h5]
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
  (tgaDstFrame (.seq tgaCall
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
      s'.mem 3 = some info ∧
      (∀ j, j ≠ 6 → j ≠ 17 → j ≠ 18 → j ≠ 19 → j ≠ 20 → j ≠ 26 → j ≠ 21 → j ≠ 22 → j ≠ 23 → j ≠ 24 → j ≠ 25 → s'.locals j = s.locals j) ∧
      s'.ro = s.ro ∧
      (∀ j, j ≠ ob → s'.mem j = s.mem j) := by
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
  obtain ⟨s5, hframe, hgen, h21, h22, h23, h24, h25, h3d, h8d, h17d, h18d, h19d, h20d, h6d, h7d, hm5, hro5⟩ :=
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
  refine ⟨s7, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- compose
    exact ExS.seq e17 (ExS.seq e18 (ExS.seq e19 (ExS.seq e20 (ExS.seq hskip (hframe (.seq tgaCall (.seq tgaWrCheck tgaPixelInc)) .normal s7 (ExS.seq hcall (ExS.seq hwr hinc)))))))
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
  · intro j h6 h17 h18 h19 h20 h26 h21 h22 h23 h24 h25
    show s7.locals j = s.locals j
    rw [show s7.locals j = s6.locals j from by simp [s7, Locals.upd_ne, h6]]
    rw [show s6.locals j = s5.locals j from by show (s5.locals.upd 26 (.int i32 1)) j = s5.locals j; simp [Locals.upd_ne, h26]]
    rw [hgen j h21 h22 h23 h24 h25]
    simp [s4, s3, s2, s1, Locals.upd_ne, h17, h18, h19, h20]
  · show s7.ro = s.ro
    rw [show s7.ro = s5.ro from rfl]; exact hro5
  · intro j hj
    show s7.mem j = s.mem j
    rw [show s7.mem j = s6.mem j from rfl]
    rw [show s6.mem j = s5.mem j from by simp [s6, Mem.upd, hj]]
    rw [hm5]

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
    ∃ s', ExS Gen.prog s (tgaDstFrame (.seq tgaCall (.seq tgaWrCheck tgaPixelInc))) .normal s' ∧
      s'.locals 6 = some (.int u64 (p + 1)) ∧
      s'.mem ob = some (obl.take (tgaDstIndex h p) ++ tgaPixelOut h.channels (UInt8.ofNat r0v) (UInt8.ofNat r1v) (UInt8.ofNat r2v) (UInt8.ofNat r3v) ++ obl.drop (tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat r0v) (UInt8.ofNat r1v) (UInt8.ofNat r2v) (UInt8.ofNat r3v)).length)) ∧
      s'.mem 3 = some info ∧
      (∀ j, j ≠ 6 → j ≠ 26 → j ≠ 21 → j ≠ 22 → j ≠ 23 → j ≠ 24 → j ≠ 25 → s'.locals j = s.locals j) ∧
      s'.ro = s.ro ∧
      (∀ j, j ≠ ob → s'.mem j = s.mem j) := by
  obtain ⟨s5, hframe, hgen, h21, h22, h23, h24, h25, h3d, h8d, h17d, h18d, h19d, h20d, h6d, h7d, hm5, hro5⟩ :=
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
  refine ⟨s7, hframe (.seq tgaCall (.seq tgaWrCheck tgaPixelInc)) .normal s7 (ExS.seq hcall (ExS.seq hwr hinc)), ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro j h6 h26 h21 h22 h23 h24 h25
    show s7.locals j = s.locals j
    rw [show s7.locals j = s6.locals j from by simp [s7, Locals.upd_ne, h6]]
    rw [show s6.locals j = s5.locals j from by show (s5.locals.upd 26 (.int i32 1)) j = s5.locals j; simp [Locals.upd_ne, h26]]
    exact hgen j h21 h22 h23 h24 h25
  · show s7.ro = s.ro
    rw [show s7.ro = s5.ro from rfl]; exact hro5
  · intro j hj
    show s7.mem j = s.mem j
    rw [show s7.mem j = s6.mem j from rfl]
    rw [show s6.mem j = s5.mem j from by simp [s6, Mem.upd, hj]]
    rw [hm5]

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem ni_tga_pixel_step_raw (s : State) (h : TgaInfo) (p : Nat) (ob bd : Nat) (obl dat : List UInt8)
    (hmob : s.mem ob = some obl) (hlob : obl.length < 2 ^ 64) (hro : s.ro = false)
    (hob3 : ob ≠ 3) (hbd3 : bd ≠ 3) (hbdo : bd ≠ ob)
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
      s'.mem 3 = some info ∧
      (∀ j, j ≠ 6 → j ≠ 7 → j ≠ 17 → j ≠ 18 → j ≠ 19 → j ≠ 20 → j ≠ 26 → j ≠ 21 → j ≠ 22 → j ≠ 23 → j ≠ 24 → j ≠ 25 → s'.locals j = s.locals j) ∧
      s'.ro = s.ro ∧
      s'.locals 7 = some (.int u64 (off + h.channels)) ∧
      s'.mem bd = some dat := by
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
  obtain ⟨s', hsuf, h6, hob, hinfo', hgen', hro', hmempres⟩ :=
    ni_tga_pixel_suffix sR h p ob obl (by rw [hmR]; exact hmob) hlob (by show sR.ro = false; simp [sR]; exact hro)
      hob3 info (by rw [hmR]; exact hinfo) h32 l2R l3R l6R l8R (byteAt dat off) r1v r2v r3v h17 h18 h19 h20
      (by rw [hmR]; exact hl16) (by rw [hmR]; exact hl20) (by rw [hmR]; exact hl26) (by rw [hmR]; exact hl27)
      hw32 hh32 hwpos hhpos hpw hch hro8 hto8 hp hpp hwh64 hmul hadd hidx hc hr0 hr1 hr2 hr3 hwb'
  refine ⟨s', ExS.seq e17 (ExS.seq e18 (ExS.seq e19 (ExS.seq e20 (ExS.seq hite hsuf)))), h6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hob, hpix]
  · exact hinfo'
  · intro j hj6 hj7 hj17 hj18 hj19 hj20 hj26 hj21 hj22 hj23 hj24 hj25
    rw [hgen' j hj6 hj26 hj21 hj22 hj23 hj24 hj25]
    show sR.locals j = s.locals j
    simp [sR, s4, s3, s2, s1, Locals.upd_ne, hj7, hj17, hj18, hj19, hj20]
  · rw [hro']
  · rw [hgen' 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [sR, Locals.upd_same]
  · rw [hmempres bd (by omega)]
    show sR.mem bd = some dat
    rw [show sR.mem = s.mem from rfl]
    exact hmbd

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

abbrev tgaStep16 : Stmt :=
  .set 16 (.cast u64 (.bin .add (some u64) (.cast u64 (.var 16)) (.const (.int u64 1))))

/-- The decode inner loop (`ni_tga_decode_into_loop0`). -/
abbrev tgaLoop0 : Stmt :=
  .loop (.ite (.bin .lt (some u64) (.var 16) (.var 10)) tgaPixelBody .brk) tgaStep16

/-- loop0 invariant: counter `i`, pixel index `p0+i`, buffer = `i` folded writes,
    info block and the loop's entry locals intact, `i ≤ count`. -/
def TgaLoopInv (s : State) (h : TgaInfo) (p0 count npx ob bd : Nat) (obl info dat : List UInt8)
    (b0 b1 b2 b3 rle hdr off i : Nat) : Prop :=
  s.locals 16 = some (.int u64 i) ∧
  s.locals 6 = some (.int u64 (p0 + i)) ∧
  s.locals 5 = some (.int u64 npx) ∧
  s.locals 0 = some (.ptr bd 0) ∧ s.locals 1 = some (.int u64 dat.length) ∧
  s.mem ob = some (tgaFoldI obl h p0 (tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)) i) ∧
  s.mem 3 = some info ∧ s.mem bd = some dat ∧
  s.locals 2 = some (.ptr 3 0) ∧ s.locals 3 = some (.ptr ob 0) ∧
  s.locals 7 = some (.int u64 off) ∧ s.locals 8 = some (.int u8 h.channels) ∧
  s.locals 9 = some (.int u8 rle) ∧ s.locals 10 = some (.int u64 count) ∧
  s.locals 11 = some (.int u8 hdr) ∧
  s.locals 12 = some (.int u8 b0) ∧ s.locals 13 = some (.int u8 b1) ∧
  s.locals 14 = some (.int u8 b2) ∧ s.locals 15 = some (.int u8 b3) ∧
  s.ro = false ∧ i ≤ count

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem ni_tga_loop0_step_rle (st : State) (h : TgaInfo) (p0 count npx ob bd : Nat) (obl info dat : List UInt8)
    (b0 b1 b2 b3 rle hdr off i : Nat)
    (hinv : TgaLoopInv st h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off i)
    (hi : i < count) (hcount64 : count < 2 ^ 64) (h32 : info.length = 32)
    (hraw : rle = 0 ∨ (hdr &&& 128) ≠ 0) (hrle8 : rle < 256) (hhdr8 : hdr < 256)
    (hl16 : load st.mem (.int u32) (.ptr 3 16) = .ok (.int u32 h.width))
    (hl20 : load st.mem (.int u32) (.ptr 3 20) = .ok (.int u32 h.height))
    (hl26 : load st.mem (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin))
    (hl27 : load st.mem (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin))
    (hw32 : h.width < 2 ^ 32) (hh32 : h.height < 2 ^ 32) (hwpos : 0 < h.width) (hhpos : 0 < h.height)
    (hpw : (p0 + i) / h.width < 2 ^ 32) (hch : h.channels < 256) (hchp : 0 < h.channels)
    (hro8 : h.rightOrigin < 256) (hto8 : h.topOrigin < 256)
    (hp : p0 + i < 2 ^ 64) (hpp : p0 + i < h.width * h.height) (hwh64 : h.width * h.height < 2 ^ 64)
    (hmul : tgaDstY h (p0 + i) * h.width < 2 ^ 64)
    (hadd : tgaDstY h (p0 + i) * h.width + tgaDstX h (p0 + i) < 2 ^ 64)
    (hidx : (tgaDstY h (p0 + i) * h.width + tgaDstX h (p0 + i)) * h.channels < 2 ^ 64)
    (hc : h.channels = 1 ∨ h.channels = 3 ∨ h.channels = 4)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hlob : obl.length < 2 ^ 64) (hob3 : ob ≠ 3) (hbdo : bd ≠ ob)
    (hwb : tgaDstIndex h (p0 + i) + (tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)).length ≤ obl.length) :
    ∃ st1 st2, ExS Gen.prog st (.ite (.bin .lt (some u64) (.var 16) (.var 10)) tgaPixelBody .brk) .normal st1 ∧
      ExS Gen.prog st1 tgaStep16 .normal st2 ∧
      TgaLoopInv st2 h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off (i + 1) := by
  obtain ⟨h16, h6, h5, h0, h1, hobM, hinfo, hmemdat, h2, h3, h7, h8, h9, h10, h11, h12, h13, h14, h15, hroM, hle⟩ := hinv
  have hcond : EvE Gen.prog st (.bin .lt (some u64) (.var 16) (.var 10)) (boolVal true) :=
    EvE.bin (EvE.var h16) (EvE.var h10) (by rw [bin_u64_lt, decide_eq_true hi])
  have hfold_lt : (tgaFoldI obl h p0 (tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)) i).length < 2 ^ 64 := by
    rw [tgaFoldI_length]; exact hlob
  have hwb' : tgaDstIndex h (p0 + i) + (tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)).length ≤ (tgaFoldI obl h p0 (tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)) i).length := by
    simpa [tgaFoldI_length] using hwb
  obtain ⟨st1, hstep, h6', hob', hinfo', hpres, hro', hmem⟩ :=
    ni_tga_pixel_step_rle st h (p0 + i) ob (tgaFoldI obl h p0 (tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)) i)
      hobM hfold_lt hroM hob3 info hinfo h32 h2 h3 h6 h8 b0 b1 b2 b3 h12 h13 h14 h15 rle hdr h9 h11 hraw hrle8 hhdr8
      hl16 hl20 hl26 hl27 hw32 hh32 hwpos hhpos hpw hch hro8 hto8 hp hpp hwh64 hmul hadd hidx hc hb0 hb1 hb2 hb3 hwb'
  have hbody : ExS Gen.prog st (.ite (.bin .lt (some u64) (.var 16) (.var 10)) tgaPixelBody .brk) .normal st1 :=
    ExS.ite (b := .brk) (bc := true) hcond (by simp [truthy_boolVal]) hstep
  have h16_1 : st1.locals 16 = some (.int u64 i) := by
    rw [hpres 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h16
  have hp1 : i + 1 < 2 ^ 64 := by omega
  have e16 : EvE Gen.prog st1 (.cast u64 (.bin .add (some u64) (.cast u64 (.var 16)) (.const (.int u64 1)))) (.int u64 (i + 1)) :=
    EvE.cast (EvE.bin (EvE.cast (EvE.var h16_1) (u64_u64_cast i (by omega)))
      (EvE.const (v := .int u64 1))
      (bin_u64_add i 1 hp1)) (u64_u64_cast (i + 1) hp1)
  let st2 : State := { st1 with locals := st1.locals.upd 16 (.int u64 (i + 1)) }
  have hstep16 : ExS Gen.prog st1 tgaStep16 .normal st2 := ExS.set e16
  refine ⟨st1, st2, hbody, hstep16, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show st2.locals 16 = some (.int u64 (i + 1)); simp [st2, Locals.upd_same]
  · show st2.locals 6 = some (.int u64 (p0 + (i + 1)))
    rw [show st2.locals 6 = st1.locals 6 from by simp [st2, Locals.upd_ne], h6', show (p0 + i) + 1 = p0 + (i + 1) from by omega]
  · show st2.locals 5 = some (.int u64 npx); rw [show st2.locals 5 = st1.locals 5 from by simp [st2, Locals.upd_ne], hpres 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h5
  · show st2.locals 0 = some (.ptr bd 0); rw [show st2.locals 0 = st1.locals 0 from by simp [st2, Locals.upd_ne], hpres 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h0
  · show st2.locals 1 = some (.int u64 dat.length); rw [show st2.locals 1 = st1.locals 1 from by simp [st2, Locals.upd_ne], hpres 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h1
  · show st2.mem ob = some (tgaFoldI obl h p0 (tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)) (i + 1))
    rw [show st2.mem = st1.mem from rfl]
    rw [hob', tgaFoldI_succ, tgaWriteAt_eq _ _ _ hwb']
  · show st2.mem 3 = some info; rw [show st2.mem = st1.mem from rfl]; exact hinfo'
  · show st2.mem bd = some dat; rw [show st2.mem = st1.mem from rfl]; rw [show st1.mem bd = st.mem bd from hmem bd (by omega)]; exact hmemdat
  · show st2.locals 2 = some (.ptr 3 0); rw [show st2.locals 2 = st1.locals 2 from by simp [st2, Locals.upd_ne], hpres 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h2
  · show st2.locals 3 = some (.ptr ob 0); rw [show st2.locals 3 = st1.locals 3 from by simp [st2, Locals.upd_ne], hpres 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h3
  · show st2.locals 7 = some (.int u64 off); rw [show st2.locals 7 = st1.locals 7 from by simp [st2, Locals.upd_ne], hpres 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h7
  · show st2.locals 8 = some (.int u8 h.channels); rw [show st2.locals 8 = st1.locals 8 from by simp [st2, Locals.upd_ne], hpres 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h8
  · show st2.locals 9 = some (.int u8 rle); rw [show st2.locals 9 = st1.locals 9 from by simp [st2, Locals.upd_ne], hpres 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h9
  · show st2.locals 10 = some (.int u64 count); rw [show st2.locals 10 = st1.locals 10 from by simp [st2, Locals.upd_ne], hpres 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h10
  · show st2.locals 11 = some (.int u8 hdr); rw [show st2.locals 11 = st1.locals 11 from by simp [st2, Locals.upd_ne], hpres 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h11
  · show st2.locals 12 = some (.int u8 b0); rw [show st2.locals 12 = st1.locals 12 from by simp [st2, Locals.upd_ne], hpres 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h12
  · show st2.locals 13 = some (.int u8 b1); rw [show st2.locals 13 = st1.locals 13 from by simp [st2, Locals.upd_ne], hpres 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h13
  · show st2.locals 14 = some (.int u8 b2); rw [show st2.locals 14 = st1.locals 14 from by simp [st2, Locals.upd_ne], hpres 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h14
  · show st2.locals 15 = some (.int u8 b3); rw [show st2.locals 15 = st1.locals 15 from by simp [st2, Locals.upd_ne], hpres 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h15
  · show st2.ro = false; rw [show st2.ro = st1.ro from rfl, hro']; exact hroM
  · show i + 1 ≤ count; omega

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

abbrev TgaPixelBounds (h : TgaInfo) (p : Nat) : Prop :=
  p / h.width < 2 ^ 32 ∧ p < 2 ^ 64 ∧ p < h.width * h.height ∧
  tgaDstY h p * h.width < 2 ^ 64 ∧
  tgaDstY h p * h.width + tgaDstX h p < 2 ^ 64 ∧
  (tgaDstY h p * h.width + tgaDstX h p) * h.channels < 2 ^ 64

theorem ni_tga_loop0_rle (st0 : State) (h : TgaInfo) (p0 count npx ob bd : Nat) (obl info dat : List UInt8)
    (b0 b1 b2 b3 rle hdr off i0 : Nat)
    (hinv0 : TgaLoopInv st0 h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off i0)
    (h32 : info.length = 32) (hcount64 : count < 2 ^ 64)
    (hraw : rle = 0 ∨ (hdr &&& 128) ≠ 0) (hrle8 : rle < 256) (hhdr8 : hdr < 256)
    (hl16_0 : load st0.mem (.int u32) (.ptr 3 16) = .ok (.int u32 h.width))
    (hl20_0 : load st0.mem (.int u32) (.ptr 3 20) = .ok (.int u32 h.height))
    (hl26_0 : load st0.mem (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin))
    (hl27_0 : load st0.mem (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin))
    (hw32 : h.width < 2 ^ 32) (hh32 : h.height < 2 ^ 32) (hwpos : 0 < h.width) (hhpos : 0 < h.height)
    (hch : h.channels < 256) (hchp : 0 < h.channels) (hro8 : h.rightOrigin < 256) (hto8 : h.topOrigin < 256)
    (hwh64 : h.width * h.height < 2 ^ 64)
    (hbnd : ∀ p, p < p0 + count → TgaPixelBounds h p)
    (hwbf : ∀ p, p < p0 + count → tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)).length ≤ obl.length)
    (hc : h.channels = 1 ∨ h.channels = 3 ∨ h.channels = 4)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hlob : obl.length < 2 ^ 64) (hob3 : ob ≠ 3) (hbdo : bd ≠ ob) :
    ∃ st', ExS Gen.prog st0 tgaLoop0 .normal st' ∧ TgaLoopInv st' h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off count := by
  have hinv0' := hinv0
  obtain ⟨_, _, _, _, _, _, hinfo0, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hinv0'
  have aux : ∀ (k : Nat) (st : State) (i : Nat), count - i = k → TgaLoopInv st h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off i →
      ∃ st', ExS Gen.prog st tgaLoop0 .normal st' ∧ TgaLoopInv st' h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off count := by
    intro k
    induction k with
    | zero =>
      intro st i hk hinv
      obtain ⟨h16, h6, h5, h0, h1, hobM, hinfo_st, hmemdat, h2, h3, h7, h8, h9, h10, h11, h12, h13, h14, h15, hro_st, hle⟩ := hinv
      have hieq : i = count := by omega
      have hlf : ¬ i < count := by omega
      have hcond : EvE Gen.prog st (.bin .lt (some u64) (.var 16) (.var 10)) (boolVal false) :=
        EvE.bin (EvE.var h16) (EvE.var h10) (by rw [bin_u64_lt, decide_eq_false hlf])
      have hb : ExS Gen.prog st (.ite (.bin .lt (some u64) (.var 16) (.var 10)) tgaPixelBody .brk) .brk st :=
        ExS.ite (bc := false) hcond (by simp [truthy_boolVal]) ExS.brk
      refine ⟨st, ExS.loop_brk hb, ?_⟩
      have hinv_re : TgaLoopInv st h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off i := ⟨h16, h6, h5, h0, h1, hobM, hinfo_st, hmemdat, h2, h3, h7, h8, h9, h10, h11, h12, h13, h14, h15, hro_st, hle⟩
      exact hieq ▸ hinv_re
    | succ k ih =>
      intro st i hk hinv
      obtain ⟨h16, h6, h5, h0, h1, hobM, hinfo_st, hmemdat, h2, h3, h7, h8, h9, h10, h11, h12, h13, h14, h15, hro_st, hle⟩ := hinv
      have hi : i < count := by omega
      have hmem3 : st.mem 3 = st0.mem 3 := by rw [hinfo_st, hinfo0]
      have hl16s : load st.mem (.int u32) (.ptr 3 16) = .ok (.int u32 h.width) := by
        rw [← load_ptr_congr st0.mem st.mem 3 16 (.int u32) hmem3.symm]; exact hl16_0
      have hl20s : load st.mem (.int u32) (.ptr 3 20) = .ok (.int u32 h.height) := by
        rw [← load_ptr_congr st0.mem st.mem 3 20 (.int u32) hmem3.symm]; exact hl20_0
      have hl26s : load st.mem (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin) := by
        rw [← load_ptr_congr st0.mem st.mem 3 26 (.int u8) hmem3.symm]; exact hl26_0
      have hl27s : load st.mem (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin) := by
        rw [← load_ptr_congr st0.mem st.mem 3 27 (.int u8) hmem3.symm]; exact hl27_0
      have hp_lt : p0 + i < p0 + count := by omega
      obtain ⟨hpw, hp, hpp, hmul, hadd, hidx⟩ := hbnd (p0 + i) hp_lt
      have hinv_re : TgaLoopInv st h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off i := ⟨h16, h6, h5, h0, h1, hobM, hinfo_st, hmemdat, h2, h3, h7, h8, h9, h10, h11, h12, h13, h14, h15, hro_st, hle⟩
      obtain ⟨st1, st2, hb, hs, hinv2⟩ :=
        ni_tga_loop0_step_rle st h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off i hinv_re hi hcount64 h32 hraw hrle8 hhdr8
          hl16s hl20s hl26s hl27s hw32 hh32 hwpos hhpos hpw hch hchp hro8 hto8 hp hpp hwh64 hmul hadd hidx hc hb0 hb1 hb2 hb3 hlob hob3 hbdo (hwbf (p0 + i) hp_lt)
      have hk' : count - (i + 1) = k := by omega
      obtain ⟨st', hrec, hinv'⟩ := ih st2 (i + 1) hk' hinv2
      exact ⟨st', ExS.loop_next hb (Or.inl rfl) hs hrec, hinv'⟩
  exact aux (count - i0) st0 i0 rfl hinv0

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

def TgaLoopInvRaw (s : State) (h : TgaInfo) (p0 count npx ob bd : Nat) (obl info dat : List UInt8)
    (b0 b1 b2 b3 rle hdr off0 i : Nat) : Prop :=
  s.locals 16 = some (.int u64 i) ∧
  s.locals 6 = some (.int u64 (p0 + i)) ∧
  s.locals 5 = some (.int u64 npx) ∧
  s.locals 7 = some (.int u64 (off0 + i * h.channels)) ∧
  s.mem ob = some (tgaFoldRaw obl h p0 off0 h.channels dat i) ∧
  s.mem 3 = some info ∧ s.mem bd = some dat ∧
  s.locals 0 = some (.ptr bd 0) ∧ s.locals 1 = some (.int u64 dat.length) ∧
  s.locals 2 = some (.ptr 3 0) ∧ s.locals 3 = some (.ptr ob 0) ∧
  s.locals 8 = some (.int u8 h.channels) ∧ s.locals 9 = some (.int u8 rle) ∧
  s.locals 10 = some (.int u64 count) ∧ s.locals 11 = some (.int u8 hdr) ∧
  s.locals 12 = some (.int u8 b0) ∧ s.locals 13 = some (.int u8 b1) ∧
  s.locals 14 = some (.int u8 b2) ∧ s.locals 15 = some (.int u8 b3) ∧
  s.ro = false ∧ i ≤ count

theorem ni_tga_loop0_step_raw (st : State) (h : TgaInfo) (p0 count npx ob bd : Nat) (obl info dat : List UInt8)
    (b0 b1 b2 b3 rle hdr off0 i : Nat)
    (hinv : TgaLoopInvRaw st h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off0 i)
    (hi : i < count) (hcount64 : count < 2 ^ 64) (h32 : info.length = 32)
    (hrawR : rle ≠ 0) (hrawB : (hdr &&& 128) = 0) (hrle8 : rle < 256) (hhdr8 : hdr < 256)
    (hbd3 : bd ≠ 3) (hbdo : bd ≠ ob) (hdat64 : dat.length < 2 ^ 64)
    (hl16 : load st.mem (.int u32) (.ptr 3 16) = .ok (.int u32 h.width))
    (hl20 : load st.mem (.int u32) (.ptr 3 20) = .ok (.int u32 h.height))
    (hl26 : load st.mem (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin))
    (hl27 : load st.mem (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin))
    (hw32 : h.width < 2 ^ 32) (hh32 : h.height < 2 ^ 32) (hwpos : 0 < h.width) (hhpos : 0 < h.height)
    (hch : h.channels < 256) (hchp : 0 < h.channels) (hro8 : h.rightOrigin < 256) (hto8 : h.topOrigin < 256)
    (hwh64 : h.width * h.height < 2 ^ 64)
    (hbnd : TgaPixelBounds h (p0 + i))
    (hdbnd : (off0 + i * h.channels) + h.channels ≤ dat.length)
    (hdob : (off0 + i * h.channels) + h.channels < 2 ^ 64)
    (hwbf : tgaDstIndex h (p0 + i) + (tgaPixelOut h.channels (UInt8.ofNat (byteAt dat (off0 + i * h.channels))) (UInt8.ofNat (byteAt dat (off0 + i * h.channels + 1))) (UInt8.ofNat (byteAt dat (off0 + i * h.channels + 2))) (UInt8.ofNat (byteAt dat (off0 + i * h.channels + 3)))).length ≤ obl.length)
    (hc : h.channels = 1 ∨ h.channels = 3 ∨ h.channels = 4)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hlob : obl.length < 2 ^ 64) (hob3 : ob ≠ 3) :
    ∃ st1 st2, ExS Gen.prog st (.ite (.bin .lt (some u64) (.var 16) (.var 10)) tgaPixelBody .brk) .normal st1 ∧
      ExS Gen.prog st1 tgaStep16 .normal st2 ∧
      TgaLoopInvRaw st2 h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off0 (i + 1) := by
  obtain ⟨h16, h6, h5, h7, hobM, hinfo, hmemdat, l0', l1', l2, l3, h8, h9, h10, h11, h12, h13, h14, h15, hro, hle⟩ := hinv
  have hcond : EvE Gen.prog st (.bin .lt (some u64) (.var 16) (.var 10)) (boolVal true) :=
    EvE.bin (EvE.var h16) (EvE.var h10) (by rw [bin_u64_lt, decide_eq_true hi])
  have hfold_lt : (tgaFoldRaw obl h p0 off0 h.channels dat i).length < 2 ^ 64 := by rw [tgaFoldRaw_length]; exact hlob
  have hwb' : tgaDstIndex h (p0 + i) + (tgaPixelOut h.channels (UInt8.ofNat (byteAt dat (off0 + i * h.channels))) (UInt8.ofNat (byteAt dat (off0 + i * h.channels + 1))) (UInt8.ofNat (byteAt dat (off0 + i * h.channels + 2))) (UInt8.ofNat (byteAt dat (off0 + i * h.channels + 3)))).length ≤ (tgaFoldRaw obl h p0 off0 h.channels dat i).length := by
    rw [tgaFoldRaw_length]; exact hwbf
  obtain ⟨st1, hstep, h6', hob', hinfo', hpres, hro', h7', hmemdat'⟩ :=
    ni_tga_pixel_step_raw st h (p0 + i) ob bd (tgaFoldRaw obl h p0 off0 h.channels dat i) dat hobM hfold_lt hro hob3 hbd3 hbdo hmemdat
      info hinfo h32 l0' l1' l2 l3 h6 h8 (off0 + i * h.channels) h7 b0 b1 b2 b3 h12 h13 h14 h15 rle hdr h9 h11
      ⟨hrawR, hrawB⟩ hrle8 hhdr8 hdbnd hdob hl16 hl20 hl26 hl27 hw32 hh32 hwpos hhpos hbnd.1 hch hchp hro8 hto8 hbnd.2.1 hbnd.2.2.1 hwh64 hbnd.2.2.2.1 hbnd.2.2.2.2.1 hbnd.2.2.2.2.2 hc hb0 hb1 hb2 hb3 hwb'
  have hbody : ExS Gen.prog st (.ite (.bin .lt (some u64) (.var 16) (.var 10)) tgaPixelBody .brk) .normal st1 :=
    ExS.ite (b := .brk) (bc := true) hcond (by simp [truthy_boolVal]) hstep
  have h16_1 : st1.locals 16 = some (.int u64 i) := by
    rw [hpres 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h16
  have hp1 : i + 1 < 2 ^ 64 := by omega
  have e16 : EvE Gen.prog st1 (.cast u64 (.bin .add (some u64) (.cast u64 (.var 16)) (.const (.int u64 1)))) (.int u64 (i + 1)) :=
    EvE.cast (EvE.bin (EvE.cast (EvE.var h16_1) (u64_u64_cast i (by omega)))
      (EvE.const (v := .int u64 1))
      (bin_u64_add i 1 hp1)) (u64_u64_cast (i + 1) hp1)
  let st2 : State := { st1 with locals := st1.locals.upd 16 (.int u64 (i + 1)) }
  have hstep16 : ExS Gen.prog st1 tgaStep16 .normal st2 := ExS.set e16
  refine ⟨st1, st2, hbody, hstep16, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show st2.locals 16 = some (.int u64 (i + 1)); simp [st2, Locals.upd_same]
  · show st2.locals 6 = some (.int u64 (p0 + (i + 1)))
    rw [show st2.locals 6 = st1.locals 6 from by simp [st2, Locals.upd_ne], h6', show (p0 + i) + 1 = p0 + (i + 1) from by omega]
  · show st2.locals 5 = some (.int u64 npx); rw [show st2.locals 5 = st1.locals 5 from by simp [st2, Locals.upd_ne], hpres 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h5
  · show st2.locals 7 = some (.int u64 (off0 + (i + 1) * h.channels))
    rw [show st2.locals 7 = st1.locals 7 from by simp [st2, Locals.upd_ne], h7', show (off0 + i * h.channels) + h.channels = off0 + (i + 1) * h.channels from by rw [Nat.succ_mul, Nat.add_assoc]]
  · show st2.mem ob = some (tgaFoldRaw obl h p0 off0 h.channels dat (i + 1))
    rw [show st2.mem = st1.mem from rfl]
    rw [hob']
    rw [tgaFoldRaw_succ, tgaWriteAt_eq _ _ _ (by rw [tgaFoldRaw_length]; exact hwbf)]
  · show st2.mem 3 = some info; rw [show st2.mem = st1.mem from rfl]; exact hinfo'
  · show st2.mem bd = some dat; rw [show st2.mem = st1.mem from rfl]; exact hmemdat'
  · show st2.locals 0 = some (.ptr bd 0); rw [show st2.locals 0 = st1.locals 0 from by simp [st2, Locals.upd_ne], hpres 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l0'
  · show st2.locals 1 = some (.int u64 dat.length); rw [show st2.locals 1 = st1.locals 1 from by simp [st2, Locals.upd_ne], hpres 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l1'
  · show st2.locals 2 = some (.ptr 3 0); rw [show st2.locals 2 = st1.locals 2 from by simp [st2, Locals.upd_ne], hpres 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l2
  · show st2.locals 3 = some (.ptr ob 0); rw [show st2.locals 3 = st1.locals 3 from by simp [st2, Locals.upd_ne], hpres 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l3
  · show st2.locals 8 = some (.int u8 h.channels); rw [show st2.locals 8 = st1.locals 8 from by simp [st2, Locals.upd_ne], hpres 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h8
  · show st2.locals 9 = some (.int u8 rle); rw [show st2.locals 9 = st1.locals 9 from by simp [st2, Locals.upd_ne], hpres 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h9
  · show st2.locals 10 = some (.int u64 count); rw [show st2.locals 10 = st1.locals 10 from by simp [st2, Locals.upd_ne], hpres 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h10
  · show st2.locals 11 = some (.int u8 hdr); rw [show st2.locals 11 = st1.locals 11 from by simp [st2, Locals.upd_ne], hpres 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h11
  · show st2.locals 12 = some (.int u8 b0); rw [show st2.locals 12 = st1.locals 12 from by simp [st2, Locals.upd_ne], hpres 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h12
  · show st2.locals 13 = some (.int u8 b1); rw [show st2.locals 13 = st1.locals 13 from by simp [st2, Locals.upd_ne], hpres 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h13
  · show st2.locals 14 = some (.int u8 b2); rw [show st2.locals 14 = st1.locals 14 from by simp [st2, Locals.upd_ne], hpres 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h14
  · show st2.locals 15 = some (.int u8 b3); rw [show st2.locals 15 = st1.locals 15 from by simp [st2, Locals.upd_ne], hpres 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h15
  · show st2.ro = false; rw [show st2.ro = st1.ro from rfl, hro']; exact hro
  · show i + 1 ≤ count; omega

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem ni_tga_loop0_raw (st0 : State) (h : TgaInfo) (p0 count npx ob bd : Nat) (obl info dat : List UInt8)
    (b0 b1 b2 b3 rle hdr off0 i0 : Nat)
    (hinv0 : TgaLoopInvRaw st0 h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off0 i0)
    (h32 : info.length = 32) (hcount64 : count < 2 ^ 64)
    (hrawR : rle ≠ 0) (hrawB : (hdr &&& 128) = 0) (hrle8 : rle < 256) (hhdr8 : hdr < 256)
    (hbd3 : bd ≠ 3) (hbdo : bd ≠ ob) (hdat64 : dat.length < 2 ^ 64)
    (hl16_0 : load st0.mem (.int u32) (.ptr 3 16) = .ok (.int u32 h.width))
    (hl20_0 : load st0.mem (.int u32) (.ptr 3 20) = .ok (.int u32 h.height))
    (hl26_0 : load st0.mem (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin))
    (hl27_0 : load st0.mem (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin))
    (hw32 : h.width < 2 ^ 32) (hh32 : h.height < 2 ^ 32) (hwpos : 0 < h.width) (hhpos : 0 < h.height)
    (hch : h.channels < 256) (hchp : 0 < h.channels) (hro8 : h.rightOrigin < 256) (hto8 : h.topOrigin < 256)
    (hwh64 : h.width * h.height < 2 ^ 64)
    (hbnd : ∀ p, p < p0 + count → TgaPixelBounds h p)
    (hdbnd : ∀ i, i < count → (off0 + i * h.channels) + h.channels ≤ dat.length)
    (hdob : ∀ i, i < count → (off0 + i * h.channels) + h.channels < 2 ^ 64)
    (hwbf : ∀ i, i < count → tgaDstIndex h (p0 + i) + (tgaPixelOut h.channels (UInt8.ofNat (byteAt dat (off0 + i * h.channels))) (UInt8.ofNat (byteAt dat (off0 + i * h.channels + 1))) (UInt8.ofNat (byteAt dat (off0 + i * h.channels + 2))) (UInt8.ofNat (byteAt dat (off0 + i * h.channels + 3)))).length ≤ obl.length)
    (hc : h.channels = 1 ∨ h.channels = 3 ∨ h.channels = 4)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hlob : obl.length < 2 ^ 64) (hob3 : ob ≠ 3) (hbdo : bd ≠ ob) :
    ∃ st', ExS Gen.prog st0 tgaLoop0 .normal st' ∧ TgaLoopInvRaw st' h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off0 count := by
  have hinv0' := hinv0
  obtain ⟨_, _, _, _, _, hinfo0, hmemdat0, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hinv0'
  have aux : ∀ (k : Nat) (st : State) (i : Nat), count - i = k → TgaLoopInvRaw st h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off0 i →
      ∃ st', ExS Gen.prog st tgaLoop0 .normal st' ∧ TgaLoopInvRaw st' h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off0 count := by
    intro k
    induction k with
    | zero =>
      intro st i hk hinv
      obtain ⟨h16, h6, h5, h7, hobM, hinfo, hmemdat, l0', l1', l2, l3, h8, h9, h10, h11, h12, h13, h14, h15, hro, hle⟩ := hinv
      have hieq : i = count := by omega
      have hlf : ¬ i < count := by omega
      have hcond : EvE Gen.prog st (.bin .lt (some u64) (.var 16) (.var 10)) (boolVal false) :=
        EvE.bin (EvE.var h16) (EvE.var h10) (by rw [bin_u64_lt, decide_eq_false hlf])
      have hbE : ExS Gen.prog st (.ite (.bin .lt (some u64) (.var 16) (.var 10)) tgaPixelBody .brk) .brk st :=
        ExS.ite (bc := false) hcond (by simp [truthy_boolVal]) ExS.brk
      refine ⟨st, ExS.loop_brk hbE, ?_⟩
      have hinv_re : TgaLoopInvRaw st h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off0 i := ⟨h16, h6, h5, h7, hobM, hinfo, hmemdat, l0', l1', l2, l3, h8, h9, h10, h11, h12, h13, h14, h15, hro, hle⟩
      exact hieq ▸ hinv_re
    | succ k ih =>
      intro st i hk hinv
      obtain ⟨h16, h6, h5, h7, hobM, hinfo, hmemdat, l0', l1', l2, l3, h8, h9, h10, h11, h12, h13, h14, h15, hro, hle⟩ := hinv
      have hi : i < count := by omega
      have hmem3 : st.mem 3 = st0.mem 3 := by rw [hinfo, hinfo0]
      have hl16s : load st.mem (.int u32) (.ptr 3 16) = .ok (.int u32 h.width) := by
        rw [← load_ptr_congr st0.mem st.mem 3 16 (.int u32) hmem3.symm]; exact hl16_0
      have hl20s : load st.mem (.int u32) (.ptr 3 20) = .ok (.int u32 h.height) := by
        rw [← load_ptr_congr st0.mem st.mem 3 20 (.int u32) hmem3.symm]; exact hl20_0
      have hl26s : load st.mem (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin) := by
        rw [← load_ptr_congr st0.mem st.mem 3 26 (.int u8) hmem3.symm]; exact hl26_0
      have hl27s : load st.mem (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin) := by
        rw [← load_ptr_congr st0.mem st.mem 3 27 (.int u8) hmem3.symm]; exact hl27_0
      have hp_lt : p0 + i < p0 + count := by omega
      have hinv_re : TgaLoopInvRaw st h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off0 i := ⟨h16, h6, h5, h7, hobM, hinfo, hmemdat, l0', l1', l2, l3, h8, h9, h10, h11, h12, h13, h14, h15, hro, hle⟩
      obtain ⟨st1, st2, hbE, hs, hinv2⟩ :=
        ni_tga_loop0_step_raw st h p0 count npx ob bd obl info dat b0 b1 b2 b3 rle hdr off0 i hinv_re hi hcount64 h32 hrawR hrawB hrle8 hhdr8 hbd3 hbdo hdat64
          hl16s hl20s hl26s hl27s hw32 hh32 hwpos hhpos hch hchp hro8 hto8 hwh64 (hbnd (p0 + i) hp_lt) (hdbnd i hi) (hdob i hi) (hwbf i hi) hc hb0 hb1 hb2 hb3 hlob hob3
      have hk' : count - (i + 1) = k := by omega
      obtain ⟨st', hrec, hinv'⟩ := ih st2 (i + 1) hk' hinv2
      exact ⟨st', ExS.loop_next hbE (Or.inl rfl) hs hrec, hinv'⟩
  exact aux (count - i0) st0 i0 rfl hinv0

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

/-- The decode packet loop (`ni_tga_decode_into_loop1`). -/
abbrev tgaLoop1 : Stmt := Gen.ni_tga_decode_into_loop1

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

abbrev tgaL1Hdr : Stmt :=
  .seq (.ite (.bin .ge (some u64) (.var 7) (.var 1)) (.ret (some (.const (.int i32 8)))) .skip)
  (.seq (.set 11 (.load (.int u8) (.index (.var 0) (.var 7) 1)))
  (.seq (.set 7 (.cast u64 (.bin .add (some u64) (.cast u64 (.var 7)) (.cast u64 (.cast u64 (.const (.int u32 1)))))))
        (.set 10 (.bin .add (some u64) (.cast u64 (.bin .band (some u32) (.cast u32 (.var 11)) (.const (.int u32 127)))) (.cast u64 (.const (.int u32 1)))))))

abbrev tgaL1Bytes : Stmt :=
  .seq (.ite (.bin .gt (some u64) (.bin .add (some u64) (.var 7) (.cast u64 (.var 8))) (.var 1)) (.ret (some (.const (.int i32 10)))) .skip)
  (.seq (.set 12 (.load (.int u8) (.index (.var 0) (.var 7) 1)))
  (.seq (.ite (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 1))) (.set 13 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 1)))) 1))) .skip)
  (.seq (.ite (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 2))) (.set 14 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 2)))) 1))) .skip)
  (.seq (.ite (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 3))) (.set 15 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 3)))) 1))) .skip)
        (.set 7 (.cast u64 (.bin .add (some u64) (.cast u64 (.var 7)) (.cast u64 (.cast u64 (.var 8))))))))))

abbrev tgaL1Chk : Stmt :=
  .ite (.bin .gt (some u64) (.var 10) (.bin .sub (some u64) (.var 5) (.var 6))) (.ret (some (.const (.int i32 9)))) .skip

abbrev tgaL1Big : Stmt :=
  .seq (.set 10 (.cast u64 (.const (.int u32 1))))
  (.seq (.set 11 (.cast u8 (.const (.int u32 0))))
  (.seq (.set 12 (.cast u8 (.const (.int u32 0))))
  (.seq (.set 13 (.cast u8 (.const (.int u32 0))))
  (.seq (.set 14 (.cast u8 (.const (.int u32 0))))
  (.seq (.set 15 (.cast u8 (.const (.int u32 255))))
  (.seq (.ite (.bin .ne (some u32) (.cast u32 (.var 9)) (.const (.int u32 0))) tgaL1Hdr .skip)
  (.seq tgaL1Chk
  (.seq (.ite (.lor (.bin .eq (some u32) (.cast u32 (.var 9)) (.const (.int u32 0))) (.bin .ne (some u32) (.bin .band (some u32) (.cast u32 (.var 11)) (.const (.int u32 128))) (.const (.int u32 0)))) tgaL1Bytes .skip)
  (.seq (.set 16 (.cast u64 (.const (.int u32 0)))) tgaLoop0)))))))))

abbrev tgaL1Body : Stmt :=
  .ite (.bin .lt (some u64) (.var 6) (.var 5)) tgaL1Big .brk

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

abbrev tgaL1PreFrame (cont : Stmt) : Stmt :=
  .seq (.set 10 (.cast u64 (.const (.int u32 1))))
  (.seq (.set 11 (.cast u8 (.const (.int u32 0))))
  (.seq (.set 12 (.cast u8 (.const (.int u32 0))))
  (.seq (.set 13 (.cast u8 (.const (.int u32 0))))
  (.seq (.set 14 (.cast u8 (.const (.int u32 0))))
  (.seq (.set 15 (.cast u8 (.const (.int u32 255))))
  (.seq (.ite (.bin .ne (some u32) (.cast u32 (.var 9)) (.const (.int u32 0))) tgaL1Hdr .skip)
  (.seq tgaL1Chk
        (.seq (.ite (.lor (.bin .eq (some u32) (.cast u32 (.var 9)) (.const (.int u32 0))) (.bin .ne (some u32) (.bin .band (some u32) (.cast u32 (.var 11)) (.const (.int u32 128))) (.const (.int u32 0)))) tgaL1Bytes .skip) cont))))))))

theorem tgaL1Big_eq : tgaL1Big = tgaL1PreFrame (.seq (.set 16 (.cast u64 (.const (.int u32 0)))) tgaLoop0) := rfl

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem ni_tga_l1hdr_ok (s : State) (bd : Nat) (dat : List UInt8) (hm : s.mem bd = some dat)
    (l0 : s.locals 0 = some (.ptr bd 0)) (l1 : s.locals 1 = some (.int u64 dat.length))
    (off : Nat) (l7 : s.locals 7 = some (.int u64 off)) (hlt : off < dat.length) (hdat64 : dat.length < 2 ^ 64)
    (hro : s.ro = false) :
    ∃ s', ExS Gen.prog s tgaL1Hdr .normal s' ∧
      s'.locals 11 = some (.int u8 (byteAt dat off)) ∧
      s'.locals 7 = some (.int u64 (off + 1)) ∧
      s'.locals 10 = some (.int u64 ((byteAt dat off &&& 127) + 1)) := by
  have hge : EvE Gen.prog s (.bin .ge (some u64) (.var 7) (.var 1)) (boolVal false) :=
    EvE.bin (EvE.var l7) (EvE.var l1) (by rw [bin_u64_ge, decide_eq_false (by omega)])
  have hguard : ExS Gen.prog s (.ite (.bin .ge (some u64) (.var 7) (.var 1)) (.ret (some (.const (.int i32 8)))) .skip) .normal s :=
    ExS.ite (bc := false) hge (by simp [truthy_boolVal]) ExS.skip
  have hrd : EvE Gen.prog s (.load (.int u8) (.index (.var 0) (.var 7) 1)) (.int u8 (byteAt dat off)) :=
    EvE.load (EvE.index (EvE.var l0) (EvE.var l7) (ptrAddN_ok hm (by omega)))
      (by simpa using load_byte_dyn s.mem bd dat hm off hlt)
  let s1 : State := { s with locals := s.locals.upd 11 (.int u8 (byteAt dat off)) }
  have e11 : ExS Gen.prog s (.set 11 (.load (.int u8) (.index (.var 0) (.var 7) 1))) .normal s1 := ExS.set hrd
  have l7_1 : s1.locals 7 = some (.int u64 off) := by simp [s1, Locals.upd_ne, l7]
  have h7 : EvE Gen.prog s1 (.cast u64 (.bin .add (some u64) (.cast u64 (.var 7)) (.cast u64 (.cast u64 (.const (.int u32 1)))))) (.int u64 (off + 1)) :=
    EvE.cast (EvE.bin (EvE.cast (EvE.var l7_1) (u64_u64_cast off (by omega)))
      (EvE.cast (EvE.cast (EvE.const (v := .int u32 1)) (u32_u64_cast 1 (by omega))) (u64_u64_cast 1 (by omega)))
      (bin_u64_add off 1 (by omega))) (u64_u64_cast (off + 1) (by omega))
  let s2 : State := { s1 with locals := s1.locals.upd 7 (.int u64 (off + 1)) }
  have e7 : ExS Gen.prog s1 (.set 7 (.cast u64 (.bin .add (some u64) (.cast u64 (.var 7)) (.cast u64 (.cast u64 (.const (.int u32 1))))))) .normal s2 := ExS.set h7
  have l11_2 : s2.locals 11 = some (.int u8 (byteAt dat off)) := by simp [s2, Locals.upd_ne, s1, Locals.upd_ne]
  have h10 : EvE Gen.prog s2 (.bin .add (some u64) (.cast u64 (.bin .band (some u32) (.cast u32 (.var 11)) (.const (.int u32 127)))) (.cast u64 (.const (.int u32 1)))) (.int u64 ((byteAt dat off &&& 127) + 1)) :=
    EvE.bin (EvE.cast (EvE.bin (EvE.cast (EvE.var l11_2) (u8_u32_cast (byteAt dat off) (byteAt_lt _ _))) (EvE.const (v := .int u32 127)) (bin_u32_band (byteAt dat off) 127)) (u32_u64_cast (byteAt dat off &&& 127) (by have := Nat.and_le_right (n := byteAt dat off) (m := 127); omega)))
      (EvE.cast (EvE.const (v := .int u32 1)) (u32_u64_cast 1 (by omega))) (bin_u64_add (byteAt dat off &&& 127) 1 (by have := Nat.and_le_right (n := byteAt dat off) (m := 127); omega))
  let s3 : State := { s2 with locals := s2.locals.upd 10 (.int u64 ((byteAt dat off &&& 127) + 1)) }
  have e10 : ExS Gen.prog s2 (.set 10 (.bin .add (some u64) (.cast u64 (.bin .band (some u32) (.cast u32 (.var 11)) (.const (.int u32 127)))) (.cast u64 (.const (.int u32 1))))) .normal s3 := ExS.set h10
  refine ⟨s3, ExS.seq hguard (ExS.seq e11 (ExS.seq e7 e10)), ?_, ?_, ?_⟩
  · show s3.locals 11 = some (.int u8 (byteAt dat off))
    simp [s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  · show s3.locals 7 = some (.int u64 (off + 1))
    simp [s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  · show s3.locals 10 = some (.int u64 ((byteAt dat off &&& 127) + 1))
    simp [s3, Locals.upd_same]

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem ni_tga_l1hdr_err (s : State) (dat : List UInt8) (l1 : s.locals 1 = some (.int u64 dat.length))
    (off : Nat) (l7 : s.locals 7 = some (.int u64 off)) (hge : dat.length ≤ off) (hro : s.ro = false) :
    ExS Gen.prog s tgaL1Hdr (.ret (some (.int i32 8))) s := by
  have hge' : EvE Gen.prog s (.bin .ge (some u64) (.var 7) (.var 1)) (boolVal true) :=
    EvE.bin (EvE.var l7) (EvE.var l1) (by rw [bin_u64_ge, decide_eq_true hge])
  exact ExS.seq_ret (ExS.ite (bc := true) hge' (by simp [truthy_boolVal]) (ExS.ret (EvE.const (v := .int i32 8))))

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C

theorem ni_tga_l1chk_ok (s : State) (count npx pidx : Nat)
    (l10 : s.locals 10 = some (.int u64 count)) (l5 : s.locals 5 = some (.int u64 npx))
    (l6 : s.locals 6 = some (.int u64 pidx)) (hle : pidx ≤ npx)
    (hok : count ≤ npx - pidx) (hro : s.ro = false) :
    ExS Gen.prog s tgaL1Chk .normal s := by
  have hsub : EvE Gen.prog s (.bin .sub (some u64) (.var 5) (.var 6)) (.int u64 (npx - pidx)) :=
    EvE.bin (EvE.var l5) (EvE.var l6) (bin_u64_sub npx pidx hle)
  have hgt : EvE Gen.prog s (.bin .gt (some u64) (.var 10) (.bin .sub (some u64) (.var 5) (.var 6))) (boolVal false) :=
    EvE.bin (EvE.var l10) hsub (by rw [bin_u64_gt, decide_eq_false (by omega)])
  exact ExS.ite (bc := false) hgt (by simp [truthy_boolVal]) ExS.skip

theorem ni_tga_l1chk_err (s : State) (count npx pidx : Nat)
    (l10 : s.locals 10 = some (.int u64 count)) (l5 : s.locals 5 = some (.int u64 npx))
    (l6 : s.locals 6 = some (.int u64 pidx)) (hle : pidx ≤ npx)
    (hbad : npx - pidx < count) (hro : s.ro = false) :
    ExS Gen.prog s tgaL1Chk (.ret (some (.int i32 9))) s := by
  have hsub : EvE Gen.prog s (.bin .sub (some u64) (.var 5) (.var 6)) (.int u64 (npx - pidx)) :=
    EvE.bin (EvE.var l5) (EvE.var l6) (bin_u64_sub npx pidx hle)
  have hgt : EvE Gen.prog s (.bin .gt (some u64) (.var 10) (.bin .sub (some u64) (.var 5) (.var 6))) (boolVal true) :=
    EvE.bin (EvE.var l10) hsub (by rw [bin_u64_gt, decide_eq_true (by omega)])
  exact ExS.ite (bc := true) hgt (by simp [truthy_boolVal]) (ExS.ret (EvE.const (v := .int i32 9)))

theorem ni_tga_l1bytes_ok (s : State) (bd : Nat) (bs : List UInt8) (hm : s.mem bd = some bs)
    (l0 : s.locals 0 = some (.ptr bd 0)) (l1 : s.locals 1 = some (.int u64 bs.length))
    (off channels p1 p2 p3 : Nat) (l7 : s.locals 7 = some (.int u64 off))
    (l8 : s.locals 8 = some (.int u8 channels))
    (l18 : s.locals 13 = some (.int u8 p1)) (l19 : s.locals 14 = some (.int u8 p2))
    (l20 : s.locals 15 = some (.int u8 p3))
    (hch : channels < 256) (hcp : 0 < channels) (hb : off + channels ≤ bs.length)
    (h64 : off + channels < 2 ^ 64) :
    ExS Gen.prog s tgaL1Bytes .normal
      ⟨s.locals.upd 12 (.int u8 (byteAt bs off))
         |>.upd 13 (if 1 < channels then .int u8 (byteAt bs (off + 1)) else .int u8 p1)
         |>.upd 14 (if 2 < channels then .int u8 (byteAt bs (off + 2)) else .int u8 p2)
         |>.upd 15 (if 3 < channels then .int u8 (byteAt bs (off + 3)) else .int u8 p3)
         |>.upd 7 (.int u64 (off + channels)),
       s.mem, s.ro⟩ := by
  have hoffLt : off < bs.length := by omega
  have hadd : EvE Gen.prog s (.bin .add (some u64) (.var 7) (.cast u64 (.var 8))) (.int u64 (off + channels)) :=
    EvE.bin (EvE.var l7) (EvE.cast (EvE.var l8) (u8_u64_cast channels hch)) (bin_u64_add off channels h64)
  have hgt : EvE Gen.prog s (.bin .gt (some u64) (.bin .add (some u64) (.var 7) (.cast u64 (.var 8))) (.var 1)) (boolVal false) :=
    EvE.bin hadd (EvE.var l1) (by rw [bin_u64_gt, decide_eq_false (by omega)])
  have hguard : ExS Gen.prog s (.ite (.bin .gt (some u64) (.bin .add (some u64) (.var 7) (.cast u64 (.var 8))) (.var 1))
      (.ret (some (.const (.int i32 10)))) .skip) .normal s :=
    ExS.ite hgt (truthy_boolVal false) ExS.skip
  have hb0 : EvE Gen.prog s (.load (.int u8) (.index (.var 0) (.var 7) 1)) (.int u8 (byteAt bs off)) :=
    EvE.load (EvE.index (EvE.var l0) (EvE.var l7) (ptrAddN_ok hm (by omega)))
      (by simpa using load_byte_dyn s.mem bd bs hm off hoffLt)
  let s1 : State := { s with locals := s.locals.upd 12 (.int u8 (byteAt bs off)) }
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
  let s2 : State := { s1 with locals := s1.locals.upd 13 (if 1 < channels then .int u8 (byteAt bs (off + 1)) else .int u8 p1) }
  have h18 : ExS Gen.prog s1 (.ite (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 1)))
        (.set 13 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 1)))) 1))) .skip) .normal s2 := by
    by_cases hc1 : 1 < channels
    · have hv : EvE Gen.prog s1 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 1)))) 1)) (.int u8 (byteAt bs (off + 1))) :=
        readK 1 (by omega) hc1 s1 (by simp [s1, Locals.upd_ne, l0]) l7_1 rfl
      have heq : s2 = { s1 with locals := s1.locals.upd 13 (.int u8 (byteAt bs (off + 1))) } := by simp [s2, if_pos hc1]
      rw [heq]
      refine ExS.ite (bc := true) cond1 (by rw [decide_eq_true hc1]; exact truthy_boolVal true) ?_
      exact ExS.set (i := 13) hv
    · have l18_1 : s1.locals 13 = some (.int u8 p1) := by simp [s1, Locals.upd_ne, l18]
      have heq : s2 = s1 := by simp [s2, if_neg hc1, Locals.upd_of_eq s1.locals 13 (.int u8 p1) l18_1]
      rw [heq]
      refine ExS.ite (bc := false) cond1 (by rw [decide_eq_false hc1]; exact truthy_boolVal false) ?_
      exact ExS.skip
  have l7_2 : s2.locals 7 = some (.int u64 off) := by simp [s2, Locals.upd_ne, l7_1]
  have l8_2 : s2.locals 8 = some (.int u8 channels) := by simp [s2, Locals.upd_ne, l8_1]
  have l19_2 : s2.locals 14 = some (.int u8 p2) := by simp [s2, s1, Locals.upd_ne, l19]
  have l20_2 : s2.locals 15 = some (.int u8 p3) := by simp [s2, s1, Locals.upd_ne, l20]
  have cond2 : EvE Gen.prog s2 (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 2))) (boolVal (decide (channels > 2))) :=
    EvE.bin (EvE.cast (EvE.var l8_2) (u8_u32_cast channels hch)) (EvE.const (v := .int u32 2)) (bin_u32_gt channels 2)
  let s3 : State := { s2 with locals := s2.locals.upd 14 (if 2 < channels then .int u8 (byteAt bs (off + 2)) else .int u8 p2) }
  have h19 : ExS Gen.prog s2 (.ite (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 2)))
        (.set 14 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 2)))) 1))) .skip) .normal s3 := by
    by_cases hc2 : 2 < channels
    · have hv : EvE Gen.prog s2 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 2)))) 1)) (.int u8 (byteAt bs (off + 2))) :=
        readK 2 (by omega) hc2 s2 (by simp [s2, s1, Locals.upd_ne, l0]) l7_2 rfl
      have heq : s3 = { s2 with locals := s2.locals.upd 14 (.int u8 (byteAt bs (off + 2))) } := by simp [s3, if_pos hc2]
      rw [heq]
      refine ExS.ite (bc := true) cond2 (by rw [decide_eq_true hc2]; exact truthy_boolVal true) ?_
      exact ExS.set (i := 14) hv
    · have l19_1 : s2.locals 14 = some (.int u8 p2) := l19_2
      have heq : s3 = s2 := by simp [s3, if_neg hc2, Locals.upd_of_eq s2.locals 14 (.int u8 p2) l19_1]
      rw [heq]
      refine ExS.ite (bc := false) cond2 (by rw [decide_eq_false hc2]; exact truthy_boolVal false) ?_
      exact ExS.skip
  have l7_3 : s3.locals 7 = some (.int u64 off) := by simp [s3, Locals.upd_ne, l7_2]
  have l8_3 : s3.locals 8 = some (.int u8 channels) := by simp [s3, Locals.upd_ne, l8_2]
  have l20_3 : s3.locals 15 = some (.int u8 p3) := by simp [s3, s2, s1, Locals.upd_ne, l20]
  have cond3 : EvE Gen.prog s3 (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 3))) (boolVal (decide (channels > 3))) :=
    EvE.bin (EvE.cast (EvE.var l8_3) (u8_u32_cast channels hch)) (EvE.const (v := .int u32 3)) (bin_u32_gt channels 3)
  let s4 : State := { s3 with locals := s3.locals.upd 15 (if 3 < channels then .int u8 (byteAt bs (off + 3)) else .int u8 p3) }
  have h20 : ExS Gen.prog s3 (.ite (.bin .gt (some u32) (.cast u32 (.var 8)) (.const (.int u32 3)))
        (.set 15 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 3)))) 1))) .skip) .normal s4 := by
    by_cases hc3 : 3 < channels
    · have hv : EvE Gen.prog s3 (.load (.int u8) (.index (.var 0) (.bin .add (some u64) (.var 7) (.cast u64 (.const (.int u32 3)))) 1)) (.int u8 (byteAt bs (off + 3))) :=
        readK 3 (by omega) hc3 s3 (by simp [s3, s2, s1, Locals.upd_ne, l0]) l7_3 rfl
      have heq : s4 = { s3 with locals := s3.locals.upd 15 (.int u8 (byteAt bs (off + 3))) } := by simp [s4, if_pos hc3]
      rw [heq]
      refine ExS.ite (bc := true) cond3 (by rw [decide_eq_true hc3]; exact truthy_boolVal true) ?_
      exact ExS.set (i := 15) hv
    · have l20_3' : s3.locals 15 = some (.int u8 p3) := l20_3
      have heq : s4 = s3 := by simp [s4, if_neg hc3, Locals.upd_of_eq s3.locals 15 (.int u8 p3) l20_3']
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
  simpa [tgaL1Bytes, s4, s3, s2, s1] using hcomp


theorem ni_tga_l1bytes_err (s : State) (dat : List UInt8) (l1 : s.locals 1 = some (.int u64 dat.length))
    (off ch : Nat) (l7 : s.locals 7 = some (.int u64 off)) (l8 : s.locals 8 = some (.int u8 ch))
    (hch : ch < 256) (hbad : dat.length < off + ch) (h64 : off + ch < 2 ^ 64) (hro : s.ro = false) :
    ExS Gen.prog s tgaL1Bytes (.ret (some (.int i32 10))) s := by
  have hadd : EvE Gen.prog s (.bin .add (some u64) (.var 7) (.cast u64 (.var 8))) (.int u64 (off + ch)) :=
    EvE.bin (EvE.var l7) (EvE.cast (EvE.var l8) (u8_u64_cast ch hch)) (bin_u64_add off ch h64)
  have hgt : EvE Gen.prog s (.bin .gt (some u64) (.bin .add (some u64) (.var 7) (.cast u64 (.var 8))) (.var 1)) (boolVal true) :=
    EvE.bin hadd (EvE.var l1) (by rw [bin_u64_gt, decide_eq_true (by omega)])
  exact ExS.seq_ret (ExS.ite (bc := true) hgt (by simp [truthy_boolVal]) (ExS.ret (EvE.const (v := .int i32 10))))


theorem ni_tga_l1set (s : State) :
    ∃ s', ExS Gen.prog s
        (.seq (.set 10 (.cast u64 (.const (.int u32 1))))
        (.seq (.set 11 (.cast u8 (.const (.int u32 0))))
        (.seq (.set 12 (.cast u8 (.const (.int u32 0))))
        (.seq (.set 13 (.cast u8 (.const (.int u32 0))))
        (.seq (.set 14 (.cast u8 (.const (.int u32 0))))
              (.set 15 (.cast u8 (.const (.int u32 255))))))))) .normal s' ∧
      s'.locals 10 = some (.int u64 1) ∧ s'.locals 11 = some (.int u8 0) ∧
      s'.locals 12 = some (.int u8 0) ∧ s'.locals 13 = some (.int u8 0) ∧
      s'.locals 14 = some (.int u8 0) ∧ s'.locals 15 = some (.int u8 255) ∧
      s'.mem = s.mem := by
  let s1 : State := { s with locals := s.locals.upd 10 (.int u64 1) }
  have e10 : ExS Gen.prog s (.set 10 (.cast u64 (.const (.int u32 1)))) .normal s1 :=
    ExS.set (EvE.cast (EvE.const (v := .int u32 1)) (u32_u64_cast 1 (by omega)))
  let s2 : State := { s1 with locals := s1.locals.upd 11 (.int u8 0) }
  have e11 : ExS Gen.prog s1 (.set 11 (.cast u8 (.const (.int u32 0)))) .normal s2 :=
    ExS.set (EvE.cast (EvE.const (v := .int u32 0)) (u32_u8_cast 0 (by omega)))
  let s3 : State := { s2 with locals := s2.locals.upd 12 (.int u8 0) }
  have e12 : ExS Gen.prog s2 (.set 12 (.cast u8 (.const (.int u32 0)))) .normal s3 :=
    ExS.set (EvE.cast (EvE.const (v := .int u32 0)) (u32_u8_cast 0 (by omega)))
  let s4 : State := { s3 with locals := s3.locals.upd 13 (.int u8 0) }
  have e13 : ExS Gen.prog s3 (.set 13 (.cast u8 (.const (.int u32 0)))) .normal s4 :=
    ExS.set (EvE.cast (EvE.const (v := .int u32 0)) (u32_u8_cast 0 (by omega)))
  let s5 : State := { s4 with locals := s4.locals.upd 14 (.int u8 0) }
  have e14 : ExS Gen.prog s4 (.set 14 (.cast u8 (.const (.int u32 0)))) .normal s5 :=
    ExS.set (EvE.cast (EvE.const (v := .int u32 0)) (u32_u8_cast 0 (by omega)))
  let s6 : State := { s5 with locals := s5.locals.upd 15 (.int u8 255) }
  have e15 : ExS Gen.prog s5 (.set 15 (.cast u8 (.const (.int u32 255)))) .normal s6 :=
    ExS.set (EvE.cast (EvE.const (v := .int u32 255)) (u32_u8_cast 255 (by omega)))
  refine ⟨s6, ExS.seq e10 (ExS.seq e11 (ExS.seq e12 (ExS.seq e13 (ExS.seq e14 e15)))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show s6.locals 10 = some (.int u64 1); simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  · show s6.locals 11 = some (.int u8 0); simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  · show s6.locals 12 = some (.int u8 0); simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  · show s6.locals 13 = some (.int u8 0); simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  · show s6.locals 14 = some (.int u8 0); simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  · show s6.locals 15 = some (.int u8 255); simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  · show s6.mem = s.mem; simp [s6, s5, s4, s3, s2, s1]


def tgaL1PreRle0Post (s : State) (dat : List UInt8) (off ch : Nat) : State :=
  { s with locals :=
      s.locals.upd 10 (.int u64 1) |>.upd 11 (.int u8 0) |>.upd 12 (.int u8 0)
        |>.upd 13 (.int u8 0) |>.upd 14 (.int u8 0) |>.upd 15 (.int u8 255)
        |>.upd 12 (.int u8 (byteAt dat off))
        |>.upd 13 (if 1 < ch then .int u8 (byteAt dat (off + 1)) else .int u8 0)
        |>.upd 14 (if 2 < ch then .int u8 (byteAt dat (off + 2)) else .int u8 0)
        |>.upd 15 (if 3 < ch then .int u8 (byteAt dat (off + 3)) else .int u8 255)
        |>.upd 7 (.int u64 (off + ch)) }

theorem ni_tga_l1pre_rle0 (s : State) (bd : Nat) (dat : List UInt8) (hm : s.mem bd = some dat)
    (l0 : s.locals 0 = some (.ptr bd 0)) (l1 : s.locals 1 = some (.int u64 dat.length))
    (off ch npx pidx : Nat) (l5 : s.locals 5 = some (.int u64 npx)) (l6 : s.locals 6 = some (.int u64 pidx))
    (l7 : s.locals 7 = some (.int u64 off)) (l8 : s.locals 8 = some (.int u8 ch))
    (l9 : s.locals 9 = some (.int u8 0))
    (hch : ch < 256) (hcp : 0 < ch) (hdat64 : dat.length < 2 ^ 64)
    (hle : pidx ≤ npx) (hleft : 1 ≤ npx - pidx) (hb : off + ch ≤ dat.length) (h64 : off + ch < 2 ^ 64)
    (hro : s.ro = false)
    (cont : Stmt) (o : Outcome) (s' : State)
    (hcont : ExS Gen.prog (tgaL1PreRle0Post s dat off ch) cont o s') :
    ExS Gen.prog s (tgaL1PreFrame cont) o s' := by
  let s1 : State := { s with locals := s.locals.upd 10 (.int u64 1) }
  have e10 : ExS Gen.prog s (.set 10 (.cast u64 (.const (.int u32 1)))) .normal s1 :=
    ExS.set (EvE.cast (EvE.const (v := .int u32 1)) (u32_u64_cast 1 (by omega)))
  let s2 : State := { s1 with locals := s1.locals.upd 11 (.int u8 0) }
  have e11 : ExS Gen.prog s1 (.set 11 (.cast u8 (.const (.int u32 0)))) .normal s2 :=
    ExS.set (EvE.cast (EvE.const (v := .int u32 0)) (u32_u8_cast 0 (by omega)))
  let s3 : State := { s2 with locals := s2.locals.upd 12 (.int u8 0) }
  have e12 : ExS Gen.prog s2 (.set 12 (.cast u8 (.const (.int u32 0)))) .normal s3 :=
    ExS.set (EvE.cast (EvE.const (v := .int u32 0)) (u32_u8_cast 0 (by omega)))
  let s4 : State := { s3 with locals := s3.locals.upd 13 (.int u8 0) }
  have e13 : ExS Gen.prog s3 (.set 13 (.cast u8 (.const (.int u32 0)))) .normal s4 :=
    ExS.set (EvE.cast (EvE.const (v := .int u32 0)) (u32_u8_cast 0 (by omega)))
  let s5 : State := { s4 with locals := s4.locals.upd 14 (.int u8 0) }
  have e14 : ExS Gen.prog s4 (.set 14 (.cast u8 (.const (.int u32 0)))) .normal s5 :=
    ExS.set (EvE.cast (EvE.const (v := .int u32 0)) (u32_u8_cast 0 (by omega)))
  let s6 : State := { s5 with locals := s5.locals.upd 15 (.int u8 255) }
  have e15 : ExS Gen.prog s5 (.set 15 (.cast u8 (.const (.int u32 255)))) .normal s6 :=
    ExS.set (EvE.cast (EvE.const (v := .int u32 255)) (u32_u8_cast 255 (by omega)))
  have l9_6 : s6.locals 9 = some (.int u8 0) := by simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, l9]
  have hne : EvE Gen.prog s6 (.bin .ne (some u32) (.cast u32 (.var 9)) (.const (.int u32 0))) (boolVal false) :=
    EvE.bin (EvE.cast (EvE.var l9_6) (u8_u32_cast 0 (by omega))) (EvE.const (v := .int u32 0)) (bin_u32_ne 0 0)
  have hiterle : ExS Gen.prog s6 (.ite (.bin .ne (some u32) (.cast u32 (.var 9)) (.const (.int u32 0))) tgaL1Hdr .skip) .normal s6 :=
    ExS.ite (bc := false) hne (by simp [truthy_boolVal]) ExS.skip
  have l10_6 : s6.locals 10 = some (.int u64 1) := by simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  have l5_6 : s6.locals 5 = some (.int u64 npx) := by simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, l5]
  have l6_6 : s6.locals 6 = some (.int u64 pidx) := by simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, l6]
  have hchk : ExS Gen.prog s6 tgaL1Chk .normal s6 :=
    ni_tga_l1chk_ok s6 1 npx pidx l10_6 l5_6 l6_6 hle hleft (by simp [s6, s5, s4, s3, s2, s1]; exact hro)
  have l7_6 : s6.locals 7 = some (.int u64 off) := by simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, l7]
  have l8_6 : s6.locals 8 = some (.int u8 ch) := by simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, l8]
  have l0_6 : s6.locals 0 = some (.ptr bd 0) := by simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, l0]
  have l1_6 : s6.locals 1 = some (.int u64 dat.length) := by simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, l1]
  have l13_6 : s6.locals 13 = some (.int u8 0) := by simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  have l14_6 : s6.locals 14 = some (.int u8 0) := by simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  have l15_6 : s6.locals 15 = some (.int u8 255) := by simp [s6, s5, s4, s3, s2, s1, Locals.upd_ne, Locals.upd_same]
  have hm6 : s6.mem = s.mem := by simp [s6, s5, s4, s3, s2, s1]
  have hbytes := ni_tga_l1bytes_ok s6 bd dat (by rw [hm6]; exact hm) l0_6 l1_6 off ch 0 0 255 l7_6 l8_6 l13_6 l14_6 l15_6 hch hcp hb h64
  have heq0 : EvE Gen.prog s6 (.bin .eq (some u32) (.cast u32 (.var 9)) (.const (.int u32 0))) (boolVal true) :=
    EvE.bin (EvE.cast (EvE.var l9_6) (u8_u32_cast 0 (by omega))) (EvE.const (v := .int u32 0)) (bin_u32_eq 0 0)
  have hlor : EvE Gen.prog s6 (.lor (.bin .eq (some u32) (.cast u32 (.var 9)) (.const (.int u32 0))) (.bin .ne (some u32) (.bin .band (some u32) (.cast u32 (.var 11)) (.const (.int u32 128))) (.const (.int u32 0)))) (boolVal true) :=
    EvE.lor_true heq0 (by simp [truthy_boolVal])
  have hiteraw : ExS Gen.prog s6 (.ite (.lor (.bin .eq (some u32) (.cast u32 (.var 9)) (.const (.int u32 0))) (.bin .ne (some u32) (.bin .band (some u32) (.cast u32 (.var 11)) (.const (.int u32 128))) (.const (.int u32 0)))) tgaL1Bytes .skip) .normal (tgaL1PreRle0Post s dat off ch) := by
    refine ExS.ite (bc := true) hlor (by simp [truthy_boolVal]) ?_
    exact hbytes
  exact ExS.seq e10 (ExS.seq e11 (ExS.seq e12 (ExS.seq e13 (ExS.seq e14 (ExS.seq e15 (ExS.seq hiterle (ExS.seq hchk (ExS.seq hiteraw hcont))))))))


/-- loop1 invariant: pixel cursor pidx, data cursor off, buffer obl, with the
    packet-loop's fixed configuration (channels, rle, pointers). -/
def TgaL1Inv (s : State) (h : TgaInfo) (npx ob bd : Nat) (obl info dat : List UInt8) (pidx off : Nat) : Prop :=
  s.locals 5 = some (.int u64 npx) ∧ s.locals 6 = some (.int u64 pidx) ∧
  s.locals 7 = some (.int u64 off) ∧ s.locals 8 = some (.int u8 h.channels) ∧
  s.locals 9 = some (.int u8 h.rle) ∧
  s.locals 0 = some (.ptr bd 0) ∧ s.locals 1 = some (.int u64 dat.length) ∧
  s.locals 2 = some (.ptr 3 0) ∧ s.locals 3 = some (.ptr ob 0) ∧
  s.mem ob = some obl ∧ s.mem 3 = some info ∧ s.mem bd = some dat ∧
  s.ro = false ∧ pidx ≤ npx


theorem ni_tga_l1step_rle0 (s : State) (h : TgaInfo) (npx ob bd : Nat) (obl info dat : List UInt8) (pidx off : Nat)
    (hinv : TgaL1Inv s h npx ob bd obl info dat pidx off) (hpn : pidx < npx) (hrle0 : h.rle = 0)
    (hch : h.channels < 256) (hcp : 0 < h.channels) (hdat64 : dat.length < 2 ^ 64) (hob3 : ob ≠ 3) (hbd3 : bd ≠ 3) (hbdo : bd ≠ ob)
    (hb : off + h.channels ≤ dat.length) (h64 : off + h.channels < 2 ^ 64) (hlob : obl.length < 2 ^ 64)
    (h32 : info.length = 32) (hcount64 : npx < 2 ^ 64)
    (hl16 : load s.mem (.int u32) (.ptr 3 16) = .ok (.int u32 h.width))
    (hl20 : load s.mem (.int u32) (.ptr 3 20) = .ok (.int u32 h.height))
    (hl26 : load s.mem (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin))
    (hl27 : load s.mem (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin))
    (hw32 : h.width < 2 ^ 32) (hh32 : h.height < 2 ^ 32) (hwpos : 0 < h.width) (hhpos : 0 < h.height)
    (hro8 : h.rightOrigin < 256) (hto8 : h.topOrigin < 256) (hwh64 : h.width * h.height < 2 ^ 64)
    (hbnd : ∀ p, p < pidx + 1 → TgaPixelBounds h p)
    (hwbf : ∀ p, p < pidx + 1 → tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat (byteAt dat off)) (UInt8.ofNat (if 1 < h.channels then byteAt dat (off + 1) else 0)) (UInt8.ofNat (if 2 < h.channels then byteAt dat (off + 2) else 0)) (UInt8.ofNat (if 3 < h.channels then byteAt dat (off + 3) else 255))).length ≤ obl.length)
    (hc : h.channels = 1 ∨ h.channels = 3 ∨ h.channels = 4) :
    ∃ s', ExS Gen.prog s (.ite (.bin .lt (some u64) (.var 6) (.var 5)) tgaL1Big .brk) .normal s' ∧
      TgaL1Inv s' h npx ob bd (tgaFoldI obl h pidx (tgaPixelOut h.channels (UInt8.ofNat (byteAt dat off)) (UInt8.ofNat (if 1 < h.channels then byteAt dat (off + 1) else 0)) (UInt8.ofNat (if 2 < h.channels then byteAt dat (off + 2) else 0)) (UInt8.ofNat (if 3 < h.channels then byteAt dat (off + 3) else 255))) 1) info dat (pidx + 1) (off + h.channels) := by
  obtain ⟨l5, l6, l7, l8, l9, l0, l1, l2, l3, hmob, hinfo, hmemdat, hro, hle⟩ := hinv
  let b0 := byteAt dat off
  let b1 := if 1 < h.channels then byteAt dat (off + 1) else 0
  let b2 := if 2 < h.channels then byteAt dat (off + 2) else 0
  let b3 := if 3 < h.channels then byteAt dat (off + 3) else 255
  let post := tgaL1PreRle0Post s dat off h.channels
  let post16 : State := { post with locals := post.locals.upd 16 (.int u64 0) }
  have e16 : ExS Gen.prog post (.set 16 (.cast u64 (.const (.int u32 0)))) .normal post16 :=
    ExS.set (EvE.cast (EvE.const (v := .int u32 0)) (u64_u64_cast 0 (by omega)))
  have hmem16 : post16.mem = s.mem := by simp [post16, post, tgaL1PreRle0Post]
  have inv16 : TgaLoopInv post16 h pidx 1 npx ob bd obl info dat b0 b1 b2 b3 0 0 (off + h.channels) 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [post16, Locals.upd_same]
    · simp [post16, post, tgaL1PreRle0Post, Locals.upd_ne, l6]
    · simp [post16, post, tgaL1PreRle0Post, Locals.upd_ne, l5]
    · simp [post16, post, tgaL1PreRle0Post, Locals.upd_ne, l0]
    · simp [post16, post, tgaL1PreRle0Post, Locals.upd_ne, l1]
    · simp only [post16, post, tgaL1PreRle0Post, tgaFoldI]; exact hmob
    · simp only [post16, post, tgaL1PreRle0Post]; exact hinfo
    · simp only [post16, post, tgaL1PreRle0Post]; exact hmemdat
    · simp [post16, post, tgaL1PreRle0Post, Locals.upd_ne, l2]
    · simp [post16, post, tgaL1PreRle0Post, Locals.upd_ne, l3]
    · simp [post16, post, tgaL1PreRle0Post, Locals.upd_ne, Locals.upd_same]
    · simp [post16, post, tgaL1PreRle0Post, Locals.upd_ne, l8]
    · simp [post16, post, tgaL1PreRle0Post, Locals.upd_ne, l9, hrle0]
    · simp [post16, post, tgaL1PreRle0Post, Locals.upd_ne, Locals.upd_same]
    · simp [post16, post, tgaL1PreRle0Post, Locals.upd_ne, Locals.upd_same]
    · simp [post16, post, tgaL1PreRle0Post, Locals.upd_same, Locals.upd_ne, b0]
    · by_cases hc1 : 1 < h.channels <;> simp [post16, post, tgaL1PreRle0Post, b1, hc1, Locals.upd_ne, Locals.upd_same]
    · by_cases hc2 : 2 < h.channels <;> simp [post16, post, tgaL1PreRle0Post, b2, hc2, Locals.upd_ne, Locals.upd_same]
    · by_cases hc3 : 3 < h.channels <;> simp [post16, post, tgaL1PreRle0Post, b3, hc3, Locals.upd_ne, Locals.upd_same]
    · simp only [post16, post, tgaL1PreRle0Post]; exact hro
    · simp
  have hb0 : b0 < 256 := by simp [b0]; exact byteAt_lt _ _
  have hb1 : b1 < 256 := by
    unfold b1
    split
    · exact byteAt_lt _ _
    · omega
  have hb2 : b2 < 256 := by
    unfold b2
    split
    · exact byteAt_lt _ _
    · omega
  have hb3 : b3 < 256 := by
    unfold b3
    split
    · exact byteAt_lt _ _
    · omega
  have hlen16 : load post16.mem (.int u32) (.ptr 3 16) = .ok (.int u32 h.width) := by rw [hmem16]; exact hl16
  have hl20' : load post16.mem (.int u32) (.ptr 3 20) = .ok (.int u32 h.height) := by rw [hmem16]; exact hl20
  have hl26' : load post16.mem (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin) := by rw [hmem16]; exact hl26
  have hl27' : load post16.mem (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin) := by rw [hmem16]; exact hl27
  have hwb16 : ∀ p, p < pidx + 1 → tgaDstIndex h p + (tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)).length ≤ obl.length := by
    intro p hp
    have e : tgaPixelOut h.channels (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3) = tgaPixelOut h.channels (UInt8.ofNat (byteAt dat off)) (UInt8.ofNat (if 1 < h.channels then byteAt dat (off + 1) else 0)) (UInt8.ofNat (if 2 < h.channels then byteAt dat (off + 2) else 0)) (UInt8.ofNat (if 3 < h.channels then byteAt dat (off + 3) else 255)) := rfl
    rw [e]; exact hwbf p hp
  obtain ⟨s', hloop0, inv'⟩ :=
    ni_tga_loop0_rle post16 h pidx 1 npx ob bd obl info dat b0 b1 b2 b3 0 0 (off + h.channels) 0 inv16 h32 (by omega) (Or.inl rfl) (by omega) (by omega)
      hlen16 hl20' hl26' hl27' hw32 hh32 hwpos hhpos hch hcp hro8 hto8 hwh64 hbnd hwb16 hc hb0 hb1 hb2 hb3 hlob hob3 hbdo
  have hcont : ExS Gen.prog post (.seq (.set 16 (.cast u64 (.const (.int u32 0)))) tgaLoop0) .normal s' := ExS.seq e16 hloop0
  have hpre : ExS Gen.prog s (tgaL1PreFrame (.seq (.set 16 (.cast u64 (.const (.int u32 0)))) tgaLoop0)) .normal s' :=
    ni_tga_l1pre_rle0 s bd dat hmemdat l0 l1 off h.channels npx pidx l5 l6 l7 l8 (by show s.locals 9 = some (.int u8 0); rw [← hrle0]; exact l9) hch hcp hdat64 (by omega) (by omega) hb h64 hro (.seq (.set 16 (.cast u64 (.const (.int u32 0)))) tgaLoop0) .normal s' hcont
  have hcond : EvE Gen.prog s (.bin .lt (some u64) (.var 6) (.var 5)) (boolVal true) :=
    EvE.bin (EvE.var l6) (EvE.var l5) (by rw [bin_u64_lt, decide_eq_true hpn])
  have hbody : ExS Gen.prog s (.ite (.bin .lt (some u64) (.var 6) (.var 5)) tgaL1Big .brk) .normal s' :=
    ExS.ite (b := .brk) (bc := true) hcond (by simp [truthy_boolVal]) (by simpa [tgaL1Big_eq] using hpre)
  refine ⟨s', hbody, ?_⟩
  obtain ⟨k16, k6, k5, k0, k1, kob, k3, kb, k2, k3b, k7, k8, k9, k10, k11, k12, k13, k14, k15, kro, kle⟩ := inv'
  refine ⟨k5, k6, k7, k8, ?_, k0, k1, k2, k3b, kob, k3, kb, kro, ?_⟩
  · show s'.locals 9 = some (.int u8 h.rle); rw [hrle0]; exact k9
  · show pidx + 1 ≤ npx; omega


theorem tgaFoldI_raw_eq (obl0 : List UInt8) (h : TgaInfo) (p0 off0 : Nat) (dat : List UInt8) (j : Nat)
    (hc : h.channels = 1 ∨ h.channels = 3 ∨ h.channels = 4) :
    tgaFoldI (tgaFoldRaw obl0 h p0 off0 h.channels dat j) h (p0 + j)
      (tgaPixelOut h.channels (UInt8.ofNat (byteAt dat (off0 + j * h.channels)))
        (UInt8.ofNat (if 1 < h.channels then byteAt dat (off0 + j * h.channels + 1) else 0))
        (UInt8.ofNat (if 2 < h.channels then byteAt dat (off0 + j * h.channels + 2) else 0))
        (UInt8.ofNat (if 3 < h.channels then byteAt dat (off0 + j * h.channels + 3) else 255))) 1
    = tgaFoldRaw obl0 h p0 off0 h.channels dat (j + 1) := by
  have e : tgaPixelOut h.channels (UInt8.ofNat (byteAt dat (off0 + j * h.channels)))
        (UInt8.ofNat (if 1 < h.channels then byteAt dat (off0 + j * h.channels + 1) else 0))
        (UInt8.ofNat (if 2 < h.channels then byteAt dat (off0 + j * h.channels + 2) else 0))
        (UInt8.ofNat (if 3 < h.channels then byteAt dat (off0 + j * h.channels + 3) else 255))
      = tgaPixelOut h.channels (UInt8.ofNat (byteAt dat (off0 + j * h.channels))) (UInt8.ofNat (byteAt dat (off0 + j * h.channels + 1))) (UInt8.ofNat (byteAt dat (off0 + j * h.channels + 2))) (UInt8.ofNat (byteAt dat (off0 + j * h.channels + 3))) :=
    tgaPixelOut_raw h.channels 0 0 255 (byteAt dat (off0 + j * h.channels)) (byteAt dat (off0 + j * h.channels + 1)) (byteAt dat (off0 + j * h.channels + 2)) (byteAt dat (off0 + j * h.channels + 3)) hc
  rw [e]
  simp [tgaFoldI, tgaFoldRaw]

theorem tgaPixelOut_length (ch b0 b1 b2 b3 : Nat) (hc : ch = 1 ∨ ch = 3 ∨ ch = 4) :
    (tgaPixelOut ch (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)).length = ch := by
  rcases hc with rfl | rfl | rfl <;> simp [tgaPixelOut]


theorem ni_tga_loop1_rle (st0 : State) (h : TgaInfo) (npx ob bd : Nat) (obl info dat : List UInt8) (p0 off0 : Nat)
    (hinv : TgaL1Inv st0 h npx ob bd obl info dat p0 off0) (hpn : p0 ≤ npx) (hrle0 : h.rle = 0)
    (hch : h.channels < 256) (hcp : 0 < h.channels) (hdat64 : dat.length < 2 ^ 64) (hob3 : ob ≠ 3) (hbd3 : bd ≠ 3) (hbdo : bd ≠ ob)
    (hlob : obl.length < 2 ^ 64) (h32 : info.length = 32) (hcount64 : npx < 2 ^ 64)
    (hl16 : load st0.mem (.int u32) (.ptr 3 16) = .ok (.int u32 h.width))
    (hl20 : load st0.mem (.int u32) (.ptr 3 20) = .ok (.int u32 h.height))
    (hl26 : load st0.mem (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin))
    (hl27 : load st0.mem (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin))
    (hw32 : h.width < 2 ^ 32) (hh32 : h.height < 2 ^ 32) (hwpos : 0 < h.width) (hhpos : 0 < h.height)
    (hro8 : h.rightOrigin < 256) (hto8 : h.topOrigin < 256) (hwh64 : h.width * h.height < 2 ^ 64)
    (hbnd : ∀ q, q < npx → TgaPixelBounds h q)
    (hwbf : ∀ q, q < npx → tgaDstIndex h q + h.channels ≤ obl.length)
    (hdbnd : ∀ i, i < npx - p0 → off0 + i * h.channels + h.channels ≤ dat.length)
    (hdob : ∀ i, i < npx - p0 → off0 + i * h.channels + h.channels < 2 ^ 64)
    (hc : h.channels = 1 ∨ h.channels = 3 ∨ h.channels = 4) :
    ∃ st', ExS Gen.prog st0 tgaLoop1 .normal st' ∧ TgaL1Inv st' h npx ob bd (tgaFoldRaw obl h p0 off0 h.channels dat (npx - p0)) info dat npx (off0 + (npx - p0) * h.channels) := by
  have hinv0' := hinv
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hinfo0, _, _, _⟩ := hinv0'
  have aux : ∀ (k : Nat) (st : State) (pidx : Nat), npx - pidx = k → p0 ≤ pidx →
      TgaL1Inv st h npx ob bd (tgaFoldRaw obl h p0 off0 h.channels dat (pidx - p0)) info dat pidx (off0 + (pidx - p0) * h.channels) →
      ∃ st', ExS Gen.prog st tgaLoop1 .normal st' ∧ TgaL1Inv st' h npx ob bd (tgaFoldRaw obl h p0 off0 h.channels dat (npx - p0)) info dat npx (off0 + (npx - p0) * h.channels) := by
    intro k
    induction k with
    | zero =>
      intro st pidx hk hp0 hinv
      obtain ⟨l5, l6, l7, l8, l9, l0, l1, l2, l3, hmob, hinfo, hmemdat, hro, hle⟩ := hinv
      have hpideq : pidx = npx := by omega
      have hlf : ¬ pidx < npx := by omega
      have hcond : EvE Gen.prog st (.bin .lt (some u64) (.var 6) (.var 5)) (boolVal false) :=
        EvE.bin (EvE.var l6) (EvE.var l5) (by rw [bin_u64_lt, decide_eq_false hlf])
      have hbE : ExS Gen.prog st (.ite (.bin .lt (some u64) (.var 6) (.var 5)) tgaL1Big .brk) .brk st :=
        ExS.ite (bc := false) hcond (by simp [truthy_boolVal]) ExS.brk
      refine ⟨st, ExS.loop_brk hbE, ?_⟩
      have hinv_re : TgaL1Inv st h npx ob bd (tgaFoldRaw obl h p0 off0 h.channels dat (pidx - p0)) info dat pidx (off0 + (pidx - p0) * h.channels) := ⟨l5, l6, l7, l8, l9, l0, l1, l2, l3, hmob, hinfo, hmemdat, hro, hle⟩
      exact hpideq ▸ hinv_re
    | succ k ih =>
      intro st pidx hk hp0 hinv
      have hlt : pidx < npx := by omega
      obtain ⟨l5, l6, l7, l8, l9, l0, l1, l2, l3, hmob, hinfo, hmemdat, hro, hle⟩ := hinv
      have hm3 : st0.mem 3 = st.mem 3 := by rw [hinfo0, hinfo]
      have hL16 : load st.mem (.int u32) (.ptr 3 16) = .ok (.int u32 h.width) := by rw [← load_ptr_congr st0.mem st.mem 3 16 (.int u32) hm3]; exact hl16
      have hL20 : load st.mem (.int u32) (.ptr 3 20) = .ok (.int u32 h.height) := by rw [← load_ptr_congr st0.mem st.mem 3 20 (.int u32) hm3]; exact hl20
      have hL26 : load st.mem (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin) := by rw [← load_ptr_congr st0.mem st.mem 3 26 (.int u8) hm3]; exact hl26
      have hL27 : load st.mem (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin) := by rw [← load_ptr_congr st0.mem st.mem 3 27 (.int u8) hm3]; exact hl27
      have heqfold : tgaFoldI (tgaFoldRaw obl h p0 off0 h.channels dat (pidx - p0)) h pidx
            (tgaPixelOut h.channels (UInt8.ofNat (byteAt dat (off0 + (pidx - p0) * h.channels))) (UInt8.ofNat (if 1 < h.channels then byteAt dat (off0 + (pidx - p0) * h.channels + 1) else 0)) (UInt8.ofNat (if 2 < h.channels then byteAt dat (off0 + (pidx - p0) * h.channels + 2) else 0)) (UInt8.ofNat (if 3 < h.channels then byteAt dat (off0 + (pidx - p0) * h.channels + 3) else 255))) 1
          = tgaFoldRaw obl h p0 off0 h.channels dat ((pidx + 1) - p0) := by
        have hh := tgaFoldI_raw_eq obl h p0 off0 dat (pidx - p0) hc
        rw [show p0 + (pidx - p0) = pidx from by omega, show (pidx - p0) + 1 = (pidx + 1) - p0 from by omega] at hh
        exact hh
      obtain ⟨s1, hbE, hinv1⟩ :=
        ni_tga_l1step_rle0 st h npx ob bd (tgaFoldRaw obl h p0 off0 h.channels dat (pidx - p0)) info dat pidx (off0 + (pidx - p0) * h.channels)
          ⟨l5, l6, l7, l8, l9, l0, l1, l2, l3, hmob, hinfo, hmemdat, hro, hle⟩ hlt hrle0 hch hcp hdat64 hob3 hbd3 hbdo
          (hdbnd (pidx - p0) (by omega)) (hdob (pidx - p0) (by omega)) (by rw [tgaFoldRaw_length]; exact hlob) h32 hcount64
          hL16 hL20 hL26 hL27 hw32 hh32 hwpos hhpos hro8 hto8 hwh64
          (by intro q hq; exact hbnd q (by omega))
          (by intro p hp; rw [tgaPixelOut_length h.channels (byteAt dat (off0 + (pidx - p0) * h.channels)) (if 1 < h.channels then byteAt dat (off0 + (pidx - p0) * h.channels + 1) else 0) (if 2 < h.channels then byteAt dat (off0 + (pidx - p0) * h.channels + 2) else 0) (if 3 < h.channels then byteAt dat (off0 + (pidx - p0) * h.channels + 3) else 255) hc, tgaFoldRaw_length]; exact hwbf p (by omega))
          hc
      have hinv2 : TgaL1Inv s1 h npx ob bd (tgaFoldRaw obl h p0 off0 h.channels dat ((pidx + 1) - p0)) info dat (pidx + 1) (off0 + ((pidx + 1) - p0) * h.channels) := by
        rw [heqfold, show off0 + (pidx - p0) * h.channels + h.channels = off0 + ((pidx + 1) - p0) * h.channels from by rw [show (pidx+1)-p0 = (pidx-p0)+1 from by omega, Nat.succ_mul, Nat.add_assoc]] at hinv1
        exact hinv1
      have hk' : npx - (pidx + 1) = k := by omega
      obtain ⟨st', hrec, hinv'⟩ := ih s1 (pidx + 1) hk' (by omega) hinv2
      exact ⟨st', ExS.loop_next hbE (Or.inl rfl) ExS.skip hrec, hinv'⟩
  have hstart : TgaL1Inv st0 h npx ob bd (tgaFoldRaw obl h p0 off0 h.channels dat (p0 - p0)) info dat p0 (off0 + (p0 - p0) * h.channels) := by
    rw [Nat.sub_self, Nat.zero_mul, Nat.add_zero, show tgaFoldRaw obl h p0 off0 h.channels dat 0 = obl from rfl]
    exact hinv
  exact aux (npx - p0) st0 p0 rfl (by omega) hstart
end NANO.C.Proofs
