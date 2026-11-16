/-
  The final composition of `ni_bmp_header`: after the geometry stage reports a
  verdict of 0, the C runs `ni_bmp_header_arith` and `ni_bmp_header_palette`
  and, on success, stores the six `ni_bmp_info` fields. Proved piecewise to
  keep the kernel workload inside limits.
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Lemmas
import NANO.Spec
import NANO.Bmp
import NANO.C.Proofs.Core
import NANO.C.Proofs.NiGeometryTail
import NANO.C.Proofs.Bmp
import NANO.C.Proofs.NiBmpHeaderLoads
import NANO.C.Proofs.NiBmpHeaderArith
import NANO.C.Proofs.NiBmpHeaderPalette
import NANO.C.Proofs.NiBmpHeaderSpecGeo
import NANO.C.Proofs.NiBmpHeaderSpecPalette
import NANO.C.Proofs.NiBmpHeaderSpecCompose
import NANO.C.Proofs.NiBmpHeaderHeight

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000000
set_option maxHeartbeats 8000000

namespace NANO.C.Proofs
open NANO NANO.C

/-- The 48-byte `ni_bmp_info` block after the six tail stores
    (width@24, height@28, pixel_offset@32, bit_count@40, channels@42,
    top_down@43). Bytes 36..39 are preserved from the input (the palette
    stage stored `palette_entries` there), as are 0..23 and 44..47. -/
def bmpHeadBlock (obl : List UInt8) (w h po b c t : Nat) : List UInt8 :=
  obl.take 24 ++ encodeLE 4 w ++ encodeLE 4 h ++ encodeLE 4 po ++
  (obl.drop 36).take 4 ++ encodeLE 2 b ++ encodeLE 1 c ++ encodeLE 1 t ++ obl.drop 44

theorem bmpHeadBlock_length (obl : List UInt8) (h48 : obl.length = 48) (w h po b c t : Nat) :
    (bmpHeadBlock obl w h po b c t).length = 48 := by
  have e4 : ∀ n : Nat, (encodeLE 4 n).length = 4 := encodeLE_length 4
  have e2 : (encodeLE 2 b).length = 2 := encodeLE_length 2 b
  have e1c : (encodeLE 1 c).length = 1 := encodeLE_length 1 c
  have e1t : (encodeLE 1 t).length = 1 := encodeLE_length 1 t
  simp [bmpHeadBlock, h48, e4, e2, e1c, e1t, List.length_take, List.length_append,
    List.length_drop]

/-- The full 48-byte `ni_bmp_info` block a successful `ni_bmp_header` leaves in
    the info object: arith (row_stride@0, output_size@8), palette
    (palette_offset@16, palette_entries@36) and tail (width@24, height@28,
    pixel_offset@32, bit_count@40, channels@42, top_down@43) stores applied to
    the geometry stage's output block. -/
def bmpHeaderFinalBlock (d gout : List UInt8) : List UInt8 :=
  bmpHeadBlock
    (bmpPaletteBlock (bmpArithBlock gout (bmpRowStride (rd32le d 18) (rd16le d 28))
        (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3)
          ((NANO.toInt32 (rd32le d 22)).natAbs)))
      (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
      (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0))
    (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd32le d 10)
    (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3)
    (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)

theorem header_stores_exs (m : Mem) (obl : List UInt8) (hob : m 3 = some obl) (h48 : obl.length = 48)
    (ro : Bool) (hro : ro = false)
    (l : Locals) (hl2 : l 2 = some (.ptr 3 0))
    (w h po : Nat) (hw : w < 4294967296) (hh : h < 4294967296) (hpo : po < 4294967296)
    (b c t : Nat) (hb : b < 65536) (hc : c < 256) (ht : t < 256)
    (hl7 : l 7 = some (.int ⟨32, false⟩ w)) (hl8 : l 8 = some (.int ⟨32, false⟩ h))
    (hl3 : l 3 = some (.int ⟨32, false⟩ po)) (hl5 : l 5 = some (.int ⟨16, false⟩ b))
    (hl9 : l 9 = some (.int ⟨8, false⟩ c)) (hl10 : l 10 = some (.int ⟨8, false⟩ t)) :
    ∃ s', ExS Gen.prog ⟨l, m, ro⟩
      (.seq (.store (.int ⟨32, false⟩) (.field (.var 2) 24) (.var 7))
      (.seq (.store (.int ⟨32, false⟩) (.field (.var 2) 28) (.var 8))
      (.seq (.store (.int ⟨32, false⟩) (.field (.var 2) 32) (.var 3))
      (.seq (.store (.int ⟨16, false⟩) (.field (.var 2) 40) (.var 5))
      (.seq (.store (.int ⟨8, false⟩) (.field (.var 2) 42) (.var 9))
      (.seq (.store (.int ⟨8, false⟩) (.field (.var 2) 43) (.var 10))
                  (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 0))))))))))
      (Outcome.ret (some (.int ⟨32, true⟩ 0))) s' ∧
    s'.mem 3 = some (bmpHeadBlock obl w h po b c t) ∧
    (∀ j, j ≠ 3 → s'.mem j = m j) := by
  have h2 : EvE Gen.prog ⟨l, m, ro⟩ (.var 2) (.ptr 3 0) := EvE.var hl2
  have h7 : EvE Gen.prog ⟨l, m, ro⟩ (.var 7) (.int ⟨32, false⟩ w) := EvE.var hl7
  have h8 : EvE Gen.prog ⟨l, m, ro⟩ (.var 8) (.int ⟨32, false⟩ h) := EvE.var hl8
  have h3 : EvE Gen.prog ⟨l, m, ro⟩ (.var 3) (.int ⟨32, false⟩ po) := EvE.var hl3
  have h5 : EvE Gen.prog ⟨l, m, ro⟩ (.var 5) (.int ⟨16, false⟩ b) := EvE.var hl5
  have h9 : EvE Gen.prog ⟨l, m, ro⟩ (.var 9) (.int ⟨8, false⟩ c) := EvE.var hl9
  have h10 : EvE Gen.prog ⟨l, m, ro⟩ (.var 10) (.int ⟨8, false⟩ t) := EvE.var hl10
  have hr24 : EvE Gen.prog ⟨l, m, ro⟩ (.field (.var 2) 24) (.ptr 3 24) :=
    EvE.field h2 (ptrAddN_ok hob (by omega))
  have hW : ExS Gen.prog ⟨l, m, ro⟩ (.store (.int ⟨32, false⟩) (.field (.var 2) 24) (.var 7)) .normal
      { locals := l, mem := m.upd 3 (obl.take 24 ++ encodeLE 4 w ++ obl.drop 28), ro := ro } :=
    ExS.store hr24 h7 hro (store_field_u32 m 3 obl hob h48 24 (by omega) w hw)
  let b1 : List UInt8 := obl.take 24 ++ encodeLE 4 w ++ obl.drop 28
  have hb1 : b1.length = 48 := by
    simp [b1, h48, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have h2m1 : (m.upd 3 b1) 3 = some b1 := rfl
  let s1 : State := { locals := l, mem := m.upd 3 b1, ro := ro }
  have h2s : EvE Gen.prog s1 (.var 2) (.ptr 3 0) := EvE.var hl2
  have h8s : EvE Gen.prog s1 (.var 8) (.int ⟨32, false⟩ h) := EvE.var hl8
  have h3s : EvE Gen.prog s1 (.var 3) (.int ⟨32, false⟩ po) := EvE.var hl3
  have hr28 : EvE Gen.prog s1 (.field (.var 2) 28) (.ptr 3 28) :=
    EvE.field h2s (ptrAddN_ok h2m1 (by omega))
  have hH : ExS Gen.prog s1 (.store (.int ⟨32, false⟩) (.field (.var 2) 28) (.var 8)) .normal
      { s1 with mem := (m.upd 3 b1).upd 3 (b1.take 28 ++ encodeLE 4 h ++ b1.drop 32) } :=
    ExS.store hr28 h8s hro (store_field_u32 (m.upd 3 b1) 3 b1 h2m1 hb1 28 (by omega) h hh)
  let b2 : List UInt8 := b1.take 28 ++ encodeLE 4 h ++ b1.drop 32
  have hb2 : b2.length = 48 := by
    simp [b2, hb1, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have h2m2 : ((m.upd 3 b1).upd 3 b2) 3 = some b2 := rfl
  let s2 : State := { s1 with mem := (m.upd 3 b1).upd 3 b2 }
  have h2s2 : EvE Gen.prog s2 (.var 2) (.ptr 3 0) := EvE.var hl2
  have h3s2 : EvE Gen.prog s2 (.var 3) (.int ⟨32, false⟩ po) := EvE.var hl3
  have hr32 : EvE Gen.prog s2 (.field (.var 2) 32) (.ptr 3 32) :=
    EvE.field h2s2 (ptrAddN_ok h2m2 (by omega))
  have hP : ExS Gen.prog s2 (.store (.int ⟨32, false⟩) (.field (.var 2) 32) (.var 3)) .normal
      { s2 with mem := ((m.upd 3 b1).upd 3 b2).upd 3 (b2.take 32 ++ encodeLE 4 po ++ b2.drop 36) } :=
    ExS.store hr32 h3s2 hro (store_field_u32 ((m.upd 3 b1).upd 3 b2) 3 b2 h2m2 hb2 32 (by omega) po hpo)
  let b3 : List UInt8 := b2.take 32 ++ encodeLE 4 po ++ b2.drop 36
  have hb3 : b3.length = 48 := by
    simp [b3, hb2, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have h2m3 : (((m.upd 3 b1).upd 3 b2).upd 3 b3) 3 = some b3 := rfl
  let s3 : State := { s2 with mem := ((m.upd 3 b1).upd 3 b2).upd 3 b3 }
  have h2s3 : EvE Gen.prog s3 (.var 2) (.ptr 3 0) := EvE.var hl2
  have h5s3 : EvE Gen.prog s3 (.var 5) (.int ⟨16, false⟩ b) := EvE.var hl5
  have hr40 : EvE Gen.prog s3 (.field (.var 2) 40) (.ptr 3 40) :=
    EvE.field h2s3 (ptrAddN_ok h2m3 (by omega))
  have hBP : ExS Gen.prog s3 (.store (.int ⟨16, false⟩) (.field (.var 2) 40) (.var 5)) .normal
      { s3 with mem := (((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 (b3.take 40 ++ encodeLE 2 b ++ b3.drop 42) } :=
    ExS.store hr40 h5s3 hro (store_field_u16 _ 3 b3 h2m3 hb3 40 (by omega) b hb)
  let b4 : List UInt8 := b3.take 40 ++ encodeLE 2 b ++ b3.drop 42
  have hb4 : b4.length = 48 := by
    simp [b4, hb3, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have h2m4 : ((((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4) 3 = some b4 := rfl
  let s4 : State := { s3 with mem := (((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4 }
  have h2s4 : EvE Gen.prog s4 (.var 2) (.ptr 3 0) := EvE.var hl2
  have h9s4 : EvE Gen.prog s4 (.var 9) (.int ⟨8, false⟩ c) := EvE.var hl9
  have hr42 : EvE Gen.prog s4 (.field (.var 2) 42) (.ptr 3 42) :=
    EvE.field h2s4 (ptrAddN_ok h2m4 (by omega))
  have hCH : ExS Gen.prog s4 (.store (.int ⟨8, false⟩) (.field (.var 2) 42) (.var 9)) .normal
      { s4 with mem := ((((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 (b4.take 42 ++ encodeLE 1 c ++ b4.drop 43) } :=
    ExS.store hr42 h9s4 hro (store_field_u8 _ 3 b4 h2m4 hb4 42 (by omega) c hc)
  let b5 : List UInt8 := b4.take 42 ++ encodeLE 1 c ++ b4.drop 43
  have hb5 : b5.length = 48 := by
    simp [b5, hb4, encodeLE_length, List.length_take, List.length_append, List.length_drop]
  have h2m5 : (((((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5) 3 = some b5 := rfl
  let s5 : State := { s4 with mem := ((((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5 }
  have h2s5 : EvE Gen.prog s5 (.var 2) (.ptr 3 0) := EvE.var hl2
  have h10s5 : EvE Gen.prog s5 (.var 10) (.int ⟨8, false⟩ t) := EvE.var hl10
  have hr43 : EvE Gen.prog s5 (.field (.var 2) 43) (.ptr 3 43) :=
    EvE.field h2s5 (ptrAddN_ok h2m5 (by omega))
  have hTD : ExS Gen.prog s5 (.store (.int ⟨8, false⟩) (.field (.var 2) 43) (.var 10)) .normal
      { s5 with mem := (((((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 (b5.take 43 ++ encodeLE 1 t ++ b5.drop 44) } :=
    ExS.store hr43 h10s5 hro (store_field_u8 _ 3 b5 h2m5 hb5 43 (by omega) t ht)
  let s6 : State := { s5 with mem := (((((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 (b5.take 43 ++ encodeLE 1 t ++ b5.drop 44) }
  have hMem6 : s6.mem 3 = some (b5.take 43 ++ encodeLE 1 t ++ b5.drop 44) := rfl
  have hFinal : (b5.take 43 ++ encodeLE 1 t ++ b5.drop 44) = bmpHeadBlock obl w h po b c t := by
    simp [b1, b2, b3, b4, b5, bmpHeadBlock, h48, encodeLE_length, List.length_take,
      List.length_drop, List.length_append, List.take_append, List.drop_append,
      List.drop_of_length_le, List.take_of_length_le, List.nil_append, List.append_nil]
  have hret : ExS Gen.prog s6 (Stmt.ret (some (Expr.const (Val.int ⟨32, true⟩ 0))))
      (Outcome.ret (some (.int ⟨32, true⟩ 0))) s6 :=
    ExS.ret (EvE.const (v := (.int ⟨32, true⟩ 0)))
  refine ⟨s6, ExS.seq hW (ExS.seq hH (ExS.seq hP (ExS.seq hBP (ExS.seq hCH (ExS.seq hTD hret))))), ?_, ?_⟩
  · rw [hMem6, hFinal]
  · intro j hj
    show (((((m.upd 3 b1).upd 3 b2).upd 3 b3).upd 3 b4).upd 3 b5).upd 3 (b5.take 43 ++ encodeLE 1 t ++ b5.drop 44) j = m j
    rw [mem_upd_other_blk _ 3 j _ hj, mem_upd_other_blk _ 3 j _ hj, mem_upd_other_blk _ 3 j _ hj,
        mem_upd_other_blk _ 3 j _ hj, mem_upd_other_blk _ 3 j _ hj, mem_upd_other_blk _ 3 j _ hj]

end NANO.C.Proofs

namespace NANO.C.Proofs
open NANO NANO.C
def ni_bmp_header_geom_call_stmt : Stmt :=
  (.call (some 11) 14 [(.var 0), (.var 1), (.var 2)])

/-- The prelude of the BMP header body after the signal/layout readers:
    the geometry call, the `geom_code != 0` gate and the five field loads. -/
def ni_bmp_header_prelude_stmt : Stmt :=
  (.seq ni_bmp_header_geom_call_stmt
    (.seq (.ite (.bin .ne (some ⟨32, true⟩) (.var 11) (.const (.int ⟨32, true⟩ 0)))
          (.ret (some (.var 11))) .skip)
      (.seq (.set 7 (.load (.int ⟨32, false⟩) (.field (.var 2) 24)))
        (.seq (.set 8 (.load (.int ⟨32, false⟩) (.field (.var 2) 28)))
          (.seq (.set 5 (.load (.int ⟨16, false⟩) (.field (.var 2) 40)))
            (.seq (.set 9 (.load (.int ⟨8, false⟩) (.field (.var 2) 42)))
              (.set 10 (.load (.int ⟨8, false⟩) (.field (.var 2) 43)))))))))

/-- The arith-gate sub-statement of the BMP header body. -/
def ni_bmp_header_arith_stmt : Stmt :=
  (.seq (.call (some 12) 17 [(.var 7), (.var 8), (.var 5), (.var 9), (.var 3), (.var 1), (.var 2)])
        (.ite (.bin .ne (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 0))) (.ret (some (.var 12))) .skip))

/-- The palette-gate sub-statement of the BMP header body. -/
def ni_bmp_header_palette_stmt : Stmt :=
  (.seq (.call (some 13) 18 [(.var 5), (.var 6), (.var 4), (.var 3), (.var 2)])
        (.ite (.bin .ne (some ⟨32, true⟩) (.var 13) (.const (.int ⟨32, true⟩ 0))) (.ret (some (.var 13))) .skip))

/-- The six field stores ending in `ret 0`. -/
def ni_bmp_header_stores_stmt : Stmt :=
  (.seq (.store (.int ⟨32, false⟩) (.field (.var 2) 24) (.var 7))
    (.seq (.store (.int ⟨32, false⟩) (.field (.var 2) 28) (.var 8))
      (.seq (.store (.int ⟨32, false⟩) (.field (.var 2) 32) (.var 3))
        (.seq (.store (.int ⟨16, false⟩) (.field (.var 2) 40) (.var 5))
          (.seq (.store (.int ⟨8, false⟩) (.field (.var 2) 42) (.var 9))
            (.seq (.store (.int ⟨8, false⟩) (.field (.var 2) 43) (.var 10))
                  (.ret (some (.const (.int ⟨32, true⟩ 0))))))))))

/-- The palette call and the six field stores after it. -/
def ni_bmp_header_rest_stmt : Stmt :=
  (.seq ni_bmp_header_palette_stmt ni_bmp_header_stores_stmt)

/-- Everything of `ni_bmp_header` after the readers, composed from the named
    pieces so the kernel can unfold one level at a time. -/
abbrev ni_bmp_header_rem_stmt : Stmt :=
  (.seq ni_bmp_header_prelude_stmt
    (.seq ni_bmp_header_arith_stmt ni_bmp_header_rest_stmt))

theorem ni_bmp_header_load_width_exs (d : List UInt8) (s7 : State)
    (gout : List UInt8) (hg_len : gout.length = 48)
    (hob' : s7.mem 3 = some gout)
    (hW24 : (gout.drop 24).take 4 = encodeLE 4 (rd32le d 18))
    (hl2 : s7.locals 2 = some (.ptr 3 0)) :
    ∃ s8, ExS Gen.prog s7 (.set 7 (.load (.int ⟨32, false⟩) (.field (.var 2) 24))) .normal s8 ∧
      s8.locals 1 = s7.locals 1 ∧ s8.locals 2 = s7.locals 2 ∧ s8.locals 3 = s7.locals 3 ∧
      s8.locals 4 = s7.locals 4 ∧ s8.locals 5 = s7.locals 5 ∧ s8.locals 6 = s7.locals 6 ∧
      s8.locals 7 = some (.int ⟨32, false⟩ (rd32le d 18)) ∧
      s8.locals 9 = s7.locals 9 ∧ s8.locals 10 = s7.locals 10 ∧
      s8.mem = s7.mem ∧ s8.locals 8 = s7.locals 8 ∧ s8.ro = s7.ro := by
  have hptr2_7 : EvE Gen.prog s7 (.var 2) (.ptr 3 0) := EvE.var hl2
  have hfield24 : EvE Gen.prog s7 (.field (.var 2) 24) (.ptr 3 24) :=
    EvE.field hptr2_7 (ptrAddN_ok hob' (by omega))
  have hWLoad : EvE Gen.prog s7 (.load (.int ⟨32, false⟩) (.field (.var 2) 24))
      (.int ⟨32, false⟩ (rd32le d 18)) := by
    have hloadRaw : (load s7.mem (.int ⟨32, false⟩) (.ptr 3 24)) =
        Res.ok (Val.int ⟨32, false⟩ (rd32le d 18)) :=
      load_u32_field_of_geom s7.mem 24 gout hob' hg_len (by omega : 24 ≤ 44)
        (rd32le d 18) hW24 (rd32_lt d 18)
    exact EvE.load hfield24 hloadRaw
  let s8 : State := { s7 with locals := s7.locals.upd 7 (.int ⟨32, false⟩ (rd32le d 18)) }
  refine ⟨s8, ExS.set hWLoad, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ni_bmp_header_load_height_exs (d : List UInt8) (s8 : State)
    (gout : List UInt8) (hg_len : gout.length = 48)
    (hob' : s8.mem 3 = some gout)
    (hH28 : (gout.drop 28).take 4 = encodeLE 4 ((NANO.toInt32 (rd32le d 22)).natAbs))
    (hh32 : ((NANO.toInt32 (rd32le d 22)).natAbs) ≤ 4294967295)
    (hl2 : s8.locals 2 = some (.ptr 3 0)) :
    ∃ s9, ExS Gen.prog s8 (.set 8 (.load (.int ⟨32, false⟩) (.field (.var 2) 28))) .normal s9 ∧
      s9.locals 1 = s8.locals 1 ∧ s9.locals 2 = s8.locals 2 ∧ s9.locals 3 = s8.locals 3 ∧
      s9.locals 4 = s8.locals 4 ∧ s9.locals 5 = s8.locals 5 ∧ s9.locals 6 = s8.locals 6 ∧
      s9.locals 7 = s8.locals 7 ∧ s9.locals 9 = s8.locals 9 ∧ s9.locals 10 = s8.locals 10 ∧
      s9.mem = s8.mem ∧ s9.locals 8 = some (.int ⟨32, false⟩ ((NANO.toInt32 (rd32le d 22)).natAbs)) ∧ s9.ro = s8.ro := by
  have hfield28 : EvE Gen.prog s8 (.field (.var 2) 28) (.ptr 3 28) :=
    EvE.field (EvE.var hl2) (ptrAddN_ok hob' (by omega))
  have hHLoad : EvE Gen.prog s8 (.load (.int ⟨32, false⟩) (.field (.var 2) 28))
      (.int ⟨32, false⟩ ((NANO.toInt32 (rd32le d 22)).natAbs)) := by
    have hloadRaw : (load s8.mem (.int ⟨32, false⟩) (.ptr 3 28)) =
        Res.ok (Val.int ⟨32, false⟩ ((NANO.toInt32 (rd32le d 22)).natAbs)) :=
      load_u32_field_of_geom s8.mem 28 gout hob' hg_len (by omega : 28 ≤ 44)
        ((NANO.toInt32 (rd32le d 22)).natAbs) hH28 (by omega)
    exact EvE.load hfield28 hloadRaw
  let s9 : State := { s8 with locals := s8.locals.upd 8 (.int ⟨32, false⟩ ((NANO.toInt32 (rd32le d 22)).natAbs)) }
  refine ⟨s9, ExS.set hHLoad, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ni_bmp_header_load_bitCount_exs (d : List UInt8) (s9 : State)
    (gout : List UInt8) (hg_len : gout.length = 48)
    (hob' : s9.mem 3 = some gout)
    (hB40 : (gout.drop 40).take 2 = encodeLE 2 (rd16le d 28))
    (hl2 : s9.locals 2 = some (.ptr 3 0)) :
    ∃ s10, ExS Gen.prog s9 (.set 5 (.load (.int ⟨16, false⟩) (.field (.var 2) 40))) .normal s10 ∧
      s10.locals 1 = s9.locals 1 ∧ s10.locals 2 = s9.locals 2 ∧ s10.locals 3 = s9.locals 3 ∧
      s10.locals 4 = s9.locals 4 ∧ s10.locals 6 = s9.locals 6 ∧
      s10.locals 7 = s9.locals 7 ∧ s10.locals 8 = s9.locals 8 ∧ s10.locals 9 = s9.locals 9 ∧
      s10.locals 10 = s9.locals 10 ∧
      s10.locals 5 = some (.int ⟨16, false⟩ (rd16le d 28)) ∧ s10.mem = s9.mem ∧ s10.ro = s9.ro := by
  have hfield40 : EvE Gen.prog s9 (.field (.var 2) 40) (.ptr 3 40) :=
    EvE.field (EvE.var hl2) (ptrAddN_ok hob' (by omega))
  have hBLoad : EvE Gen.prog s9 (.load (.int ⟨16, false⟩) (.field (.var 2) 40))
      (.int ⟨16, false⟩ (rd16le d 28)) := by
    have hloadRaw : (load s9.mem (.int ⟨16, false⟩) (.ptr 3 40)) =
        Res.ok (Val.int ⟨16, false⟩ (rd16le d 28)) :=
      load_u16_field_of_geom s9.mem 40 gout hob' hg_len (by omega : 40 ≤ 46)
        (rd16le d 28) hB40 (rd16le_lt d 28)
    exact EvE.load hfield40 hloadRaw
  let s10 : State := { s9 with locals := s9.locals.upd 5 (.int ⟨16, false⟩ (rd16le d 28)) }
  refine ⟨s10, ExS.set hBLoad, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ni_bmp_header_load_channels_exs (d : List UInt8) (s10 : State)
    (gout : List UInt8) (hg_len : gout.length = 48)
    (hob' : s10.mem 3 = some gout)
    (hC42 : (gout.drop 42).take 1 = encodeLE 1 (if rd16le d 28 = 32 then 4 else 3))
    (hl2 : s10.locals 2 = some (.ptr 3 0)) :
    ∃ s11, ExS Gen.prog s10 (.set 9 (.load (.int ⟨8, false⟩) (.field (.var 2) 42))) .normal s11 ∧
      s11.locals 1 = s10.locals 1 ∧ s11.locals 2 = s10.locals 2 ∧ s11.locals 3 = s10.locals 3 ∧
      s11.locals 4 = s10.locals 4 ∧ s11.locals 5 = s10.locals 5 ∧ s11.locals 6 = s10.locals 6 ∧
      s11.locals 7 = s10.locals 7 ∧ s11.locals 8 = s10.locals 8 ∧ s11.locals 10 = s10.locals 10 ∧
      s11.locals 9 = some (.int ⟨8, false⟩ (if rd16le d 28 = 32 then 4 else 3)) ∧ s11.mem = s10.mem ∧ s11.ro = s10.ro := by
  have hfield42 : EvE Gen.prog s10 (.field (.var 2) 42) (.ptr 3 42) :=
    EvE.field (EvE.var hl2) (ptrAddN_ok hob' (by omega))
  have hCLoad : EvE Gen.prog s10 (.load (.int ⟨8, false⟩) (.field (.var 2) 42))
      (.int ⟨8, false⟩ (if rd16le d 28 = 32 then 4 else 3)) := by
    have hloadRaw : (load s10.mem (.int ⟨8, false⟩) (.ptr 3 42)) =
        Res.ok (Val.int ⟨8, false⟩ (if rd16le d 28 = 32 then 4 else 3)) :=
      load_u8_field_of_geom s10.mem 42 gout hob' hg_len (by omega : 42 ≤ 47)
        (if rd16le d 28 = 32 then 4 else 3) hC42 (by by_cases h32 : rd16le d 28 = 32 <;> simp [h32])
    exact EvE.load hfield42 hloadRaw
  let s11 : State := { s10 with locals := s10.locals.upd 9 (.int ⟨8, false⟩ (if rd16le d 28 = 32 then 4 else 3)) }
  refine ⟨s11, ExS.set hCLoad, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ni_bmp_header_load_topDown_exs (d : List UInt8) (s11 : State)
    (gout : List UInt8) (hg_len : gout.length = 48)
    (hob' : s11.mem 3 = some gout)
    (hT43 : (gout.drop 43).take 1 = encodeLE 1 (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0))
    (hTopD : (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0) < 256)
    (hl2 : s11.locals 2 = some (.ptr 3 0)) :
    ∃ s12, ExS Gen.prog s11 (.set 10 (.load (.int ⟨8, false⟩) (.field (.var 2) 43))) .normal s12 ∧
      s12.locals 1 = s11.locals 1 ∧ s12.locals 2 = s11.locals 2 ∧ s12.locals 3 = s11.locals 3 ∧
      s12.locals 4 = s11.locals 4 ∧ s12.locals 5 = s11.locals 5 ∧ s12.locals 6 = s11.locals 6 ∧
      s12.locals 7 = s11.locals 7 ∧ s12.locals 8 = s11.locals 8 ∧ s12.locals 9 = s11.locals 9 ∧
      s12.locals 10 = some (.int ⟨8, false⟩ (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)) ∧
      s12.mem = s11.mem ∧ s12.ro = s11.ro := by
  have hfield43 : EvE Gen.prog s11 (.field (.var 2) 43) (.ptr 3 43) :=
    EvE.field (EvE.var hl2) (ptrAddN_ok hob' (by omega))
  have hTLoad : EvE Gen.prog s11 (.load (.int ⟨8, false⟩) (.field (.var 2) 43))
      (.int ⟨8, false⟩ (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)) := by
    have hloadRaw : (load s11.mem (.int ⟨8, false⟩) (.ptr 3 43)) =
        Res.ok (Val.int ⟨8, false⟩ (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)) :=
      load_u8_field_of_geom s11.mem 43 gout hob' hg_len (by omega : 43 ≤ 47)
        (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0) hT43 hTopD
    exact EvE.load hfield43 hloadRaw
  let s12 : State := { s11 with locals := s11.locals.upd 10 (.int ⟨8, false⟩ (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)) }
  refine ⟨s12, ExS.set hTLoad, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ni_bmp_header_geom_call_exs (s6 : State) (d : List UInt8) (bd : Nat) (hm : s6.mem bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hd : 54 ≤ d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : s6.mem 3 = some obl) (h48 : obl.length = 48)
    (hS6ro : s6.ro = false)
    (hl0 : s6.locals 0 = some (.ptr bd 0))
    (hl2 : s6.locals 2 = some (.ptr 3 0))
    (hl1 : s6.locals 1 = some (.int ⟨64, false⟩ size))
    (hl3 : s6.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)))
    (hl4 : s6.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)))
    (hl6 : s6.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46))) :
    ∃ s7, ExS Gen.prog s6 ni_bmp_header_geom_call_stmt .normal s7 ∧
      s7.locals 1 = some (.int ⟨64, false⟩ size) ∧
      s7.locals 2 = some (.ptr 3 0) ∧
      s7.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)) ∧
      s7.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)) ∧
      s7.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46)) ∧
      s7.locals 11 = some (.int ⟨32, true⟩ (bmpGeometryCode d)) ∧
      s7.ro = false ∧
      bmpGeometryCode d ≤ 6 ∧
      (∀ hG0 : bmpGeometryCode d = 0, s7.mem 3 = some (geomOutBlock obl d)) ∧
      (∀ hG0 : bmpGeometryCode d = 0, ∀ j, j ≠ 3 → s7.mem j = s6.mem j) := by
  obtain ⟨sGeo, exGeo, hblk0, hUnt0⟩ := ni_bmp_geometry_exs s6.mem bd d hm size hs (by omega) hlen obl hob h48 s6.ro hS6ro
  have hread2 : s6.locals 2 = some (.ptr 3 0) := hl2
  have hread0 : s6.locals 0 = some (.ptr bd 0) := hl0
  have hread1 : s6.locals 1 = some (.int ⟨64, false⟩ size) := hl1
  have hwG : ExS Gen.prog s6 ni_bmp_header_geom_call_stmt .normal
      { locals := s6.locals.upd 11 (.int ⟨32, true⟩ (bmpGeometryCode d)), mem := sGeo.mem, ro := s6.ro } :=
    ExS.call_dst
      (EvArgs.cons (EvE.var hread0)
        (EvArgs.cons (EvE.var hread1)
          (EvArgs.cons (EvE.var hread2) EvArgs.nil)))
      (show Gen.prog 14 = some Gen.ni_bmp_geometry from rfl)
      (show Gen.ni_bmp_geometry.params.length = 3 from rfl)
      exGeo
  let s7 : State := { locals := s6.locals.upd 11 (.int ⟨32, true⟩ (bmpGeometryCode d)), mem := sGeo.mem, ro := s6.ro }
  have hl1_7 : s7.locals 1 = some (.int ⟨64, false⟩ size) := by
    show s7.locals 1 = some (.int ⟨64, false⟩ size)
    rw [show s7.locals 1 = s6.locals 1 from rfl]; exact hl1
  have hl2_7 : s7.locals 2 = some (.ptr 3 0) := by
    show s7.locals 2 = some (.ptr 3 0)
    rw [show s7.locals 2 = s6.locals 2 from rfl]; exact hl2
  have hl3_7 : s7.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)) := by
    show s7.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10))
    rw [show s7.locals 3 = s6.locals 3 from rfl]; exact hl3
  have hl4_7 : s7.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)) := by
    show s7.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14))
    rw [show s7.locals 4 = s6.locals 4 from rfl]; exact hl4
  have hl6_7 : s7.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46)) := by
    show s7.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46))
    rw [show s7.locals 6 = s6.locals 6 from rfl]; exact hl6
  have hl11_7 : s7.locals 11 = some (.int ⟨32, true⟩ (bmpGeometryCode d)) := rfl
  have hS7ro : s7.ro = false := by rw [show s7.ro = s6.ro from rfl]; exact hS6ro
  have hSm : bmpGeometryCode d ≤ 6 := bmpGeometryCode_bound d
  exact ⟨s7, hwG, hl1_7, hl2_7, hl3_7, hl4_7, hl6_7, hl11_7, hS7ro, hSm, hblk0,
    fun hG0 j hj => by
      show s7.mem j = s6.mem j
      rw [show s7.mem = sGeo.mem from rfl]
      exact hUnt0 hG0 j hj⟩

theorem ni_bmp_header_prelude_ok_exs (s6 : State) (d : List UInt8) (bd : Nat) (hm : s6.mem bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hd : 54 ≤ d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : s6.mem 3 = some obl) (h48 : obl.length = 48)
    (hS6ro : s6.ro = false)
    (hSig : sigOk size d = true) (hLayout : layoutOk size d = true)
    (hl0 : s6.locals 0 = some (.ptr bd 0))
    (hl2 : s6.locals 2 = some (.ptr 3 0))
    (hl1 : s6.locals 1 = some (.int ⟨64, false⟩ size))
    (hl3 : s6.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)))
    (hl4 : s6.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)))
    (hl6 : s6.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46)))
    (hG0 : bmpGeometryCode d = 0) :
    ∃ g : List UInt8, ∃ s12 : State,
      ExS Gen.prog s6 ni_bmp_header_prelude_stmt .normal s12 ∧
      g.length = 48 ∧ s12.mem 3 = some g ∧
      (NANO.toInt32 (rd32le d 22)).natAbs ≤ 2147483648 ∧
      rd32le d 18 ≤ 2147483647 ∧ rd16le d 28 ≤ 32 ∧ (if rd16le d 28 = 32 then 4 else 3) ≤ 4 ∧
      s12.locals 1 = some (.int ⟨64, false⟩ size) ∧
      s12.locals 2 = some (.ptr 3 0) ∧
      s12.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)) ∧
      s12.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)) ∧
      s12.locals 5 = some (.int ⟨16, false⟩ (rd16le d 28)) ∧
      s12.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46)) ∧
      s12.locals 7 = some (.int ⟨32, false⟩ (rd32le d 18)) ∧
      s12.locals 8 = some (.int ⟨32, false⟩ ((NANO.toInt32 (rd32le d 22)).natAbs)) ∧
      s12.locals 9 = some (.int ⟨8, false⟩ (if rd16le d 28 = 32 then 4 else 3)) ∧
      s12.locals 10 = some (.int ⟨8, false⟩ (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)) ∧
      s12.ro = false ∧
      (∀ j, j ≠ 3 → s12.mem j = s6.mem j) := by
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  obtain ⟨s7, hwG, hl1_7, hl2_7, hl3_7, hl4_7, hl6_7, hl11_7, hS7ro, hSm, hMem, hUntG⟩ :=
    ni_bmp_header_geom_call_exs s6 d bd hm size hs hd hlen obl hob h48 hS6ro hl0 hl2 hl1 hl3 hl4 hl6
  have hNot16F : EvE Gen.prog s7
      (.bin .ne (some ⟨32, true⟩) (.var 11) (.const (.int ⟨32, true⟩ 0))) (boolVal false) := by
    have hDec : (decide (IntTy.toInt ⟨32, true⟩ (bmpGeometryCode d) ≠ IntTy.toInt ⟨32, true⟩ 0)) = false := by
      rw [hG0]; decide
    have hNot11 : EvE Gen.prog s7
        (.bin .ne (some ⟨32, true⟩) (.var 11) (.const (.int ⟨32, true⟩ 0)))
        (boolVal (decide (IntTy.toInt ⟨32, true⟩ (bmpGeometryCode d) ≠ IntTy.toInt ⟨32, true⟩ 0))) :=
      EvE.bin (EvE.var hl11_7) (EvE.const _) (bin_i32_ne _ _)
    rw [hDec] at hNot11
    exact hNot11
  have hGeSkip : ExS Gen.prog s7
      (.ite (.bin .ne (some ⟨32, true⟩) (.var 11) (.const (.int ⟨32, true⟩ 0))) (.ret (some (.var 11))) .skip) .normal s7 :=
    ExS.ite hNot16F truthy_false ExS.skip
  have hmax : rd32le d 22 ≤ 4294967295 := by have := rd32_lt d 22; omega
  have hIntmin : NANO.toInt32 (rd32le d 22) ≠ -2147483648 := by
    intro hInt
    have hcode : bmpGeometryCode d = 4 := by
      unfold bmpGeometryCode
      by_cases h1 : NANO.toInt32 (rd32le d 18) ≤ 0 ∨ NANO.toInt32 (rd32le d 22) = 0 ∨ rd16le d 26 ≠ 1
      · have he : bmpGeometryCode d = 3 := by unfold bmpGeometryCode; rw [ite_eq_left h1]
        rw [he] at hG0; exact absurd hG0 (by decide)
      · rw [ite_eq_right h1, ite_eq_left (by omega : NANO.toInt32 (rd32le d 22) < 0), ite_eq_left hInt]
    rw [hcode] at hG0; exact absurd hG0 (by decide)
  have toInt32_eq : ∀ n : Nat, NANO.toInt32 n = if n ≥ 2147483648 then (n : Int) - 4294967296 else (n : Int) := by
    intro n; rfl
  have toInt32_lt : ∀ n : Nat, n < 2147483648 → NANO.toInt32 n = (n : Int) := by
    intro n h; rw [toInt32_eq, ite_eq_right (by omega : ¬ (n ≥ 2147483648))]
  have toInt32_ge : ∀ n : Nat, 2147483648 ≤ n → NANO.toInt32 n = (n : Int) - 4294967296 := by
    intro n h; rw [toInt32_eq, ite_eq_left h]
  have h2blk : s7.mem 3 = some (geomOutBlock obl d) := hMem hG0
  have hblk : s7.mem 3 = some (bmpTailBlock obl (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)) := by
    rw [h2blk]
    by_cases hNeg : NANO.toInt32 (rd32le d 22) < 0
    · rw [geomOutBlock_neg_normal obl d hNeg hIntmin]
      have hge : rd32le d 22 ≥ 2147483648 := by
        by_cases hge : rd32le d 22 ≥ 2147483648
        · exact hge
        · have h2 : NANO.toInt32 (rd32le d 22) = (rd32le d 22 : Int) := toInt32_lt _ (by omega)
          omega
      have hn : (IntTy.wrap ⟨32, true⟩ (-(IntTy.toInt ⟨32, true⟩ (rd32le d 22)))) =
          (NANO.toInt32 (rd32le d 22)).natAbs := by
        rw [wrap_neg_eq_neg hge (by have := rd32_lt d 22; omega)]
        rw [toInt32_ge _ hge, toInt_ge_of_ge hge]
      rw [hn, ite_eq_left hNeg]
    · have hnotNeg : ¬ NANO.toInt32 (rd32le d 22) < 0 := hNeg
      have hge' : (NANO.toInt32 (rd32le d 22) : Int) ≥ 0 := by
        by_cases hge : rd32le d 22 ≥ 2147483648
        · exfalso
          have h2 : NANO.toInt32 (rd32le d 22) = (rd32le d 22 : Int) - 4294967296 := toInt32_ge _ hge
          have h3 : (NANO.toInt32 (rd32le d 22) : Int) < 0 := by rw [h2]; omega
          exact hNeg h3
        · rw [toInt32_lt _ (by omega)]; omega
      rw [geomOutBlock_pos obl d hge']
      have hbound : rd32le d 22 < 2147483648 := by
        by_cases hge : rd32le d 22 ≥ 2147483648
        · have h2 : NANO.toInt32 (rd32le d 22) = (rd32le d 22 : Int) - 4294967296 := toInt32_ge _ hge
          have h3 : (NANO.toInt32 (rd32le d 22) : Int) < 0 := by rw [h2]; omega
          exact absurd h3 (by omega)
        · omega
      have hn : (NANO.toInt32 (rd32le d 22)).natAbs = rd32le d 22 := by
        rw [toInt32_lt _ (by omega), Int.natAbs_natCast]
      rw [hn]
      have hZero : (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0) = 0 := by
        rw [toInt32_lt _ hbound, ite_eq_right (by omega)]
      rw [hZero]
  let gout : List UInt8 := bmpTailBlock obl (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)
  have hob' : s7.mem 3 = some gout := hblk
  have hg_len : gout.length = 48 :=
    bmpTailBlock_length obl h48 (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)
  have hW24 : (gout.drop 24).take 4 = encodeLE 4 (rd32le d 18) :=
    bmpTailBlock_slice24 obl h48 (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)
  have hH28 : (gout.drop 28).take 4 = encodeLE 4 ((NANO.toInt32 (rd32le d 22)).natAbs) :=
    bmpTailBlock_slice28 obl h48 (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)
  have hB40 : (gout.drop 40).take 2 = encodeLE 2 (rd16le d 28) :=
    bmpTailBlock_slice40 obl h48 (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)
  have hC42 : (gout.drop 42).take 1 = encodeLE 1 (if rd16le d 28 = 32 then 4 else 3) :=
    bmpTailBlock_slice42 obl h48 (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)
  have hT43 : (gout.drop 43).take 1 = encodeLE 1 (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0) :=
    bmpTailBlock_slice43 obl h48 (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)
  have hTopD : (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0) < 256 := by
    by_cases h : NANO.toInt32 (rd32le d 22) < 0 <;> simp [h]
  -- ========== geometry bounds ==========
  have hHb : (NANO.toInt32 (rd32le d 22)).natAbs ≤ 2147483648 := height_bound_of_geomOk d hG0
  have hWle : rd32le d 18 ≤ 2147483647 := by
    by_cases hge : rd32le d 18 ≥ 2147483648
    · have he : NANO.toInt32 (rd32le d 18) ≤ -1 := by
        simp [NANO.toInt32, hge]
        have hmax : rd32le d 18 ≤ 4294967295 := by have := rd32_lt d 18; omega
        omega
      have h3 : bmpGeometryCode d = 3 := by
        unfold bmpGeometryCode
        rw [ite_eq_left (Or.inl (by omega))]
      rw [h3] at hG0
      exact absurd hG0 (by decide)
    · omega
  have hBl : rd16le d 28 ≤ 32 := by
    have hbs := rd16le28_in_set_of_geomOk d hG0
    cases hbs with
    | inl h8 => omega
    | inr h => cases h with
      | inl h24 => omega
      | inr h32 => omega
  have hCh : (if rd16le d 28 = 32 then 4 else 3) ≤ 4 := channels_le_4 (rd16le d 28)
  have hBl16 : rd16le d 28 ≤ 65535 := by
    have := rd16le_lt d 28
    omega
  -- ========== loads (each as a separate theorem) ==========
  have hl2s7 : s7.locals 2 = some (.ptr 3 0) := hl2_7
  obtain ⟨s8, hW, hW1, hW2, hW3, hW4, hW5, hW6, hW7, hW9, hW10, hWMem, hW8, hWRo⟩ :=
    ni_bmp_header_load_width_exs d s7 gout hg_len hob' hW24 hl2s7
  have hl2s8 : s8.locals 2 = some (.ptr 3 0) := by rw [hW2]; exact hl2s7
  obtain ⟨s9, hH, hH1, hH2, hH3, hH4, hH5, hH6, hH7, hH9, hH10, hHMem, hH8, hHRo⟩ :=
    ni_bmp_header_load_height_exs d s8 gout hg_len (by rw [hWMem]; exact hob') hH28
      (show ((NANO.toInt32 (rd32le d 22)).natAbs) ≤ 4294967295 from by have := hHb; omega)
      hl2s8
  have hl2s9 : s9.locals 2 = some (.ptr 3 0) := by rw [hH2, hW2]; exact hl2s7
  obtain ⟨s10, hB, hB1, hB2, hB3, hB4, hB6, hB7, hB8, hB9, hB10, hB5, hBMem, hBRo⟩ :=
    ni_bmp_header_load_bitCount_exs d s9 gout hg_len (by rw [hHMem, hWMem]; exact hob') hB40 hl2s9
  have hl2s10 : s10.locals 2 = some (.ptr 3 0) := by rw [hB2, hH2, hW2]; exact hl2s7
  obtain ⟨s11, hC, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC10, hC9, hCMem, hCRo⟩ :=
    ni_bmp_header_load_channels_exs d s10 gout hg_len (by rw [hBMem, hHMem, hWMem]; exact hob') hC42 hl2s10
  have hl2s11 : s11.locals 2 = some (.ptr 3 0) := by rw [hC2, hB2, hH2, hW2]; exact hl2s7
  obtain ⟨s12, hT, hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9, hT10, hTMem, hTRo⟩ :=
    ni_bmp_header_load_topDown_exs d s11 gout hg_len (by rw [hCMem, hBMem, hHMem, hWMem]; exact hob') hT43 hTopD hl2s11
  -- thread locals through the opaque chain
  have hl1_12 : s12.locals 1 = some (.int ⟨64, false⟩ size) := by
    rw [hT1, hC1, hB1, hH1, hW1, hl1_7]
  have hl2_12 : s12.locals 2 = some (.ptr 3 0) := by
    rw [hT2, hC2, hB2, hH2, hW2]; exact hl2s7
  have hl3_12 : s12.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)) := by
    rw [hT3, hC3, hB3, hH3, hW3, hl3_7]
  have hl4_12 : s12.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)) := by
    rw [hT4, hC4, hB4, hH4, hW4, hl4_7]
  have hl5_12 : s12.locals 5 = some (.int ⟨16, false⟩ (rd16le d 28)) := by
    rw [hT5, hC5, hB5]
  have hl6_12 : s12.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46)) := by
    rw [hT6, hC6, hB6, hH6, hW6, hl6_7]
  have hl7_12 : s12.locals 7 = some (.int ⟨32, false⟩ (rd32le d 18)) := by
    rw [hT7, hC7, hB7, hH7, hW7]
  have hl8_12 : s12.locals 8 = some (.int ⟨32, false⟩ ((NANO.toInt32 (rd32le d 22)).natAbs)) := by
    rw [hT8, hC8, hB8, hH8]
  have hl9_12 : s12.locals 9 = some (.int ⟨8, false⟩ (if rd16le d 28 = 32 then 4 else 3)) := by
    rw [hT9, hC9]
  have hl10_12 : s12.locals 10 = some (.int ⟨8, false⟩ (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)) := hT10
  have hob'12 : s12.mem 3 = some gout := by
    rw [hTMem, hCMem, hBMem, hHMem, hWMem]; exact hob'
  have hS12ro : s12.ro = false := by
    rw [hTRo, hCRo, hBRo, hHRo, hWRo, hS7ro]

  refine ⟨gout, s12, ?_, hg_len, hob'12, hHb, hWle, hBl, hCh,
    hl1_12, hl2_12, hl3_12, hl4_12, hl5_12, hl6_12, hl7_12, hl8_12, hl9_12, hl10_12, hS12ro,
    fun j hj => by
      rw [show s12.mem = s7.mem from by rw [hTMem, hCMem, hBMem, hHMem, hWMem]]
      exact hUntG hG0 j hj⟩
  exact ExS.seq hwG (ExS.seq hGeSkip (ExS.seq hW (ExS.seq hH (ExS.seq hB (ExS.seq hC hT)))))

/-- The `ni_bmp_header_palette` call itself, exposing the final state facts
    so the caller can compose gates and stores afterwards. -/
theorem ni_bmp_header_palette_call_exs (s13 : State) (d : List UInt8)
    (gout : List UInt8) (hg_len : gout.length = 48)
    (hAblkEq : s13.mem 3 = some (bmpArithBlock gout
        (bmpRowStride (rd32le d 18) (rd16le d 28))
        (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3) ((NANO.toInt32 (rd32le d 22)).natAbs))))
    (hBkLen : (bmpArithBlock gout
        (bmpRowStride (rd32le d 18) (rd16le d 28))
        (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3) ((NANO.toInt32 (rd32le d 22)).natAbs))).length = 48)
    (s13ro : s13.ro = false)
    (hl5_13 : s13.locals 5 = some (.int ⟨16, false⟩ (rd16le d 28)))
    (hl6_13 : s13.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46)))
    (hl4_13 : s13.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)))
    (hl3_13 : s13.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)))
    (hl2_13 : s13.locals 2 = some (.ptr 3 0))
    (hl7_13 : s13.locals 7 = some (.int ⟨32, false⟩ (rd32le d 18)))
    (hl8_13 : s13.locals 8 = some (.int ⟨32, false⟩ ((NANO.toInt32 (rd32le d 22)).natAbs)))
    (hl9_13 : s13.locals 9 = some (.int ⟨8, false⟩ (if rd16le d 28 = 32 then 4 else 3)))
    (hl10_13 : s13.locals 10 = some (.int ⟨8, false⟩ (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0))) :
    ∃ s14, ExS Gen.prog s13
      (.call (some 13) 18 [(.var 5), (.var 6), (.var 4), (.var 3), (.var 2)]) .normal s14 ∧
      s14.locals 1 = s13.locals 1 ∧ s14.locals 2 = s13.locals 2 ∧
      s14.locals 3 = s13.locals 3 ∧ s14.locals 4 = s13.locals 4 ∧ s14.locals 5 = s13.locals 5 ∧
      s14.locals 6 = s13.locals 6 ∧ s14.locals 7 = s13.locals 7 ∧ s14.locals 8 = s13.locals 8 ∧
      s14.locals 9 = s13.locals 9 ∧ s14.locals 10 = s13.locals 10 ∧
      s14.locals 13 = some (.int ⟨32, true⟩
        (bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10))) ∧
      s14.ro = false ∧
      (∀ (hPcr0 : bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10) = 0),
        s14.mem 3 = some (bmpPaletteBlock (bmpArithBlock gout
          (bmpRowStride (rd32le d 18) (rd16le d 28))
          (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3) ((NANO.toInt32 (rd32le d 22)).natAbs)))
          (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
          (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0))) ∧
      (∀ (hPcr0 : bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10) = 0),
        ∀ j, j ≠ 3 → s14.mem j = s13.mem j) := by
  obtain ⟨sP, exP, hPblk, hPUnt⟩ := ni_bmp_header_palette_exs s13.mem
    (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10)
    (rd16le_lt d 28) (rd32_lt d 46) (rd32_lt d 14) (rd32_lt d 10)
    (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28))
      (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3) ((NANO.toInt32 (rd32le d 22)).natAbs)))
    hAblkEq hBkLen s13.ro s13ro
  have hw5_13 : EvE Gen.prog s13 (.var 5) (.int ⟨16, false⟩ (rd16le d 28)) :=
    EvE.var hl5_13
  have hw6_13 : EvE Gen.prog s13 (.var 6) (.int ⟨32, false⟩ (rd32le d 46)) :=
    EvE.var hl6_13
  have hw4_13 : EvE Gen.prog s13 (.var 4) (.int ⟨32, false⟩ (rd32le d 14)) :=
    EvE.var hl4_13
  have hp3_13 : EvE Gen.prog s13 (.var 3) (.int ⟨32, false⟩ (rd32le d 10)) :=
    EvE.var hl3_13
  have hp2_13 : EvE Gen.prog s13 (.var 2) (.ptr 3 0) :=
    EvE.var hl2_13
  have hCallP : ExS Gen.prog s13
      (.call (some 13) 18 [(.var 5), (.var 6), (.var 4), (.var 3), (.var 2)]) .normal
      { s13 with locals := s13.locals.upd 13 (.int ⟨32, true⟩
          (bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10))), mem := sP.mem, ro := s13.ro } :=
    ExS.call_dst
      (EvArgs.cons hw5_13 (EvArgs.cons hw6_13 (EvArgs.cons hw4_13 (EvArgs.cons hp3_13 (EvArgs.cons hp2_13 EvArgs.nil)))))
      (show Gen.prog 18 = some Gen.ni_bmp_header_palette from rfl)
      (show Gen.ni_bmp_header_palette.params.length = 5 from rfl)
      exP
  let s14 : State := { s13 with locals := s13.locals.upd 13 (.int ⟨32, true⟩
      (bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10))), mem := sP.mem, ro := s13.ro }
  have hS14ro : s14.ro = false := by rw [show s14.ro = s13.ro from rfl]; exact s13ro
  have hl13 : s14.locals 13 = some (.int ⟨32, true⟩
      (bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10))) := rfl
  have hl1_14 : s14.locals 1 = s13.locals 1 := rfl
  have hl2_14 : s14.locals 2 = s13.locals 2 := rfl
  have hl3_14 : s14.locals 3 = s13.locals 3 := rfl
  have hl4_14 : s14.locals 4 = s13.locals 4 := rfl
  have hl5_14 : s14.locals 5 = s13.locals 5 := rfl
  have hl6_14 : s14.locals 6 = s13.locals 6 := rfl
  have hl7_14 : s14.locals 7 = s13.locals 7 := rfl
  have hl8_14 : s14.locals 8 = s13.locals 8 := rfl
  have hl9_14 : s14.locals 9 = s13.locals 9 := rfl
  have hl10_14 : s14.locals 10 = s13.locals 10 := rfl
  exact ⟨s14, hCallP, hl1_14, hl2_14, hl3_14, hl4_14, hl5_14, hl6_14, hl7_14, hl8_14, hl9_14, hl10_14, hl13, hS14ro, hPblk,
    fun hPcr0 j hj => by
      show s14.mem j = s13.mem j
      rw [show s14.mem = sP.mem from rfl]
      exact hPUnt hPcr0 j hj⟩

theorem ni_bmp_header_rem_geom_fail_exs (s6 : State) (d : List UInt8) (bd : Nat) (hm : s6.mem bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hd : 54 ≤ d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : s6.mem 3 = some obl) (h48 : obl.length = 48)
    (hS6ro : s6.ro = false)
    (hSig : sigOk size d = true) (hLayout : layoutOk size d = true)
    (hl0 : s6.locals 0 = some (.ptr bd 0))
    (hl2 : s6.locals 2 = some (.ptr 3 0))
    (hl1 : s6.locals 1 = some (.int ⟨64, false⟩ size))
    (hl3 : s6.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)))
    (hl4 : s6.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)))
    (hl6 : s6.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46)))
    (hG0 : bmpGeometryCode d ≠ 0) :
    ∃ s', ExS Gen.prog s6 ni_bmp_header_rem_stmt (.ret (some (.int ⟨32, true⟩ (bmpHeaderCode size d)))) s' := by
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  obtain ⟨s7, hwG, hl1_7, hl2_7, hl3_7, hl4_7, hl6_7, hl11_7, hS7ro, hSm, hMem, _⟩ :=
    ni_bmp_header_geom_call_exs s6 d bd hm size hs hd hlen obl hob h48 hS6ro hl0 hl2 hl1 hl3 hl4 hl6
  have hG' : bmpGeometryCode d ≠ 0 := hG0
  have hNot16T : EvE Gen.prog s7
      (.bin .ne (some ⟨32, true⟩) (.var 11) (.const (.int ⟨32, true⟩ 0))) (boolVal true) := by
    have hBnd : bmpGeometryCode d ≤ 2147483647 := by omega
    have hDec : (decide (IntTy.toInt ⟨32, true⟩ (bmpGeometryCode d) ≠ IntTy.toInt ⟨32, true⟩ 0)) = true := by
      rw [decide_eq_true_eq]
      have h2 : ¬ 2147483648 ≤ bmpGeometryCode d := by omega
      have e1 : IntTy.toInt ⟨32, true⟩ (bmpGeometryCode d) = (bmpGeometryCode d : Int) := by
        simp [IntTy.toInt, h2]
      have e2 : IntTy.toInt ⟨32, true⟩ 0 = (0 : Int) := by simp [IntTy.toInt]
      rw [e1, e2]
      omega
    have hNot11 : EvE Gen.prog s7
        (.bin .ne (some ⟨32, true⟩) (.var 11) (.const (.int ⟨32, true⟩ 0)))
        (boolVal (decide (IntTy.toInt ⟨32, true⟩ (bmpGeometryCode d) ≠ IntTy.toInt ⟨32, true⟩ 0))) :=
      EvE.bin (EvE.var hl11_7) (EvE.const _) (bin_i32_ne _ _)
    rw [hDec] at hNot11
    exact hNot11
  have hbvG : bmpHeaderCode size d = bmpGeometryCode d := by
    unfold bmpHeaderCode
    have hSigOk : bmpSigGate size d = .ok () := bmpSigGate_ok_of_sigOk size d hSig
    have hLayOk : bmpLayoutGate size d = .ok () := bmpLayoutGate_ok_of_layoutOk size d hLayout
    have hGeo : bmpGeometryStage size d = .error (bmpGeometryCode d) :=
      bmpGeometryStage_eq_of_ne_zero size d hG'
    unfold bmpHeader
    rw [hSigOk]
    simp only [bind_ok_of_ok]
    rw [hLayOk]
    simp only [bind_ok_of_ok]
    rw [hGeo]
    simp only [bind_error_of_error_l]
  refine ⟨s7, ?_⟩
  show ExS Gen.prog s6 ni_bmp_header_rem_stmt (.ret (some (.int ⟨32, true⟩ (bmpHeaderCode size d)))) s7
  rw [hbvG]
  exact ExS.seq_ret (ExS.seq hwG (ExS.seq_ret (ExS.ite hNot16T truthy_true (ExS.ret (EvE.var hl11_7)))))

theorem ni_bmp_header_rem_arith_fail_exs (s6 : State) (d : List UInt8) (bd : Nat) (hm : s6.mem bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hd : 54 ≤ d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : s6.mem 3 = some obl) (h48 : obl.length = 48)
    (hS6ro : s6.ro = false)
    (hSig : sigOk size d = true) (hLayout : layoutOk size d = true)
    (hl0 : s6.locals 0 = some (.ptr bd 0))
    (hl2 : s6.locals 2 = some (.ptr 3 0))
    (hl1 : s6.locals 1 = some (.int ⟨64, false⟩ size))
    (hl3 : s6.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)))
    (hl4 : s6.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)))
    (hl6 : s6.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46)))
    (hG0 : bmpGeometryCode d = 0)
    (hAcr : ¬ (bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
        (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size) = 0) :
    ∃ s', ExS Gen.prog s6 ni_bmp_header_rem_stmt (.ret (some (.int ⟨32, true⟩ (bmpHeaderCode size d)))) s' := by
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  obtain ⟨gout, s12, hP, hg_len, hob'12, hHb, hWle, hBl, hCh,
    hl1_12, hl2_12, hl3_12, hl4_12, hl5_12, hl6_12, hl7_12, hl8_12, hl9_12, hl10_12, hS12ro, hPreUnt⟩ :=
    ni_bmp_header_prelude_ok_exs s6 d bd hm size hs hd hlen obl hob h48 hS6ro hSig hLayout hl0 hl2 hl1 hl3 hl4 hl6 hG0
  -- ========== arith call ==========
  obtain ⟨sA, exA, hAblk, hAUnt⟩ := ni_bmp_header_arith_exs s12.mem
    (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3)
    (rd32le d 10) size
    (rd32_lt d 18) (by omega) (rd16le_lt d 28) (by omega) (rd32_lt d 10) (by omega)
    gout hob'12 hg_len s12.ro hS12ro
  have hw7 : EvE Gen.prog s12 (.var 7) (.int ⟨32, false⟩ (rd32le d 18)) :=
    EvE.var hl7_12
  have hw8 : EvE Gen.prog s12 (.var 8) (.int ⟨32, false⟩ ((NANO.toInt32 (rd32le d 22)).natAbs)) :=
    EvE.var hl8_12
  have hb5 : EvE Gen.prog s12 (.var 5) (.int ⟨16, false⟩ (rd16le d 28)) :=
    EvE.var hl5_12
  have hc9 : EvE Gen.prog s12 (.var 9) (.int ⟨8, false⟩ (if rd16le d 28 = 32 then 4 else 3)) :=
    EvE.var hl9_12
  have hp3 : EvE Gen.prog s12 (.var 3) (.int ⟨32, false⟩ (rd32le d 10)) :=
    EvE.var hl3_12
  have hsz1 : EvE Gen.prog s12 (.var 1) (.int ⟨64, false⟩ size) :=
    EvE.var hl1_12
  have hp2 : EvE Gen.prog s12 (.var 2) (.ptr 3 0) :=
    EvE.var hl2_12
  have hCallA : ExS Gen.prog s12
      (.call (some 12) 17 [(.var 7), (.var 8), (.var 5), (.var 9), (.var 3), (.var 1), (.var 2)]) .normal
      { s12 with locals := s12.locals.upd 12 (.int ⟨32, true⟩
          (bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
            (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size)), mem := sA.mem, ro := s12.ro } :=
    ExS.call_dst
      (EvArgs.cons hw7 (EvArgs.cons hw8 (EvArgs.cons hb5 (EvArgs.cons hc9 (EvArgs.cons hp3
        (EvArgs.cons hsz1 (EvArgs.cons hp2 EvArgs.nil)))))))
      (show Gen.prog 17 = some Gen.ni_bmp_header_arith from rfl)
      (show Gen.ni_bmp_header_arith.params.length = 7 from rfl)
      exA
  let s13 : State := { s12 with locals := s12.locals.upd 12 (.int ⟨32, true⟩
      (bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
        (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size)), mem := sA.mem, ro := s12.ro }
  have hS13ro : s13.ro = false := by rw [show s13.ro = s12.ro from rfl]; exact hS12ro
  have hl12 : s13.locals 12 = some (.int ⟨32, true⟩
      (bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
        (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size)) := rfl
  have hl2_13 : s13.locals 2 = some (.ptr 3 0) := by
    rw [show s13.locals 2 = s12.locals 2 from rfl, hl2_12]
  have hl3_13 : s13.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)) := by
    rw [show s13.locals 3 = s12.locals 3 from rfl, hl3_12]
  have hl4_13 : s13.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)) := by
    rw [show s13.locals 4 = s12.locals 4 from rfl, hl4_12]
  have hl6_13 : s13.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46)) := by
    rw [show s13.locals 6 = s12.locals 6 from rfl, hl6_12]
  have hl5_13 : s13.locals 5 = some (.int ⟨16, false⟩ (rd16le d 28)) := by
    rw [show s13.locals 5 = s12.locals 5 from rfl, hl5_12]
  have hl7_13 : s13.locals 7 = some (.int ⟨32, false⟩ (rd32le d 18)) := by
    rw [show s13.locals 7 = s12.locals 7 from rfl, hl7_12]
  have hl8_13 : s13.locals 8 = some (.int ⟨32, false⟩ ((NANO.toInt32 (rd32le d 22)).natAbs)) := by
    rw [show s13.locals 8 = s12.locals 8 from rfl, hl8_12]
  have hl9_13 : s13.locals 9 = some (.int ⟨8, false⟩ (if rd16le d 28 = 32 then 4 else 3)) := by
    rw [show s13.locals 9 = s12.locals 9 from rfl, hl9_12]
  have hl10_13 : s13.locals 10 = some (.int ⟨8, false⟩ (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)) := by
    rw [show s13.locals 10 = s12.locals 10 from rfl, hl10_12]
  have hA9 : (bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
      (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size) = 9 := by
    rcases (arithCode_zero_or_nine (show rd32le d 18 ≤ 2147483647 from hWle) hBl hCh hHb) with h0 | h9
    · exact absurd h0 hAcr
    · exact h9
  have h9v : s13.locals 12 = some (.int ⟨32, true⟩ 9) := by rw [hl12, hA9]
  have hSpec : bmpHeaderCode size d = 9 := by
    apply bmpHeaderCode_nine_of_trunc size d hSig hLayout hG0
    have hU := @arithCode_unfold (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size hWle hBl hCh hHb
    rw [hA9] at hU
    by_cases hbad : rd32le d 10 > sizeMax - bmpRowStride (rd32le d 18) (rd16le d 28) * ((NANO.toInt32 (rd32le d 22)).natAbs) ∨
        rd32le d 10 + bmpRowStride (rd32le d 18) (rd16le d 28) * ((NANO.toInt32 (rd32le d 22)).natAbs) > size
    · have hconv : specRowStride (rd32le d 18) (rd16le d 28) = bmpRowStride (rd32le d 18) (rd16le d 28) := rfl
      rw [hconv]
      exact hbad
    · rw [ite_eq_right hbad] at hU
      exact absurd hU (by decide)
  have h12ne : EvE Gen.prog s13
      (.bin .ne (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 0)))
      (boolVal true) := by
    have e : EvE Gen.prog s13
        (.bin .ne (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 0)))
        (boolVal (decide (IntTy.toInt ⟨32, true⟩ (bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
          (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size) ≠ IntTy.toInt ⟨32, true⟩ 0))) :=
      EvE.bin (EvE.var hl12) (EvE.const _) (bin_i32_ne _ _)
    rw [hA9] at e
    rw [show (decide (IntTy.toInt ⟨32, true⟩ 9 ≠ IntTy.toInt ⟨32, true⟩ 0)) = true from by decide] at e
    exact e
  have hRet12 : ExS Gen.prog s13
      (.ite (.bin .ne (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 0)))
        (Stmt.ret (some (Expr.var 12))) .skip)
      (Outcome.ret (some (.int ⟨32, true⟩ 9))) s13 :=
    ExS.ite h12ne truthy_true (ExS.ret (EvE.var h9v))
  refine ⟨s13, ?_⟩
  show ExS Gen.prog s6 ni_bmp_header_rem_stmt (.ret (some (.int ⟨32, true⟩ (bmpHeaderCode size d)))) s13
  rw [hSpec]
  exact ExS.seq hP (ExS.seq_ret (ExS.seq hCallA hRet12))



theorem ni_bmp_header_rem_stores_exs (s6 : State) (d : List UInt8) (bd : Nat) (hm : s6.mem bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hd : 54 ≤ d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : s6.mem 3 = some obl) (h48 : obl.length = 48)
    (hS6ro : s6.ro = false)
    (hSig : sigOk size d = true) (hLayout : layoutOk size d = true)
    (hl0 : s6.locals 0 = some (.ptr bd 0))
    (hl2 : s6.locals 2 = some (.ptr 3 0))
    (hl1 : s6.locals 1 = some (.int ⟨64, false⟩ size))
    (hl3 : s6.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)))
    (hl4 : s6.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)))
    (hl6 : s6.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46)))
    (hG0 : bmpGeometryCode d = 0)
    (hAcr : bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
        (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size = 0)
    (hPcr : bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10) = 0) :
    ∃ s', ExS Gen.prog s6 ni_bmp_header_rem_stmt (.ret (some (.int ⟨32, true⟩ (bmpHeaderCode size d)))) s' ∧
      (∃ gout, s'.mem 3 = some (bmpHeaderFinalBlock d gout) ∧ gout.length = 48) ∧
      (∀ j, j ≠ 3 → s'.mem j = s6.mem j) := by
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  obtain ⟨gout, s12, hP, hg_len, hob'12, hHb, hWle, hBl, hCh,
    hl1_12, hl2_12, hl3_12, hl4_12, hl5_12, hl6_12, hl7_12, hl8_12, hl9_12, hl10_12, hS12ro, hPreUnt⟩ :=
    ni_bmp_header_prelude_ok_exs s6 d bd hm size hs hd hlen obl hob h48 hS6ro hSig hLayout hl0 hl2 hl1 hl3 hl4 hl6 hG0
  obtain ⟨sA, exA, hAblk, hAUnt⟩ := ni_bmp_header_arith_exs s12.mem
    (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3)
    (rd32le d 10) size
    (rd32_lt d 18) (by omega) (rd16le_lt d 28) (by omega) (rd32_lt d 10) (by omega)
    gout hob'12 hg_len s12.ro hS12ro
  have hw7 : EvE Gen.prog s12 (.var 7) (.int ⟨32, false⟩ (rd32le d 18)) :=
    EvE.var hl7_12
  have hw8 : EvE Gen.prog s12 (.var 8) (.int ⟨32, false⟩ ((NANO.toInt32 (rd32le d 22)).natAbs)) :=
    EvE.var hl8_12
  have hb5 : EvE Gen.prog s12 (.var 5) (.int ⟨16, false⟩ (rd16le d 28)) :=
    EvE.var hl5_12
  have hc9 : EvE Gen.prog s12 (.var 9) (.int ⟨8, false⟩ (if rd16le d 28 = 32 then 4 else 3)) :=
    EvE.var hl9_12
  have hp3 : EvE Gen.prog s12 (.var 3) (.int ⟨32, false⟩ (rd32le d 10)) :=
    EvE.var hl3_12
  have hsz1 : EvE Gen.prog s12 (.var 1) (.int ⟨64, false⟩ size) :=
    EvE.var hl1_12
  have hp2 : EvE Gen.prog s12 (.var 2) (.ptr 3 0) :=
    EvE.var hl2_12
  have hCallA : ExS Gen.prog s12
      (.call (some 12) 17 [(.var 7), (.var 8), (.var 5), (.var 9), (.var 3), (.var 1), (.var 2)]) .normal
      { s12 with locals := s12.locals.upd 12 (.int ⟨32, true⟩
          (bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
            (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size)), mem := sA.mem, ro := s12.ro } :=
    ExS.call_dst
      (EvArgs.cons hw7 (EvArgs.cons hw8 (EvArgs.cons hb5 (EvArgs.cons hc9 (EvArgs.cons hp3
        (EvArgs.cons hsz1 (EvArgs.cons hp2 EvArgs.nil)))))))
      (show Gen.prog 17 = some Gen.ni_bmp_header_arith from rfl)
      (show Gen.ni_bmp_header_arith.params.length = 7 from rfl)
      exA
  let s13 : State := { s12 with locals := s12.locals.upd 12 (.int ⟨32, true⟩
      (bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
        (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size)), mem := sA.mem, ro := s12.ro }
  have hS13ro : s13.ro = false := by rw [show s13.ro = s12.ro from rfl]; exact hS12ro
  have hl12 : s13.locals 12 = some (.int ⟨32, true⟩
      (bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
        (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size)) := rfl
  have hl2_13 : s13.locals 2 = some (.ptr 3 0) := by
    rw [show s13.locals 2 = s12.locals 2 from rfl, hl2_12]
  have hl3_13 : s13.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)) := by
    rw [show s13.locals 3 = s12.locals 3 from rfl, hl3_12]
  have hl4_13 : s13.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)) := by
    rw [show s13.locals 4 = s12.locals 4 from rfl, hl4_12]
  have hl6_13 : s13.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46)) := by
    rw [show s13.locals 6 = s12.locals 6 from rfl, hl6_12]
  have hl5_13 : s13.locals 5 = some (.int ⟨16, false⟩ (rd16le d 28)) := by
    rw [show s13.locals 5 = s12.locals 5 from rfl, hl5_12]
  have hl7_13 : s13.locals 7 = some (.int ⟨32, false⟩ (rd32le d 18)) := by
    rw [show s13.locals 7 = s12.locals 7 from rfl, hl7_12]
  have hl8_13 : s13.locals 8 = some (.int ⟨32, false⟩ ((NANO.toInt32 (rd32le d 22)).natAbs)) := by
    rw [show s13.locals 8 = s12.locals 8 from rfl, hl8_12]
  have hl9_13 : s13.locals 9 = some (.int ⟨8, false⟩ (if rd16le d 28 = 32 then 4 else 3)) := by
    rw [show s13.locals 9 = s12.locals 9 from rfl, hl9_12]
  have hl10_13 : s13.locals 10 = some (.int ⟨8, false⟩ (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)) := by
    rw [show s13.locals 10 = s12.locals 10 from rfl, hl10_12]
  have hAblkEq : s13.mem 3 = some (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28)) (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3) ((NANO.toInt32 (rd32le d 22)).natAbs))) :=
    hAblk hAcr
  have hBkLen : (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28)) (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3) ((NANO.toInt32 (rd32le d 22)).natAbs))).length = 48 :=
    bmpArithBlock_length gout hg_len _ _
  obtain ⟨s14, hCallP, h1_14, h2_14, h3_14, h4_14, h5_14, h6_14, h7_14, h8_14, h9_14, h10_14, hl13, hS14ro, hPblk, hPUnt⟩ :=
    ni_bmp_header_palette_call_exs s13 d gout hg_len hAblkEq hBkLen hS13ro
      hl5_13 hl6_13 hl4_13 hl3_13 hl2_13 hl7_13 hl8_13 hl9_13 hl10_13
  have hl2_14 : s14.locals 2 = some (.ptr 3 0) := h2_14.trans hl2_13
  have hl3_14 : s14.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)) := h3_14.trans hl3_13
  have hl5_14 : s14.locals 5 = some (.int ⟨16, false⟩ (rd16le d 28)) := h5_14.trans hl5_13
  have hl7_14 : s14.locals 7 = some (.int ⟨32, false⟩ (rd32le d 18)) := h7_14.trans hl7_13
  have hl8_14 : s14.locals 8 = some (.int ⟨32, false⟩ ((NANO.toInt32 (rd32le d 22)).natAbs)) := h8_14.trans hl8_13
  have hl9_14 : s14.locals 9 = some (.int ⟨8, false⟩ (if rd16le d 28 = 32 then 4 else 3)) := h9_14.trans hl9_13
  have hl10_14 : s14.locals 10 = some (.int ⟨8, false⟩ (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)) := h10_14.trans hl10_13
  have hP010 := paletteCode_zero_or_ten (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10)
  have hNotTrunc : ¬ (rd32le d 10 > sizeMax - bmpRowStride (rd32le d 18) (rd16le d 28) * ((NANO.toInt32 (rd32le d 22)).natAbs) ∨
      rd32le d 10 + bmpRowStride (rd32le d 18) (rd16le d 28) * ((NANO.toInt32 (rd32le d 22)).natAbs) > size) := by
    have hU := @arithCode_unfold (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size hWle hBl hCh hHb
    rw [hAcr] at hU
    intro hbad
    rw [ite_eq_left hbad] at hU
    exact absurd hU (by decide)
  have hOk8 : rd16le d 28 ≠ 8 ∨
      (rd16le d 28 = 8 ∧
        ¬ ((if rd32le d 46 = 0 then 256 else rd32le d 46) = 0 ∨
           (256 < if rd32le d 46 = 0 then 256 else rd32le d 46) ∨
           rd32le d 10 < 14 + rd32le d 14 + (if rd32le d 46 = 0 then 256 else rd32le d 46) * 4)) := by
    by_cases hB8 : rd16le d 28 = 8
    · right
      refine ⟨hB8, ?_⟩
      intro hbad
      have hU := paletteCode_unfold (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10)
      rw [ite_eq_left hB8] at hU
      have hUf : ¬ ((if rd32le d 46 = 0 then 256 else rd32le d 46) = 0 ∨
                    (if rd32le d 46 = 0 then 256 else rd32le d 46) > 256 ∨
                    14 + rd32le d 14 + (if rd32le d 46 = 0 then 256 else rd32le d 46) * 4 > rd32le d 10) := by
        intro hbad'
        rw [ite_eq_left hbad'] at hU
        rw [hPcr] at hU
        exact absurd hU (by decide)
      have hbad' : (if rd32le d 46 = 0 then 256 else rd32le d 46) = 0 ∨
                   (if rd32le d 46 = 0 then 256 else rd32le d 46) > 256 ∨
                   14 + rd32le d 14 + (if rd32le d 46 = 0 then 256 else rd32le d 46) * 4 > rd32le d 10 := by
        rcases hbad with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))
      exact hUf hbad'
    · left; exact hB8
  have hSpec : bmpHeaderCode size d = 0 :=
    bmpHeaderCode_zero_of_ok size d hSig hLayout hG0 hNotTrunc hOk8
  have hBlockFin : s14.mem 3 = some (bmpPaletteBlock (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28))
      (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3) ((NANO.toInt32 (rd32le d 22)).natAbs)))
      (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
      (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0)) :=
    hPblk hPcr
  have hBkLen2 : (bmpPaletteBlock (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28))
      (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3) ((NANO.toInt32 (rd32le d 22)).natAbs)))
      (if rd16le d 28 = 8 then 14 + rd32le d 14 else 0)
      (if rd16le d 28 = 8 then (if rd32le d 46 = 0 then 256 else rd32le d 46) else 0)).length = 48 :=
    bmpPaletteBlock_length _ (bmpArithBlock_length gout hg_len _ _) _ _
  obtain ⟨s', hStores, hStoresMem, hStUnt⟩ := header_stores_exs s14.mem _ hBlockFin hBkLen2 s14.ro hS14ro s14.locals hl2_14
    (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd32le d 10)
    (rd32_lt d 18) (by omega) (rd32_lt d 10)
    (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3) (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)
    (rd16le_lt d 28) (by omega) (by by_cases h : NANO.toInt32 (rd32le d 22) < 0 <;> simp [h]) hl7_14 hl8_14 hl3_14 hl5_14 hl9_14 hl10_14
  refine ⟨s', ?_, ⟨gout, hStoresMem, hg_len⟩, fun j hj => by
    rw [hStUnt j hj, hPUnt hPcr j hj, show s13.mem = sA.mem from rfl]
    rw [hAUnt hAcr j hj, hPreUnt j hj]⟩
  show ExS Gen.prog s6 ni_bmp_header_rem_stmt (.ret (some (.int ⟨32, true⟩ (bmpHeaderCode size d)))) s'
  rw [hSpec]
  have h12skipV12 : EvE Gen.prog s13
      (.bin .ne (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 0)))
      (boolVal false) := by
    have e : EvE Gen.prog s13
        (.bin .ne (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 0)))
        (boolVal (decide (IntTy.toInt ⟨32, true⟩ (bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
          (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size) ≠ IntTy.toInt ⟨32, true⟩ 0))) :=
      EvE.bin (EvE.var hl12) (EvE.const _) (bin_i32_ne _ _)
    rw [hAcr] at e
    rw [show (decide (IntTy.toInt ⟨32, true⟩ 0 ≠ IntTy.toInt ⟨32, true⟩ 0)) = false from by decide] at e
    exact e
  have hTailA : ExS Gen.prog s12
      (.seq (.call (some 12) 17 [(.var 7), (.var 8), (.var 5), (.var 9), (.var 3), (.var 1), (.var 2)])
        (.ite (.bin .ne (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 0))) (.ret (some (.var 12))) .skip))
      .normal s13 :=
    ExS.seq hCallA (ExS.ite h12skipV12 truthy_false ExS.skip)
  have h13skip : EvE Gen.prog s14
      (.bin .ne (some ⟨32, true⟩) (.var 13) (.const (.int ⟨32, true⟩ 0)))
      (boolVal false) := by
    have e : EvE Gen.prog s14
        (.bin .ne (some ⟨32, true⟩) (.var 13) (.const (.int ⟨32, true⟩ 0)))
        (boolVal (decide (IntTy.toInt ⟨32, true⟩ (bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10)) ≠
          IntTy.toInt ⟨32, true⟩ 0))) :=
      EvE.bin (EvE.var hl13) (EvE.const _) (bin_i32_ne _ _)
    rw [hPcr] at e
    rw [show (decide (IntTy.toInt ⟨32, true⟩ 0 ≠ IntTy.toInt ⟨32, true⟩ 0)) = false from by decide] at e
    exact e
  have hRest : ExS Gen.prog s13 ni_bmp_header_rest_stmt (.ret (some (.int ⟨32, true⟩ 0))) s' :=
    ExS.seq (ExS.seq hCallP (ExS.ite h13skip truthy_false ExS.skip)) hStores
  exact ExS.seq hP (ExS.seq hTailA hRest)

theorem ni_bmp_header_rem_palette_bad_exs (s6 : State) (d : List UInt8) (bd : Nat) (hm : s6.mem bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hd : 54 ≤ d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : s6.mem 3 = some obl) (h48 : obl.length = 48)
    (hS6ro : s6.ro = false)
    (hSig : sigOk size d = true) (hLayout : layoutOk size d = true)
    (hl0 : s6.locals 0 = some (.ptr bd 0))
    (hl2 : s6.locals 2 = some (.ptr 3 0))
    (hl1 : s6.locals 1 = some (.int ⟨64, false⟩ size))
    (hl3 : s6.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)))
    (hl4 : s6.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)))
    (hl6 : s6.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46)))
    (hG0 : bmpGeometryCode d = 0)
    (hAcr : bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
        (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size = 0)
    (hPcr : ¬ (bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10) = 0)) :
    ∃ s', ExS Gen.prog s6 ni_bmp_header_rem_stmt (.ret (some (.int ⟨32, true⟩ (bmpHeaderCode size d)))) s' := by
  have truthy_true : truthy (boolVal true) = .ok true := truthy_boolVal true
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  obtain ⟨gout, s12, hP, hg_len, hob'12, hHb, hWle, hBl, hCh,
    hl1_12, hl2_12, hl3_12, hl4_12, hl5_12, hl6_12, hl7_12, hl8_12, hl9_12, hl10_12, hS12ro, hPreUnt⟩ :=
    ni_bmp_header_prelude_ok_exs s6 d bd hm size hs hd hlen obl hob h48 hS6ro hSig hLayout hl0 hl2 hl1 hl3 hl4 hl6 hG0
  obtain ⟨sA, exA, hAblk, hAUnt⟩ := ni_bmp_header_arith_exs s12.mem
    (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3)
    (rd32le d 10) size
    (rd32_lt d 18) (by omega) (rd16le_lt d 28) (by omega) (rd32_lt d 10) (by omega)
    gout hob'12 hg_len s12.ro hS12ro
  have hw7 : EvE Gen.prog s12 (.var 7) (.int ⟨32, false⟩ (rd32le d 18)) :=
    EvE.var hl7_12
  have hw8 : EvE Gen.prog s12 (.var 8) (.int ⟨32, false⟩ ((NANO.toInt32 (rd32le d 22)).natAbs)) :=
    EvE.var hl8_12
  have hb5 : EvE Gen.prog s12 (.var 5) (.int ⟨16, false⟩ (rd16le d 28)) :=
    EvE.var hl5_12
  have hc9 : EvE Gen.prog s12 (.var 9) (.int ⟨8, false⟩ (if rd16le d 28 = 32 then 4 else 3)) :=
    EvE.var hl9_12
  have hp3 : EvE Gen.prog s12 (.var 3) (.int ⟨32, false⟩ (rd32le d 10)) :=
    EvE.var hl3_12
  have hsz1 : EvE Gen.prog s12 (.var 1) (.int ⟨64, false⟩ size) :=
    EvE.var hl1_12
  have hp2 : EvE Gen.prog s12 (.var 2) (.ptr 3 0) :=
    EvE.var hl2_12
  have hCallA : ExS Gen.prog s12
      (.call (some 12) 17 [(.var 7), (.var 8), (.var 5), (.var 9), (.var 3), (.var 1), (.var 2)]) .normal
      { s12 with locals := s12.locals.upd 12 (.int ⟨32, true⟩
          (bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
            (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size)), mem := sA.mem, ro := s12.ro } :=
    ExS.call_dst
      (EvArgs.cons hw7 (EvArgs.cons hw8 (EvArgs.cons hb5 (EvArgs.cons hc9 (EvArgs.cons hp3
        (EvArgs.cons hsz1 (EvArgs.cons hp2 EvArgs.nil)))))))
      (show Gen.prog 17 = some Gen.ni_bmp_header_arith from rfl)
      (show Gen.ni_bmp_header_arith.params.length = 7 from rfl)
      exA
  let s13 : State := { s12 with locals := s12.locals.upd 12 (.int ⟨32, true⟩
      (bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
        (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size)), mem := sA.mem, ro := s12.ro }
  have hS13ro : s13.ro = false := by rw [show s13.ro = s12.ro from rfl]; exact hS12ro
  have hl12 : s13.locals 12 = some (.int ⟨32, true⟩
      (bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
        (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size)) := rfl
  have hl2_13 : s13.locals 2 = some (.ptr 3 0) := by
    rw [show s13.locals 2 = s12.locals 2 from rfl, hl2_12]
  have hl3_13 : s13.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)) := by
    rw [show s13.locals 3 = s12.locals 3 from rfl, hl3_12]
  have hl4_13 : s13.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)) := by
    rw [show s13.locals 4 = s12.locals 4 from rfl, hl4_12]
  have hl6_13 : s13.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46)) := by
    rw [show s13.locals 6 = s12.locals 6 from rfl, hl6_12]
  have hl5_13 : s13.locals 5 = some (.int ⟨16, false⟩ (rd16le d 28)) := by
    rw [show s13.locals 5 = s12.locals 5 from rfl, hl5_12]
  have hl7_13 : s13.locals 7 = some (.int ⟨32, false⟩ (rd32le d 18)) := by
    rw [show s13.locals 7 = s12.locals 7 from rfl, hl7_12]
  have hl8_13 : s13.locals 8 = some (.int ⟨32, false⟩ ((NANO.toInt32 (rd32le d 22)).natAbs)) := by
    rw [show s13.locals 8 = s12.locals 8 from rfl, hl8_12]
  have hl9_13 : s13.locals 9 = some (.int ⟨8, false⟩ (if rd16le d 28 = 32 then 4 else 3)) := by
    rw [show s13.locals 9 = s12.locals 9 from rfl, hl9_12]
  have hl10_13 : s13.locals 10 = some (.int ⟨8, false⟩ (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)) := by
    rw [show s13.locals 10 = s12.locals 10 from rfl, hl10_12]
  have hAblkEq : s13.mem 3 = some (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28)) (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3) ((NANO.toInt32 (rd32le d 22)).natAbs))) :=
    hAblk hAcr
  have hBkLen : (bmpArithBlock gout
      (bmpRowStride (rd32le d 18) (rd16le d 28)) (bmpOutSize (rd32le d 18) (if rd16le d 28 = 32 then 4 else 3) ((NANO.toInt32 (rd32le d 22)).natAbs))).length = 48 :=
    bmpArithBlock_length gout hg_len _ _
  obtain ⟨s14, hCallP, h1_14, h2_14, h3_14, h4_14, h5_14, h6_14, h7_14, h8_14, h9_14, h10_14, hl13, hS14ro, hPblk, hPUnt⟩ :=
    ni_bmp_header_palette_call_exs s13 d gout hg_len hAblkEq hBkLen hS13ro
      hl5_13 hl6_13 hl4_13 hl3_13 hl2_13 hl7_13 hl8_13 hl9_13 hl10_13
  have hl2_14 : s14.locals 2 = some (.ptr 3 0) := h2_14.trans hl2_13
  have hl10_14 : s14.locals 10 = some (.int ⟨8, false⟩ (if NANO.toInt32 (rd32le d 22) < 0 then 1 else 0)) := h10_14.trans hl10_13
  have hP010 := paletteCode_zero_or_ten (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10)
  have hP10 : (bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10)) = 10 := by
    rcases hP010 with h0 | h10
    · exact absurd h0 hPcr
    · exact h10
  have h10v : s14.locals 13 = some (.int ⟨32, true⟩ 10) := by rw [hl13, hP10]
  have hB8 : rd16le d 28 = 8 := by
    by_cases hB8' : rd16le d 28 = 8
    · exact hB8'
    · have hU := paletteCode_unfold (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10)
      rw [ite_eq_right hB8'] at hU
      rw [hP10] at hU
      exact absurd hU (by decide)
  have hEntriesBad : (if rd32le d 46 = 0 then 256 else rd32le d 46) = 0 ∨
      (256 < if rd32le d 46 = 0 then 256 else rd32le d 46) ∨
      rd32le d 10 < 14 + rd32le d 14 + (if rd32le d 46 = 0 then 256 else rd32le d 46) * 4 := by
    have hU := paletteCode_unfold (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10)
    rw [ite_eq_left hB8, hP10] at hU
    have hbad : (if rd32le d 46 = 0 then 256 else rd32le d 46) = 0 ∨
                (if rd32le d 46 = 0 then 256 else rd32le d 46) > 256 ∨
                14 + rd32le d 14 + (if rd32le d 46 = 0 then 256 else rd32le d 46) * 4 > rd32le d 10 := by
      by_cases hbad' : (if rd32le d 46 = 0 then 256 else rd32le d 46) = 0 ∨
                       (if rd32le d 46 = 0 then 256 else rd32le d 46) > 256 ∨
                       14 + rd32le d 14 + (if rd32le d 46 = 0 then 256 else rd32le d 46) * 4 > rd32le d 10
      · exact hbad'
      · rw [ite_eq_right hbad'] at hU
        exact absurd hU (by decide)
    rcases hbad with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (by omega))
  have hNotTrunc : ¬ (rd32le d 10 > sizeMax - bmpRowStride (rd32le d 18) (rd16le d 28) * (NANO.toInt32 (rd32le d 22)).natAbs ∨
      rd32le d 10 + bmpRowStride (rd32le d 18) (rd16le d 28) * (NANO.toInt32 (rd32le d 22)).natAbs > size) := by
    have hU := @arithCode_unfold (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28) (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size hWle hBl hCh hHb
    rw [hAcr] at hU
    intro hbad
    rw [ite_eq_left hbad] at hU
    exact absurd hU (by decide)
  have hSpec : bmpHeaderCode size d = 10 :=
    bmpHeaderCode_ten_of_palette size d hSig hLayout hG0 hNotTrunc hB8 hEntriesBad
  have h13ne : EvE Gen.prog s14
      (.bin .ne (some ⟨32, true⟩) (.var 13) (.const (.int ⟨32, true⟩ 0)))
      (boolVal true) := by
    have e : EvE Gen.prog s14
        (.bin .ne (some ⟨32, true⟩) (.var 13) (.const (.int ⟨32, true⟩ 0)))
        (boolVal (decide (IntTy.toInt ⟨32, true⟩ (bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10)) ≠
          IntTy.toInt ⟨32, true⟩ 0))) :=
      EvE.bin (EvE.var hl13) (EvE.const _) (bin_i32_ne _ _)
    rw [hP10] at e
    rw [show (decide (IntTy.toInt ⟨32, true⟩ 10 ≠ IntTy.toInt ⟨32, true⟩ 0)) = true from by decide] at e
    exact e
  have hRet13 : ExS Gen.prog s14
      (.ite (.bin .ne (some ⟨32, true⟩) (.var 13) (.const (.int ⟨32, true⟩ 0)))
        (Stmt.ret (some (Expr.var 13))) .skip)
      (Outcome.ret (some (.int ⟨32, true⟩ 10))) s14 :=
    ExS.ite h13ne truthy_true (ExS.ret (EvE.var h10v))
  refine ⟨s14, ?_⟩
  show ExS Gen.prog s6 ni_bmp_header_rem_stmt (.ret (some (.int ⟨32, true⟩ (bmpHeaderCode size d)))) s14
  rw [hSpec]
  have h12skipV12 : EvE Gen.prog s13
      (.bin .ne (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 0)))
      (boolVal false) := by
    have e : EvE Gen.prog s13
        (.bin .ne (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 0)))
        (boolVal (decide (IntTy.toInt ⟨32, true⟩ (bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
          (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size) ≠ IntTy.toInt ⟨32, true⟩ 0))) :=
      EvE.bin (EvE.var hl12) (EvE.const _) (bin_i32_ne _ _)
    rw [hAcr] at e
    rw [show (decide (IntTy.toInt ⟨32, true⟩ 0 ≠ IntTy.toInt ⟨32, true⟩ 0)) = false from by decide] at e
    exact e
  have hTailA : ExS Gen.prog s12
      (.seq (.call (some 12) 17 [(.var 7), (.var 8), (.var 5), (.var 9), (.var 3), (.var 1), (.var 2)])
        (.ite (.bin .ne (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 0))) (.ret (some (.var 12))) .skip))
      .normal s13 :=
    ExS.seq hCallA (ExS.ite h12skipV12 truthy_false ExS.skip)
  have hRest : ExS Gen.prog s13 ni_bmp_header_rest_stmt (Outcome.ret (some (.int ⟨32, true⟩ 10))) s14 :=
    ExS.seq_ret (ExS.seq hCallP hRet13)
  exact ExS.seq hP (ExS.seq hTailA hRest)


/-- The full `ni_bmp_header` theorem: signature, layout, geometry, arith and
    palette stages, assembled from the outcome-specific lemmas. -/
theorem ni_bmp_header_rem_exs (s6 : State) (d : List UInt8) (bd : Nat) (hm : s6.mem bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hd : 54 ≤ d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : s6.mem 3 = some obl) (h48 : obl.length = 48)
    (hS6ro : s6.ro = false)
    (hSig : sigOk size d = true) (hLayout : layoutOk size d = true)
    (hl0 : s6.locals 0 = some (.ptr bd 0))
    (hl2 : s6.locals 2 = some (.ptr 3 0))
    (hl1 : s6.locals 1 = some (.int ⟨64, false⟩ size))
    (hl3 : s6.locals 3 = some (.int ⟨32, false⟩ (rd32le d 10)))
    (hl4 : s6.locals 4 = some (.int ⟨32, false⟩ (rd32le d 14)))
    (hl6 : s6.locals 6 = some (.int ⟨32, false⟩ (rd32le d 46))) :
    ∃ s', ExS Gen.prog s6 ni_bmp_header_rem_stmt
      (.ret (some (.int ⟨32, true⟩ (bmpHeaderCode size d)))) s' ∧
      ((bmpGeometryCode d = 0 →
       bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
         (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size = 0 →
       bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10) = 0 →
       ∃ gout, s'.mem 3 = some (bmpHeaderFinalBlock d gout) ∧ gout.length = 48) ∧
       (bmpGeometryCode d = 0 →
       bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
         (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size = 0 →
       bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10) = 0 →
       ∀ j, j ≠ 3 → s'.mem j = s6.mem j)) := by
  classical
  by_cases hG0 : bmpGeometryCode d = 0
  · by_cases hAcr : (bmpOutputArithCode (rd32le d 18) ((NANO.toInt32 (rd32le d 22)).natAbs) (rd16le d 28)
        (if rd16le d 28 = 32 then 4 else 3) (rd32le d 10) size) = 0
    · by_cases hPcr : (bmpOutputPaletteCode (rd16le d 28) (rd32le d 46) (rd32le d 14) (rd32le d 10)) = 0
      · obtain ⟨s', hEx, ⟨gout, hMem, hglen⟩, hStUnt⟩ :=
          ni_bmp_header_rem_stores_exs s6 d bd hm size hs hd hlen obl hob h48 hS6ro hSig hLayout
            hl0 hl2 hl1 hl3 hl4 hl6 hG0 hAcr hPcr
        exact ⟨s', hEx, (fun _ _ _ => ⟨gout, hMem, hglen⟩), fun _ _ _ j hj => hStUnt j hj⟩
      · obtain ⟨s', hEx⟩ :=
          ni_bmp_header_rem_palette_bad_exs s6 d bd hm size hs hd hlen obl hob h48 hS6ro hSig hLayout
            hl0 hl2 hl1 hl3 hl4 hl6 hG0 hAcr hPcr
        exact ⟨s', hEx, (fun _ _ hp => absurd hp hPcr), fun hg ha hp j hj => by
        first
          | exact absurd hg hG0
          | exact absurd ha hAcr
          | exact absurd hp hPcr⟩
    · obtain ⟨s', hEx⟩ :=
        ni_bmp_header_rem_arith_fail_exs s6 d bd hm size hs hd hlen obl hob h48 hS6ro hSig hLayout
          hl0 hl2 hl1 hl3 hl4 hl6 hG0 hAcr
      exact ⟨s', hEx, (fun _ ha _ => absurd ha hAcr), fun hg ha hp j hj => by
        first
          | exact absurd hg hG0
          | exact absurd ha hAcr
          | exact absurd hp hPcr⟩
  · obtain ⟨s', hEx⟩ :=
      ni_bmp_header_rem_geom_fail_exs s6 d bd hm size hs hd hlen obl hob h48 hS6ro hSig hLayout
        hl0 hl2 hl1 hl3 hl4 hl6 hG0
    exact ⟨s', hEx, (fun hg _ _ => absurd hg hG0), fun hg ha hp j hj => by
        first
          | exact absurd hg hG0
          | exact absurd ha hAcr
          | exact absurd hp hPcr⟩

end NANO.C.Proofs
