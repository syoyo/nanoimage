import NANO.C.Proofs.NiTgaLoadFields
import NANO.C.Proofs.NiTgaDecode
import NANO.C.Proofs.NiTgaHeaderExs
import NANO.C.Proofs.NiBmpLoop

/-!
  M4: the composed `ni_load_tga` refinement.

  The shell calls `ni_tga_header` (fid 21) to parse and describe the image
  into the info block, bails out on a non-zero header code, then calls
  `ni_tga_decode_into` (fid 23) to write the pixels. On success the settled
  pixel buffer equals `tgaPixels d h`, the TGA spec.
-/

open NANO NANO.C NANO.C.Proofs

namespace NANO.C.Proofs

set_option maxHeartbeats 2000000

theorem ni_tga_load_exs (m : Mem) (d : List UInt8) (bd : Nat) (hm : m bd = some d)
    (size : Nat) (hs : size = d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : m 3 = some obl) (h32 : obl.length = 32)
    (out : List UInt8) (bo : Nat) (hoo : m bo = some out) (hcap64 : out.length < 2 ^ 64)
    (hbdo : bd ≠ bo) (h3o : 3 ≠ bo) (hb3 : 3 ≠ bd)
    (ro : Bool) (hro : ro = false)
    (h : TgaInfo) (hHdr : tgaHeader size d = .ok h)
    (hOut : out = tgaMaterialize h.outputSize [])
    (hch : h.channels < 256) (hcp : 0 < h.channels) (hrle8 : h.rle < 256)
    (hwh64 : h.width * h.height < 2 ^ 64)
    (hw32 : h.width < 2 ^ 32) (hh32 : h.height < 2 ^ 32) (hwpos : 0 < h.width) (hhpos : 0 < h.height)
    (hdo64 : h.dataOffset < 2 ^ 64) (hro8 : h.rightOrigin < 256) (hto8 : h.topOrigin < 256)
    (hbnd : ∀ q, q < h.width * h.height → TgaPixelBounds h q)
    (hwbf : ∀ q, q < h.width * h.height →
      tgaDstIndex h q + h.channels ≤ (tgaMaterialize h.outputSize []).length)
    (hOk : TgaOkW d h (h.width * h.height) (h.width * h.height) h.dataOffset)
    (hc : h.channels = 1 ∨ h.channels = 3 ∨ h.channels = 4) :
    ∃ s' p, tgaPixels d h = Except.ok p ∧
      ExS Gen.prog
        ⟨frameLocals [0, 1, 2, 3, 4, 17]
          [.ptr bd 0, .int ⟨64, false⟩ size, .ptr 3 0, .ptr bo 0, .int ⟨64, false⟩ out.length,
           .int ⟨32, true⟩ 0], m, ro⟩
        (.seq (.call (some 17) 21 [(.var 0), (.var 1), (.var 2)])
          (.seq (.ite (.bin .ne (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0)))
                  (.ret (some (.var 17))) .skip)
            (.seq (.call none 23 [(.var 0), (.var 1), (.var 2), (.var 3), (.var 4)])
              (.ret (some (.const (.int ⟨32, true⟩ 0)))))))
        (.ret (some (.int ⟨32, true⟩ (tgaHeaderCode size d)))) s' ∧
      s'.mem bo = some p := by
  have hCode0 : tgaHeaderCode size d = 0 := by unfold tgaHeaderCode; rw [hHdr]
  let s : State :=
    ⟨frameLocals [0, 1, 2, 3, 4, 17]
      ([.ptr bd 0, .int ⟨64, false⟩ size, .ptr 3 0, .ptr bo 0, .int ⟨64, false⟩ out.length,
        .int ⟨32, true⟩ 0] : List Val), m, ro⟩
  have truthy_false : truthy (boolVal false) = .ok false := truthy_boolVal false
  have h0 : s.locals 0 = some (.ptr bd 0) := rfl
  have h1 : s.locals 1 = some (.int ⟨64, false⟩ size) := rfl
  have h2 : s.locals 2 = some (.ptr 3 0) := rfl
  have h3 : s.locals 3 = some (.ptr bo 0) := rfl
  have h4 : s.locals 4 = some (.int ⟨64, false⟩ out.length) := rfl
  obtain ⟨sH, hHdrBody, hOther, hBlock⟩ :=
    ni_tga_header_exs m bd d hm size (Nat.le_of_eq hs) hlen obl hob h32 ro hro
  have hHdrArgs : EvArgs Gen.prog s [(.var 0), (.var 1), (.var 2)]
      [.ptr bd 0, .int ⟨64, false⟩ size, .ptr 3 0] :=
    EvArgs.cons (EvE.var h0) (EvArgs.cons (EvE.var h1) (EvArgs.cons (EvE.var h2) EvArgs.nil))
  have hHdrCall : ExS Gen.prog s (.call (some 17) 21 [(.var 0), (.var 1), (.var 2)]) .normal
      { s with mem := sH.mem, locals := s.locals.upd 17 (.int ⟨32, true⟩ (tgaHeaderCode size d)) } :=
    ExS.call_dst hHdrArgs (show Gen.prog 21 = some Gen.ni_tga_header from rfl)
      (show Gen.ni_tga_header.params.length = 3 from rfl) hHdrBody
  let s1 : State :=
    { s with mem := sH.mem, locals := s.locals.upd 17 (.int ⟨32, true⟩ (tgaHeaderCode size d)) }
  have h17_1 : s1.locals 17 = some (.int ⟨32, true⟩ 0) := by
    rw [show s1.locals = s.locals.upd 17 (.int ⟨32, true⟩ (tgaHeaderCode size d)) from rfl,
      Locals.upd_same, hCode0]
  have h0_1 : s1.locals 0 = some (.ptr bd 0) :=
    locals_upd_extract 17 (.int ⟨32, true⟩ (tgaHeaderCode size d)) 0 (by decide : ¬ (0 : Nat) = 17) h0
  have h1_1 : s1.locals 1 = some (.int ⟨64, false⟩ size) :=
    locals_upd_extract 17 (.int ⟨32, true⟩ (tgaHeaderCode size d)) 1 (by decide : ¬ (1 : Nat) = 17) h1
  have h2_1 : s1.locals 2 = some (.ptr 3 0) :=
    locals_upd_extract 17 (.int ⟨32, true⟩ (tgaHeaderCode size d)) 2 (by decide : ¬ (2 : Nat) = 17) h2
  have h3_1 : s1.locals 3 = some (.ptr bo 0) :=
    locals_upd_extract 17 (.int ⟨32, true⟩ (tgaHeaderCode size d)) 3 (by decide : ¬ (3 : Nat) = 17) h3
  have h4_1 : s1.locals 4 = some (.int ⟨64, false⟩ out.length) :=
    locals_upd_extract 17 (.int ⟨32, true⟩ (tgaHeaderCode size d)) 4 (by decide : ¬ (4 : Nat) = 17) h4
  have hCond : EvE Gen.prog s1
      (.bin .ne (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0))) (boolVal false) := by
    have e : EvE Gen.prog s1
        (.bin .ne (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0)))
        (boolVal (decide (IntTy.toInt ⟨32, true⟩ 0 ≠ IntTy.toInt ⟨32, true⟩ 0))) :=
      EvE.bin (EvE.var h17_1) (EvE.const _) (bin_i32_ne _ _)
    rw [show (decide (IntTy.toInt ⟨32, true⟩ 0 ≠ IntTy.toInt ⟨32, true⟩ 0)) = false from by decide] at e
    exact e
  have hIte : ExS Gen.prog s1
      (.ite (.bin .ne (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0)))
        (.ret (some (.var 17))) .skip) .normal s1 :=
    ExS.ite hCond truthy_false ExS.skip
  have hInfo3 : sH.mem 3 = some (tgaHeaderBlock obl h) := by
    have := hBlock
    rw [hHdr] at this
    simpa using this
  have hmD : s1.mem bd = some d := by
    rw [show s1.mem = sH.mem from rfl, hOther bd (Ne.symm hb3)]; exact hm
  have hobD : s1.mem bo = some out := by
    rw [show s1.mem = sH.mem from rfl, hOther bo (Ne.symm h3o)]; exact hoo
  have hmobD : s1.mem bo = some (tgaMaterialize h.outputSize []) := hOut ▸ hobD
  have h32b : (tgaHeaderBlock obl h).length = 32 := tgaHeaderBlock_length obl h h32
  have hl8 : load s1.mem (.int u8) (.ptr 3 24) = .ok (.int u8 h.channels) :=
    tgaHeaderBlock_load24 s1.mem obl h hInfo3 h32 hch
  have hl9 : load s1.mem (.int u8) (.ptr 3 25) = .ok (.int u8 h.rle) :=
    tgaHeaderBlock_load25 s1.mem obl h hInfo3 h32 hrle8
  have hl16 : load s1.mem (.int u32) (.ptr 3 16) = .ok (.int u32 h.width) :=
    tgaHeaderBlock_load16 s1.mem obl h hInfo3 h32 hw32
  have hl20 : load s1.mem (.int u32) (.ptr 3 20) = .ok (.int u32 h.height) :=
    tgaHeaderBlock_load20 s1.mem obl h hInfo3 h32 hh32
  have hl7 : load s1.mem (.int u64) (.ptr 3 8) = .ok (.int u64 h.dataOffset) :=
    tgaHeaderBlock_load8 s1.mem obl h hInfo3 h32 hdo64
  have hl26 : load s1.mem (.int u8) (.ptr 3 26) = .ok (.int u8 h.topOrigin) :=
    tgaHeaderBlock_load26 s1.mem obl h hInfo3 h32 hto8
  have hl27 : load s1.mem (.int u8) (.ptr 3 27) = .ok (.int u8 h.rightOrigin) :=
    tgaHeaderBlock_load27 s1.mem obl h hInfo3 h32 hro8
  have hDArgs : EvArgs Gen.prog s1 [(.var 0), (.var 1), (.var 2), (.var 3), (.var 4)]
      [.ptr bd 0, .int ⟨64, false⟩ size, .ptr 3 0, .ptr bo 0, .int ⟨64, false⟩ out.length] :=
    EvArgs.cons (EvE.var h0_1) (EvArgs.cons (EvE.var h1_1) (EvArgs.cons (EvE.var h2_1)
      (EvArgs.cons (EvE.var h3_1) (EvArgs.cons (EvE.var h4_1) EvArgs.nil))))
  obtain ⟨sD, p, hPix, hDecBody, hDecMem⟩ :=
    ni_tga_decode_into_ok_exs s1.mem bd size bo out.length (tgaHeaderBlock obl h) d ro h
      hs hInfo3 h32b hmD hmobD hbdo (Ne.symm h3o) (Ne.symm hb3) hro
      hl8 hl9 hl16 hl20 hl7 hl26 hl27
      hch hcp hrle8 hlen hwh64 hw32 hh32 hwpos hhpos hro8 hto8
      (hOut ▸ hcap64) hbnd hwbf hOk hc
  have hDecCall : ExS Gen.prog s1
      (.call none 23 [(.var 0), (.var 1), (.var 2), (.var 3), (.var 4)]) .normal
      { s1 with mem := sD.mem } :=
    ExS.call_ret hDArgs (show Gen.prog 23 = some Gen.ni_tga_decode_into from rfl)
      (show Gen.ni_tga_decode_into.params.length = 5 from rfl) hDecBody
  let s2 : State := { s1 with mem := sD.mem }
  have hRet : ExS Gen.prog s2 (.ret (some (.const (.int ⟨32, true⟩ 0))))
      (.ret (some (.int ⟨32, true⟩ 0))) s2 :=
    ExS.ret (EvE.const _)
  refine ⟨s2, p, hPix, ?_, hDecMem⟩
  rw [hCode0]
  exact ExS.seq hHdrCall (ExS.seq hIte (ExS.seq hDecCall hRet))

end NANO.C.Proofs
