/-
  `ni_tga_header` top-level refinement: loads then tail.
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Lemmas
import NANO.Spec
import NANO.Tga
import NANO.C.Proofs.Core
import NANO.C.Proofs.NiGeometryTail
import NANO.C.Proofs.NiBmpDecode
import NANO.C.Proofs.Bmp
import NANO.C.Proofs.NiTgaHeader
import NANO.C.Proofs.NiTgaHeaderBody
import NANO.C.Proofs.NiTgaHeaderStores
import NANO.C.Proofs.NiTgaHeaderGates
import NANO.C.Proofs.NiTgaHeaderSpecCode
import NANO.C.Proofs.NiTgaHeaderOut

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option maxHeartbeats 6000000

namespace NANO.C.Proofs
open NANO NANO.C

theorem ni_tga_header_exs (m : Mem) (bd : Nat) (d : List UInt8) (hm : m bd = some d)
    (size : Nat) (hs : size ≤ d.length) (hlen : d.length < 2 ^ 64)
    (obl : List UInt8) (hob : m 3 = some obl) (h32 : obl.length = 32) (ro : Bool)
    (hro : ro = false) :
    ∃ s', ExS Gen.prog ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩
      Gen.ni_tga_header.body
      (.ret (some (.int i32 (tgaHeaderCode size d)))) s' ∧
      (∀ j, j ≠ 3 → s'.mem j = m j) ∧
      (match tgaHeader size d with
       | .ok h => s'.mem 3 = some (tgaHeaderBlock obl h)
       | .error _ => True) := by
  have x_tt : truthy (boolVal true) = .ok true := truthy_boolVal true
  have x_tf : truthy (boolVal false) = .ok false := truthy_boolVal false
  have hcast : evalCast u64 (.int u32 18) = .ok (.int u64 18) := u32_u64_cast 18 (by omega)
  let s0 : State := ⟨frameLocals [0, 1, 2] [.ptr bd 0, .int u64 size, .ptr 3 0], m, ro⟩
  have hszE : EvE Gen.prog s0 (.bin .lt (some u64) (.var 1) (.cast u64 (.const (.int u32 18)))) (boolVal (decide (size < 18))) :=
    EvE.bin (EvE.var rfl) (EvE.cast (EvE.const _) hcast) (bin_u64_lt size 18)
  by_cases hsz : size < 18
  case pos =>
    have hltT : EvE Gen.prog s0 (.bin .lt (some u64) (.var 1) (.cast u64 (.const (.int u32 18)))) (boolVal true) := by
      rw [show decide (size < 18) = true from decide_eq_true_eq.mpr hsz] at hszE; exact hszE
    have hgate : ExS Gen.prog s0 tgaSizeGate (.ret (some (.int i32 1))) s0 :=
      ExS.ite hltT x_tt (ExS.ret (EvE.const (v := .int i32 1)))
    refine ⟨s0, (by rw [tgaCode_lt18 d size hsz]; exact ExS.seq_ret hgate), (fun j _ => rfl), (by simp [tgaHeader_lt18 d size hsz])⟩
  case neg =>
    have hd18 : 18 ≤ d.length := by omega
    have hltF : EvE Gen.prog s0 (.bin .lt (some u64) (.var 1) (.cast u64 (.const (.int u32 18)))) (boolVal false) := by
      rw [show decide (size < 18) = false from decide_eq_false_iff_not.mpr hsz] at hszE; exact hszE
    have hgate0 : ExS Gen.prog s0 tgaSizeGate .normal s0 := ExS.ite hltF x_tf ExS.skip
    have load3 : ExS Gen.prog s0 tgaLoad3 .normal ⟨s0.locals.upd 3 (.int u8 (byteAt d 0)), m, ro⟩ :=
      ExS.set (EvE.load (ev_ptr_const (s := s0) (d := d) (k := 0) hm (by rfl) (by omega) (by omega)) (load_byte_dyn m bd d hm 0 (by omega)))
    let s3 : State := ⟨s0.locals.upd 3 (.int u8 (byteAt d 0)), m, ro⟩
    have load4 : ExS Gen.prog s3 tgaLoad4 .normal ⟨s3.locals.upd 4 (.int u8 (byteAt d 1)), m, ro⟩ :=
      ExS.set (EvE.load (ev_ptr_const (s := s3) (d := d) (k := 1) hm (by rfl) (by omega) (by omega)) (load_byte_dyn m bd d hm 1 (by omega)))
    let s4 : State := ⟨s3.locals.upd 4 (.int u8 (byteAt d 1)), m, ro⟩
    have load5 : ExS Gen.prog s4 tgaLoad5 .normal ⟨s4.locals.upd 5 (.int u8 (byteAt d 2)), m, ro⟩ :=
      ExS.set (EvE.load (ev_ptr_const (s := s4) (d := d) (k := 2) hm (by rfl) (by omega) (by omega)) (load_byte_dyn m bd d hm 2 (by omega)))
    let s5 : State := ⟨s4.locals.upd 5 (.int u8 (byteAt d 2)), m, ro⟩
    have call6 : ExS Gen.prog s5 tgaCall6 .normal ⟨s5.locals.upd 6 (.int u16 (rd16le d 12)), m, ro⟩ :=
      ExS.call_dst (s' := ⟨frameLocals [0] [.ptr bd 12], m, ro⟩)
        (EvArgs.cons (ev_ptr_const (s := s5) (d := d) (k := 12) hm (by rfl) (by omega) (by omega)) EvArgs.nil)
        (show Gen.prog 0 = some Gen.ni_read_u16le from rfl) (show Gen.ni_read_u16le.params.length = 1 from rfl)
        (ni_read_u16le_exs m bd d hm 12 (by omega) hlen ro)
    let s6 : State := ⟨s5.locals.upd 6 (.int u16 (rd16le d 12)), m, ro⟩
    have call7 : ExS Gen.prog s6 tgaCall7 .normal ⟨s6.locals.upd 7 (.int u16 (rd16le d 14)), m, ro⟩ :=
      ExS.call_dst (s' := ⟨frameLocals [0] [.ptr bd 14], m, ro⟩)
        (EvArgs.cons (ev_ptr_const (s := s6) (d := d) (k := 14) hm (by rfl) (by omega) (by omega)) EvArgs.nil)
        (show Gen.prog 0 = some Gen.ni_read_u16le from rfl) (show Gen.ni_read_u16le.params.length = 1 from rfl)
        (ni_read_u16le_exs m bd d hm 14 (by omega) hlen ro)
    let s7a : State := ⟨s6.locals.upd 7 (.int u16 (rd16le d 14)), m, ro⟩
    have load8 : ExS Gen.prog s7a tgaLoad8 .normal ⟨s7a.locals.upd 8 (.int u8 (byteAt d 16)), m, ro⟩ :=
      ExS.set (EvE.load (ev_ptr_const (s := s7a) (d := d) (k := 16) hm (by rfl) (by omega) (by omega)) (load_byte_dyn m bd d hm 16 (by omega)))
    let s7b : State := ⟨s7a.locals.upd 8 (.int u8 (byteAt d 16)), m, ro⟩
    have load9 : ExS Gen.prog s7b tgaLoad9 .normal ⟨s7b.locals.upd 9 (.int u8 (byteAt d 17)), m, ro⟩ :=
      ExS.set (EvE.load (ev_ptr_const (s := s7b) (d := d) (k := 17) hm (by rfl) (by omega) (by omega)) (load_byte_dyn m bd d hm 17 (by omega)))
    let s7 : State := ⟨s7b.locals.upd 9 (.int u8 (byteAt d 17)), m, ro⟩
    have l1 : s7.locals 1 = some (.int u64 size) := by dsimp only [s7, s7b, s7a, s6, s5, s4, s3, s0]; simp [Locals.upd_same, Locals.upd_ne]; rfl
    have l2 : s7.locals 2 = some (.ptr 3 0) := by dsimp only [s7, s7b, s7a, s6, s5, s4, s3, s0]; simp [Locals.upd_same, Locals.upd_ne]; rfl
    have l3 : s7.locals 3 = some (.int u8 (byteAt d 0)) := by dsimp only [s7, s7b, s7a, s6, s5, s4, s3, s0]; simp [Locals.upd_same, Locals.upd_ne, frameLocals]
    have l4 : s7.locals 4 = some (.int u8 (byteAt d 1)) := by dsimp only [s7, s7b, s7a, s6, s5, s4, s3, s0]; simp [Locals.upd_same, Locals.upd_ne, frameLocals]
    have l5 : s7.locals 5 = some (.int u8 (byteAt d 2)) := by dsimp only [s7, s7b, s7a, s6, s5, s4, s3, s0]; simp [Locals.upd_same, Locals.upd_ne, frameLocals]
    have l6 : s7.locals 6 = some (.int u16 (rd16le d 12)) := by dsimp only [s7, s7b, s7a, s6, s5, s4, s3, s0]; simp [Locals.upd_same, Locals.upd_ne, frameLocals]
    have l7 : s7.locals 7 = some (.int u16 (rd16le d 14)) := by dsimp only [s7, s7b, s7a, s6, s5, s4, s3, s0]; simp [Locals.upd_same, Locals.upd_ne, frameLocals]
    have l8 : s7.locals 8 = some (.int u8 (byteAt d 16)) := by dsimp only [s7, s7b, s7a, s6, s5, s4, s3, s0]; simp [Locals.upd_same, Locals.upd_ne, frameLocals]
    have l9 : s7.locals 9 = some (.int u8 (byteAt d 17)) := by dsimp only [s7, s7b, s7a, s6, s5, s4, s3, s0]; simp [Locals.upd_same, Locals.upd_ne, frameLocals]
    obtain ⟨s', hexs, hmem, hblk⟩ := tgaHeader_tail_exs m d size obl hob h32 ro hro hsz s7.locals l1 l2 l3 l4 l5 l6 l7 l8 l9
    refine ⟨s', (by exact ExS.seq hgate0 (ExS.seq load3 (ExS.seq load4 (ExS.seq load5 (ExS.seq call6 (ExS.seq call7 (ExS.seq load8 (ExS.seq load9 hexs)))))))), hmem, hblk⟩

end NANO.C.Proofs
