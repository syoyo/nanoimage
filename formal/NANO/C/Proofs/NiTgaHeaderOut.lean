/-
  `ni_tga_header` output-size computation: the two `set 11` multiplies.
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Lemmas
import NANO.Spec
import NANO.Tga
import NANO.C.Proofs.Core
import NANO.C.Proofs.NiGeometryTail
import NANO.C.Proofs.NiTgaHeader
import NANO.C.Proofs.NiTgaHeaderBody
import NANO.C.Proofs.NiTgaHeaderGates

set_option linter.unusedVariables false
set_option maxRecDepth 8000000
set_option maxHeartbeats 1600000

namespace NANO.C.Proofs
open NANO NANO.C

/-- `set 11 (width*height)` (with the overflow check passing). -/
theorem tgaMulW_exs (s : State) (ww hhv : Nat)
    (l6 : s.locals 6 = some (.int u16 ww)) (l7 : s.locals 7 = some (.int u16 hhv))
    (hww : ww < 65536) (hhh : hhv < 65536) (hm : sizeMulOK ww hhv = true) :
    ExS Gen.prog s tgaMulW .normal ⟨s.locals.upd 11 (.int u64 (ww * hhv)), s.mem, s.ro⟩ :=
  ExS.set (EvE.bin (EvE.cast (EvE.var l6) (u16_u64_cast ww hww))
    (EvE.cast (EvE.var l7) (u16_u64_cast hhv hhh))
    (bin_u64_mul ww hhv (sizeMulOK_mul_lt ww hhv hm)))

/-- `set 11 ((width*height)*channels)` (with the overflow check passing). -/
theorem tgaMulWC_exs (s : State) (osz ch : Nat)
    (l11 : s.locals 11 = some (.int u64 osz)) (l10 : s.locals 10 = some (.int u8 ch))
    (hosz : osz < 2 ^ 64) (hch : ch < 256) (hm : sizeMulOK osz ch = true) :
    ExS Gen.prog s tgaMulWC .normal ⟨s.locals.upd 11 (.int u64 (osz * ch)), s.mem, s.ro⟩ :=
  ExS.set (EvE.bin (EvE.var l11)
    (EvE.cast (EvE.var l10) (u8_u64_cast ch hch))
    (bin_u64_mul osz ch (sizeMulOK_mul_lt osz ch hm)))

end NANO.C.Proofs
