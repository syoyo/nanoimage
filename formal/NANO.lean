/-
  Lean 4 formalization and verification of nanoimage (loading path).
  See `formal/README.md` for the scope and `formal/VERIFICATION.md` for the
  assurance status.
-/
import NANO.Basic
import NANO.C.Semantics
import NANO.C.Logic
import NANO.C.Hoare
import NANO.C.Lemmas
import NANO.C.Gen
import NANO.Spec
import NANO.C.Proofs.Core
import NANO.C.Proofs.NiGeometryTail
import NANO.C.Proofs.NiGeometryPos
import NANO.C.Proofs.NiGeometryNegNormal
import NANO.C.Proofs.NiBmpHeaderSpec
import NANO.C.Proofs.NiBmpHeaderSpecSig1
import NANO.C.Proofs.NiBmpHeaderSpecGeo
import NANO.C.Proofs.NiBmpHeader
import NANO.C.Proofs.NiBmpHeaderLoads
import NANO.C.Proofs.NiBmpHeaderTail
import NANO.C.Proofs.NiBmpHeaderArith
import NANO.C.Proofs.NiBmpHeaderSpecCompose
import NANO.C.Proofs.NiBmpHeaderCompose
import NANO.C.Proofs.NiBmpHeaderHeight
import NANO.C.Proofs.NiBmpHeaderPalette
import NANO.Bmp
import NANO.Tga
import NANO.C.Proofs.Bmp
import NANO.C.Proofs.NiBmpHeaderSpecPalette
import NANO.C.Proofs.NiBmpDecode
import NANO.C.Proofs.NiBmpLoop
import NANO.C.Proofs.NiBmpLoop2
import NANO.C.Proofs.NiBmpLoop4
import NANO.C.Proofs.NiBmpLoop5
import NANO.C.Proofs.NiBmpDecodeInto
import NANO.C.Proofs.NiBmpLoad
import NANO.C.Proofs.NiTgaWritePixel
import NANO.C.Proofs.NiTgaHeader
import NANO.C.Proofs.NiTgaHeaderBody
import NANO.C.Proofs.NiTgaHeaderStores
import NANO.C.Proofs.NiTgaHeaderGates
import NANO.C.Proofs.NiTgaHeaderSpecCode
import NANO.C.Proofs.NiTgaHeaderOut

