/-
  Definitional transcription of `ni_tga_header`'s body into named fragments,
  checked equal to `Gen.ni_tga_header.body` by `rfl`.
-/
import NANO.C.Gen
import NANO.C.Semantics
import NANO.C.Lemmas
import NANO.C.Proofs.Core

set_option linter.unusedVariables false
set_option maxRecDepth 8000000

namespace NANO.C.Proofs
open NANO NANO.C

abbrev tgaSizeGate : Stmt :=
  .ite (.bin .lt (some u64) (.var 1) (.cast u64 (.const (.int u32 18))))
    (.ret (some (.const (.int i32 1)))) .skip

abbrev tgaLoad3 : Stmt := .set 3 (.load (.int u8) (.index (.var 0) (.const (.int i32 0)) 1))
abbrev tgaLoad4 : Stmt := .set 4 (.load (.int u8) (.index (.var 0) (.const (.int i32 1)) 1))
abbrev tgaLoad5 : Stmt := .set 5 (.load (.int u8) (.index (.var 0) (.const (.int i32 2)) 1))
abbrev tgaCall6 : Stmt := .call (some 6) 0 [(.index (.var 0) (.const (.int i32 12)) 1)]
abbrev tgaCall7 : Stmt := .call (some 7) 0 [(.index (.var 0) (.const (.int i32 14)) 1)]
abbrev tgaLoad8 : Stmt := .set 8 (.load (.int u8) (.index (.var 0) (.const (.int i32 16)) 1))
abbrev tgaLoad9 : Stmt := .set 9 (.load (.int u8) (.index (.var 0) (.const (.int i32 17)) 1))

abbrev tgaDims : Stmt :=
  .ite (.lor (.bin .eq (some u32) (.cast u32 (.var 6)) (.const (.int u32 0)))
             (.bin .eq (some u32) (.cast u32 (.var 7)) (.const (.int u32 0))))
    (.ret (some (.const (.int i32 2)))) .skip

abbrev tgaCmap : Stmt :=
  .ite (.bin .ne (some u32) (.cast u32 (.var 4)) (.const (.int u32 0)))
    (.ret (some (.const (.int i32 3)))) .skip

abbrev tgaBadType : Stmt :=
  .ite (.land (.land (.land (.bin .ne (some u32) (.cast u32 (.var 5)) (.const (.int u32 2)))
                             (.bin .ne (some u32) (.cast u32 (.var 5)) (.const (.int u32 3))))
                    (.bin .ne (some u32) (.cast u32 (.var 5)) (.const (.int u32 10))))
             (.bin .ne (some u32) (.cast u32 (.var 5)) (.const (.int u32 11))))
    (.ret (some (.const (.int i32 4)))) .skip

abbrev tgaSet10_1 : Stmt := .set 10 (.cast u8 (.const (.int u32 1)))
abbrev tgaSet10_3 : Stmt := .set 10 (.cast u8 (.const (.int u32 3)))
abbrev tgaSet10_4 : Stmt := .set 10 (.cast u8 (.const (.int u32 4)))

abbrev tgaChannels : Stmt :=
  .ite (.lor (.bin .eq (some u32) (.cast u32 (.var 5)) (.const (.int u32 3)))
             (.bin .eq (some u32) (.cast u32 (.var 5)) (.const (.int u32 11))))
    (.seq (.ite (.bin .ne (some u32) (.cast u32 (.var 8)) (.const (.int u32 8)))
                (.ret (some (.const (.int i32 5)))) .skip)
          tgaSet10_1)
    (.ite (.bin .eq (some u32) (.cast u32 (.var 8)) (.const (.int u32 24)))
          tgaSet10_3
      (.ite (.bin .eq (some u32) (.cast u32 (.var 8)) (.const (.int u32 32)))
            tgaSet10_4
            (.ret (some (.const (.int i32 5))))))

abbrev tgaIdBad : Stmt :=
  .ite (.bin .gt (some u64)
          (.bin .add (some u64) (.cast u64 (.const (.int i32 18))) (.cast u64 (.var 3)))
          (.var 1))
    (.ret (some (.const (.int i32 6)))) .skip

abbrev tgaMulBad1 : Stmt :=
  .ite (.un .lnot i32 (.call 11 [(.cast u64 (.var 6)), (.cast u64 (.var 7))]))
    (.ret (some (.const (.int i32 7)))) .skip

abbrev tgaMulW : Stmt := .set 11 (.bin .mul (some u64) (.cast u64 (.var 6)) (.cast u64 (.var 7)))

abbrev tgaMulBad2 : Stmt :=
  .ite (.un .lnot i32 (.call 11 [(.var 11), (.cast u64 (.var 10))]))
    (.ret (some (.const (.int i32 7)))) .skip

abbrev tgaMulWC : Stmt := .set 11 (.bin .mul (some u64) (.var 11) (.cast u64 (.var 10)))

abbrev tgaStores : Stmt :=
  .seq (.store (.int u32) (.field (.var 2) 16) (.cast u32 (.var 6))) (.seq (.store (.int u32) (.field (.var 2) 20) (.cast u32 (.var 7))) (.seq (.store (.int u8) (.field (.var 2) 24) (.var 10)) (.seq (.store (.int u8) (.field (.var 2) 25) (.cast u8 (.lor (.bin .eq (some u32) (.cast u32 (.var 5)) (.const (.int u32 10))) (.bin .eq (some u32) (.cast u32 (.var 5)) (.const (.int u32 11)))))) (.seq (.store (.int u8) (.field (.var 2) 26) (.cast u8 (.bin .ne (some u32) (.bin .band (some u32) (.cast u32 (.var 9)) (.const (.int u32 32))) (.const (.int u32 0))))) (.seq (.store (.int u8) (.field (.var 2) 27) (.cast u8 (.bin .ne (some u32) (.bin .band (some u32) (.cast u32 (.var 9)) (.const (.int u32 16))) (.const (.int u32 0))))) (.seq (.store (.int u64) (.field (.var 2) 8) (.bin .add (some u64) (.cast u64 (.const (.int i32 18))) (.cast u64 (.var 3)))) (.seq (.store (.int u64) (.field (.var 2) 0) (.var 11)) ((.ret (some (.const (.int i32 0))))))))))))

abbrev tgaTail : Stmt :=
  .seq tgaDims (.seq tgaCmap (.seq tgaBadType (.seq tgaChannels (.seq tgaIdBad (.seq tgaMulBad1 (.seq tgaMulW (.seq tgaMulBad2 (.seq tgaMulWC (tgaStores)))))))))

/-- The transcribed body (right-nested to match `Gen`). -/
abbrev tgaHeaderBody : Stmt :=
  .seq tgaSizeGate
  (.seq tgaLoad3
  (.seq tgaLoad4
  (.seq tgaLoad5
  (.seq tgaCall6
  (.seq tgaCall7
  (.seq tgaLoad8
  (.seq tgaLoad9 tgaTail)))))))

/-- The transcribed body equals the generated body. -/
theorem tgaHeaderBody_eq : Gen.ni_tga_header.body = tgaHeaderBody := rfl

end NANO.C.Proofs
