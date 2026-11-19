module

public import Silmaril.Wasm.Execution.Core.Intrinsic.LiveLift.Defs
import Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.LiveLift
import Silmaril.Wasm.Execution.Core.Intrinsic.Thms

public section

namespace Silmaril.Wasm.Execution.Core.Intrinsic

open Silmaril.Wasm.Validation

variable {locals input output : List IntType}

theorem Code.reify_erase (code : Code locals input output) (live : .unreachable ∉ code.erase) :
    Code.reify? locals input code.erase = some ⟨output, code, rfl, live⟩ :=
  Proofs.Wasm.Execution.Core.Intrinsic.reify_erase code live

/-- Exact erasure and its computable inverse for the checked live fragment. -/
def Code.liveEquiv (locals input : List IntType) : Code.Live locals input ≃ Code.CheckedRaw locals input :=
  Proofs.Wasm.Execution.Core.Intrinsic.liveEquiv locals input

theorem Code.Lifted.sound {context : Context} {raw : List Instr}
    (result : Code.Lifted locals input raw) (h : context.locals = localTypes locals) :
    InstrsOk context raw (.plain (stackTypes input) (stackTypes result.1)) :=
  Eq.mp (congrArg (fun instrs => InstrsOk context instrs
    (.plain (stackTypes input) (stackTypes result.1))) result.2.2.1) (result.2.1.sound h)

end Silmaril.Wasm.Execution.Core.Intrinsic
