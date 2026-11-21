module

public import Silmaril.Wasm.Execution.Core.Entry.Program.Defs
public import Silmaril.Wasm.V1.Intrinsic.Scalar.Defs
import Silmaril.Wasm.V1.Intrinsic.Scalar.Thms

public section

namespace Silmaril.Wasm.Execution.Core.Entry

open Numerics Semantics.Operational

variable {H : Type} {signature : V1.FuncType}

/-- Direct intrinsic emission and native V1 erasure followed by the standard
syntax injection select exactly the same Core entries and execution policy.
The equality concerns Core entry, not native V1 behavior. -/
theorem wasm1Scalar_core_entry (P : Profile) (host : HostSemantics H) (store : Store H) :
    ((rawModule P host).precompose (fun mod : V1.Module => ⟨store, mod.toCore, []⟩)).precompose
        (V1.Intrinsic.Scalar.ClosedModule.erase (sig := signature)) =
      (rawModule P host).precompose (fun term : V1.Intrinsic.Scalar.ClosedModule signature =>
        ⟨store, term.toCore, []⟩) :=
  congrArg ((rawModule P host).precompose (Other := V1.Intrinsic.Scalar.ClosedModule signature))
    (funext fun term => congrArg (fun body => ModuleInput.mk store body []) term.toCore_eq.symm)

end Silmaril.Wasm.Execution.Core.Entry
