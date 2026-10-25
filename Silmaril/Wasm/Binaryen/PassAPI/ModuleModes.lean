module

public import Silmaril.Wasm.Binaryen.PassAPI.Modes

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Modes

open Execution.Core Numerics Validation

variable {H : Type}

/-- The same source-first mode contract for transformations acting directly on
Core modules. Folded IR clients keep `Modes.contract` and its lower boundary. -/
def moduleContract (mode : Optimization.Mode) (P : Profile) (host : HostSemantics H) :
    Silmaril.Compile.PassAPI.Contract Module where
  Rel source target := ExportCorrect mode P host source target
  refl source := ExportCorrect.refl mode P host source
  trans := ExportCorrect.trans
  Inv := ModuleValid

@[simp] theorem moduleContract_lower_rel (mode : Optimization.Mode) (P : Profile)
    (host : HostSemantics H) (source target : BModule) :
    (moduleContract mode P host).Rel source.lower target.lower ↔
      (contract mode P host).Rel source target := Iff.rfl

@[simp] theorem moduleContract_lower_inv (mode : Optimization.Mode) (P : Profile)
    (host : HostSemantics H) (m : BModule) :
    (moduleContract mode P host).Inv m.lower ↔ (contract mode P host).Inv m := Iff.rfl

end Silmaril.Wasm.Binaryen.Modes
