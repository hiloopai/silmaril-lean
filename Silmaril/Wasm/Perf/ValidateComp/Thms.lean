module

public import Silmaril.Wasm.Perf.ValidateComp.Defs
public import Silmaril.Wasm.Perf.ValidateR.Thms

/-!
# The fast component validators are the reference validator

* `core3ModuleTypeF_eq`, `checkCore3F_eq : checkCore3F = Reference.check?`;
* `core3ModuleTypeR_eq`, **`checkCore3R_eq : checkCore3R = Reference.check?`**, registered with
  `@[csimp]` (`check?_eq_checkCore3R`): compiled code that imports this module and calls the
  reference validator runs `checkCore3R`.

From `ValidateF.validateF_eq` and `ValidateR.validateR_eq`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.ValidateF

open Silmaril.Wasm.Component.Validation

theorem core3ModuleTypeF_eq : core3ModuleTypeF = core3ModuleType? := by
  funext m
  unfold core3ModuleTypeF core3ModuleType?
  rw [validateF_eq]

/-- **`checkCore3F` is `Reference.check?`.** -/
theorem checkCore3F_eq : checkCore3F = Silmaril.Wasm.Component.Reference.check? := by
  funext feat c
  unfold checkCore3F Silmaril.Wasm.Component.Reference.check? checkCore3?
  rw [core3ModuleTypeF_eq]

end Silmaril.Wasm.Perf.ValidateF

namespace Silmaril.Wasm.Perf.ValidateR

open Silmaril.Wasm.Component.Validation

theorem core3ModuleTypeR_eq : core3ModuleTypeR = core3ModuleType? := by
  funext m
  unfold core3ModuleTypeR core3ModuleType?
  rw [validateR_eq]

/-- **`checkCore3R` is `Reference.check?`.** -/
theorem checkCore3R_eq : checkCore3R = Silmaril.Wasm.Component.Reference.check? := by
  funext feat c
  unfold checkCore3R Silmaril.Wasm.Component.Reference.check? checkCore3?
  rw [core3ModuleTypeR_eq]

/-- Compiled code that imports this module and calls the reference validator runs
`checkCore3R`. -/
@[csimp] theorem check?_eq_checkCore3R :
    @Silmaril.Wasm.Component.Reference.check? = @checkCore3R :=
  checkCore3R_eq.symm

end Silmaril.Wasm.Perf.ValidateR
