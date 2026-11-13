module

public import Silmaril.Wasm.Auto2.Valid.Defs
public import Silmaril.Proofs.Wasm.Auto2.Valid.Module

@[expose] public section

/-!
# The structurally recursive validator: results

Proofs in `Silmaril.Proofs.Wasm.Auto2.Valid.{Step,Module}`.

* `checkInstr_of_sigF`, `step_of_stepF`, **`checkSeq_of_seqF`**: a step of the fragment checker
  is a step of silmaril-lean's `checkSeq atomC tyOkC` (stack reversed, locals unchanged);
* `exprC_of_exprF`, `funcCheck_of_funcF`: the fragment expression and function checkers imply
  the default ones;
* `nodupNames_eq`, `checkModuleK?_eq : checkModuleK? K m = checkModule? K m`,
  `checkersK_sound`;
* **`validK?_eq : validK? m = validate? m`**, and `validate?_isSome_of_validK`, the form a
  certificate uses (`rw [← validK?_eq]; decide +kernel`).
-/
