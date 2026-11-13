module

public import Silmaril.Wasm.Auto2.Valid2.Defs
public import Silmaril.Proofs.Wasm.Auto2.Valid2.Module

@[expose] public section

/-!
# The extended structural validator: results

Proofs in `Silmaril.Proofs.Wasm.Auto2.Valid2.{Atom,Step,Module}`.

* `nextOk_of_atomG`: a step of `atomG` (`Valid`'s fragment, globals, `select`, memory) is a step
  of silmaril-lean's `checkInstr atomC tyOkC` on the reversed stack;
* `instrC_sound`, `back_classify`, `instrN_sound`: every case of the one-instruction checker
  (direct atoms, `block`/`loop`/`if`, branches, `return`, `unreachable`, `call`) is a step of
  `checkInstr` (normal or stack-polymorphic), given a sound body checker;
* `runL_sound`, **`seqN_sound`**: an accepted sequence is accepted by `checkSeq` with its goal;
  `exprC_of_exprG`, `funcCheck_of_funcBodyG`, `checkersX_sound`;
* `encB_inj`, `nodupNamesN_eq`: export names compared as numbers;
* `checkModuleG?_sound`, **`validG?_eq : validG? m = validate? m`**, and
  `validate?_isSome_of_validG`, the form a certificate uses (`rw [← validG?_eq]; decide +kernel`).
-/
