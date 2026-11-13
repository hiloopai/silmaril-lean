module

public import Silmaril.Proofs.Wasm.WatSpec.Sound

/-!
# Annotated WAT: results

Proofs in `Silmaril.Proofs.Wasm.WatSpec.Sound`, at every profile and for every host relation:

* **`Annotated.sound`**: `A.vc` (the verification condition of an annotated function, computed
  by the verified generator `Silmaril.Wasm.Logic.VC.wpc`) gives `FSpecValid P host a (A.spec fi a)`
  for every function instance `fi` running `A.func` with a type of `A.nparams` parameters and
  `A.nresults` results;
* **`Annotated.invoke`**: every run of `$invoke` on arguments meeting the precondition can
  still step or has returned results meeting the postcondition, with the store unchanged;
* **`AnnotatedSt.sound`** (and `sound₀`, no calls): the same for `wat_spec_st!`, with a valid
  spec context for the calls of the body;
* the front-end lemmas: `Annotated.vc_toFnSpec` (`A.vc → A.toFnSpec.vc A.func`),
  `Annotated.verified` (`Silmaril.Wasm.Verify.Verified A.module 0 A.toFnSpec`) and
  `AnnotatedSt.toFnSpec_sound` (`FnSpec.sound` for the `FnSpec` form);
* read-back of globals: `gv_of_globalVal`, `gv_set_self`, `gv_set_ne`.

The `wat_spec!` elaborator is not trusted: these hold for any `Annotated`.
-/
