module

public import Silmaril.Wasm.Spec.Component.Defs
public import Silmaril.Proofs.Wasm.Spec.Component.Ground

@[expose] public section

/-!
# Component signatures: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Component.Ground`.

* `irTy_level`, `irTys_level`, `irFields_level`, `irCases_level`, `irOpt_level`, `irFn_level`:
  the reference types of Silmaril's IR types are at most aggregates (levels `0`–`1`);
* `cface_level`: so is the interface of every IR component;
* `hasType_irTy` (with `hasFields_irFields`, `hasCase_irCases`, `hasOpt_irOpt`): **IR typing
  is reference typing**: if `t.check v` (the IR's dynamic check) then `toRefVal v` has the
  reference type `irTy t` (`Val.HasType` of the copied reference); `typed_irTys` for argument
  lists, and `Simple.refPre_typed`: the precondition of a transferred contract implies
  reference typing (`Typed`).
-/
