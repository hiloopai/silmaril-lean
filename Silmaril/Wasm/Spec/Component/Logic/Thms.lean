module

public import Silmaril.Wasm.Spec.Component.Logic.Defs
public import Silmaril.Proofs.Wasm.Spec.Component.Ground

@[expose] public section

/-!
# Component-specific logics: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Component.Ground`; logic maps in
`Silmaril.Wasm.Spec.Component.Logic.Defs`.

* `everyPos_nil`, `everyPos_cons`, `everyPos_single`, `everyPos_pair`: action invariants on
  concrete traces;
* `contract_pair_iff`: a contract on a call followed by its return is the implication
  `pre a → post a b` when the call is of the contract's export;
* logic maps: `Contract.toAct`, `BorrowScoped.toAct`, `NoUseAfterDrop.toAct` (into `act`, hence
  LTL/CTL/TLA through `Silmaril.Wasm.Spec.Embed`), `CallTyped.toCallPre`.
-/
