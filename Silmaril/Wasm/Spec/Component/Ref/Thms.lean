module

public import Silmaril.Wasm.Spec.Component.Ref.Defs
public import Silmaril.Proofs.Wasm.Spec.Component.Ground

@[expose] public section

/-!
# The reference semantics of components: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Component.Ground` (and short ones in
`Silmaril.Wasm.Spec.Component.Ref.Defs`), for every core engine, host, host state and component
choice profile:

* `refTraces_good`: the traces of a reference component are good;
* `mem_refTraces_ret`: every return event of such a trace comes from `exportBehaviours`;
* `refSem_retPost_iff`: **a return postcondition of export `j` holds iff every reference
  behaviour of calling `j` satisfies it**;
* `refSem_contract_iff`: the same for contracts, with the arguments of the call.
-/
