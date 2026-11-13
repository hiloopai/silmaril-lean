module

public import Silmaril.Wasm.Resource.Protocol.Defs
public import Silmaril.Proofs.Wasm.Resource.Protocol.Basic

@[expose] public section

/-!
# Resource protocols: results

Proofs in `Silmaril.Proofs.Wasm.Resource.Protocol.Basic`.

* `Protocol.run_append`, `Protocol.Accepts.of_prefix` (protocols are safety properties),
  `Protocol.accepts_concat_iff`, `Protocol.acceptsB_iff` (decidable acceptance).
* `Protocol.accepts_comap`, `Protocol.accepts_prod_iff` (conjunction of protocols).
* `Protocol.everyPos_iff` and the logic map `Protocol.toActMap : protoLogic → act`; through `act`
  protocol sentences map further into LTL, CTL and TLA (`Silmaril.Wasm.Spec.Embed`).
* `models_protoLogic_iff`, `not_models_of_trace` (refutation by one rejected trace),
  `models_prod_iff`.
-/
