module

public import Silmaril.Wasm.Resource.Component.Defs
public import Silmaril.Proofs.Wasm.Resource.Component.Basic

@[expose] public section

/-!
# Resource protocols for components: results

Proofs in `Silmaril.Proofs.Wasm.Resource.Component.Basic`: `nud_run_mem` (the state of `nudProto d`
is the list of dropped representations), **`nudProto_accepts_iff`** and
**`models_noUseAfterDrop_iff`** (`noUseAfterDrop d` is the protocol `nudProto d`, in every
semantics).
-/
