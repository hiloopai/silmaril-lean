module

public import Silmaril.Wasm.Spec.Format.Defs
public import Silmaril.Proofs.Wasm.Spec.Format.Basic

@[expose] public section

/-!
# The trace-institution format: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Format.Basic`.

* `preimage?_eq_some_iff`, `preimage?_comp`: preimages under injective maps of finite types.
* `back_id`, `back_comp`: observation of traces along interface morphisms is strictly
  functorial; hence `reduct_id`, `reduct_comp` for trace sets.
* `back_prefix`, `Good.reduct`: observation preserves good (nonempty, prefix-closed) trace sets;
  `reduct_mono`.
* `sat_map_iff` (in `Silmaril.Wasm.Spec.Format.Defs`): **the satisfaction condition** of
  `inst L S`.
* `sat_iff`: a model satisfies `(τ, φ)` iff `φ` holds of its traces observed through `τ`;
  `models_iff`: a program satisfies `φ` at its own interface iff its traces do;
  `Model.traces_reduct`: the traces of a reduct are the observed traces.
-/
