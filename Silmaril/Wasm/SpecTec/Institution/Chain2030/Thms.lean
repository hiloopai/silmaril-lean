module

public import Silmaril.Wasm.SpecTec.Institution.Chain2030.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Chain2030

/-!
# The SpecTec specification institution, wasm-2.0 → wasm-3.0: results

Namespace `Silmaril.Wasm.SpecTec.Institution.Chain2030`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.Chain2030`; see `docs/projects/spectec/README.md`,
"compose".

* `toV2`: the wasm-2.0 model's step chart to the V2 step chart, on pairs in `PairDom`, preserving
  existential sentences (`Wasm20.toModelSE` read from the model's side).
* `core_step_of_v2_step`, `toCore`: along `Step.toCore` (the simulation under
  `Models.V2Core.v20Emb`), the V2 step chart to the Core step chart on `Wasm30.DomDet`,
  preserving value-blind sentences (`Blind`).
* **`chain`**: `toV2`, `toCore` and `Wasm30.toModel` composed, a transition from the wasm-2.0
  model to the wasm-3.0 model (`Wasm30.stepModel (Wasm30.builtins ..)`), direction `preserves`
  (`chain_dir`), on value-blind sentences, with point map `configV hn ∘ Prod.snd` (`chain_pt`).
* `progress_chain`, `stuck_chain`: progress goes from the 2.0 model to the 3.0 model, stuckness
  back.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Chain2030.progress_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Chain2030.progress_chain

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Chain2030.stuck_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Chain2030.stuck_chain

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Chain2030.chain_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Chain2030.chain_dir
