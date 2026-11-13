module

public import Silmaril.Wasm.Institution.Components.Defs
public import Silmaril.Proofs.Wasm.Institution.Components.Basic
public import Silmaril.Proofs.Wasm.Institution.Components.Wrap

@[expose] public section

/-!
# Modules versus components: results

Proofs in `Silmaril.Proofs.Wasm.Institution.Components.{Basic,Wrap,PairInr}`. Everything holds for an arbitrary
core semantics `C`.

* `top_le_iff`: viewing a `sigU` strategy at the top component interface reflects refinement.
* `valid_comp_iff`, `valid_linked_iff`, `valid_program_iff`: validity of `x' ⊑ x` at the top
  interface is `x'.denU C ≤ x.denU C`.
* **Passes are uniformly valid families**: `passEquivValid : Pass (contract C) ≃` size-preserving
  `f` with every `f c ⊑ c` valid in `compSem C`; `programPassEquivValid` for
  `(programIR C).contract`.
* `valid_fuse`: adapter fusion gives valid equations `fuseComponent c ≐ c` at every interface
  (unconditional). `valid_deadExports`: dead-export elimination gives valid equations in the
  program logic (unconditional). `valid_flatten L`: flattening gives valid equations, given
  `L : PairLaws`. With `pairLaws` it is unconditional.
* **Wrapping preserves meaning**: `wrap_denU : (wrap m).denU C = modU C m` for every `C` and
  `m`, so `wrapAdequate C : WrapAdequate C`. The proof uses the pairing laws and the right
  projection `PairInr.pair_restrict_inr : (σ₁.pair σ₂).restrict (Sig.Hom.inr F₁ F₂) = σ₂`,
  which is proved here, mirroring `Silmaril.Games`' left projection.
* `valid_game_fuse`: the fusion equation, borrowed along `compToGame` into the component game
  logic.
-/
