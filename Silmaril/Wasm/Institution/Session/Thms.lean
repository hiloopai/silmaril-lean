module

public import Silmaril.Wasm.Institution.Session.Defs
public import Silmaril.Proofs.Wasm.Institution.Session.Basic

@[expose] public section

/-!
# Wasm session logics: results

Proofs are in `Silmaril.Proofs.Wasm.Institution.Session.Basic`.

* **Validity is silmaril's notion.** `valid_coreRef_iff`: validity of `m ⊑ m'` at the full
  interface in `coreRef P host R` is `ExportRefines R P host m m'`; `valid_birRef_iff` is the
  same for Binaryen IR (on lowerings); `valid_coreEquiv_iff`/`valid_birEquiv_iff` give
  `ExportEquiv R`; `valid_coreRef_eqSen_iff`: the equation `m ≐ m'` of the `Eq`-refinement logic
  is `ExportEquiv Eq`.
* **Hiding.** `Refines.restrict`, `valid_leSen_restrict`: refinement through an interface
  implies refinement through every smaller one.
* **Contracts as closures.** `refines_close_iff`: `a ⊑_R b ↔ a ⊑_Eq close R b` (uses
  `sessionRel_eq_iff`: under `Eq` the `ub` rule of `SessionRel` never fires).
* **Translations** (`ObsSemantics.Translation`, hence comorphisms, all model-expansive):
  `lowerT` (Binaryen IR → Core), `liftT` (Core → Binaryen IR), `closeT` (`R`-refinement →
  `Eq`-refinement, `t ⊑ u ↦ t ⊑ close R u`), `equivT` (`Eq`-equivalence → `Eq`-refinement,
  `t ≈ u ↦ t ≐ u`). `sat_lowerT_liftT_iff`: Core is a retract of Binaryen IR up to
  satisfaction.
* **Coarsening.** `entails_close`: `{t ⊑ u} ⊨ t ⊑ close R u` in the `Eq`-refinement logic for
  reflexive `R`; `exportRefines_of_eq` re-derives `ExportRefines Eq → ExportRefines R` through
  the institutions.
* **Passes.** `passEquivValid`: `Pass (refinesContract R P host hR)` is equivalent to
  invariant-preserving transformations `f` with every `f m ⊑ m` valid in `birRef P host R`;
  `passEquivValidEquiv` for `equivContract`; `soundPass_iff_valid` for `SoundPass`.
-/
