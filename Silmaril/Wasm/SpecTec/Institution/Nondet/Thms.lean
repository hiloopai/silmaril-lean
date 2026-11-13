module

public import Silmaril.Wasm.SpecTec.Institution.Nondet.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Nondet
public import Silmaril.Proofs.Wasm.SpecTec.Institution.NondetTrans

/-!
# The wasm-3.0 semi-comorphism off the deterministic domain: results

Namespace `Silmaril.Wasm.SpecTec.Institution.Nondet`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.{Nondet,NondetTrans}`; see
`docs/projects/spectec/README.md`, "comorph".

On round 6's domain `Dom` (valid, `BoundedSel`, `BoundedSel` successors), at any primitives `B`
with `Halves B` (`halves_BI`: the concrete `Round4Int.BI`; `halves_builtins`: `Wasm30.builtins`),
the backend canonical model `stepModel B` *resolves* Core's choice: its step facts are Core
successors up to `CfgRel`, and it has one whenever Core has one.

* `toModelUniv`, `toModelExist`: one-sided transitions on all of `Dom` (universal sentences
  preserved, existential sentences reflected).
* `sat_iff_indep`, `sat_iff_indep_BI`: two-sided on all of `Dom` for choice-independent
  `CfgRel`-respecting sentences.
* `toModelUpTo K`: an `equal` transition on `DomUpTo K` for sentences respecting `CfgRel` and `K`;
  `sat_iff_of_domDet` (`K := Eq`) and `canStep_iff`, `stuck_iff` (`K := ⊤`) are its two ends.
* `sat_iff_primitives`: the fragment does not see which admissible primitives were chosen.
* `mstep_iff_backend`: the step facts of `stepModel B` are `Round6.Int.backend.step B`.
* `toUnion`: the set-valued model is equal to Core on `Dom`, **conditional** on the frozen
  `Task.choiceCover`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Nondet.halves_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Nondet.halves_BI

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Nondet.sat_iff_indep_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Nondet.sat_iff_indep_BI

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Nondet.toModelUpTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Nondet.toModelUpTo

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Nondet.canStep_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Nondet.canStep_iff

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Nondet.sat_iff_of_domDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Nondet.sat_iff_of_domDet

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Nondet.toUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Nondet.toUnion
