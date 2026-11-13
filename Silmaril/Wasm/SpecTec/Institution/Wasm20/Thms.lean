module

public import Silmaril.Wasm.SpecTec.Institution.Wasm20.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Wasm20

/-!
# The SpecTec specification institution and the Wasm atlas, at wasm-2.0: results

Namespace `Silmaril.Wasm.SpecTec.Institution.Wasm20`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.Wasm20`; see `docs/projects/spectec/README.md`, "an earlier step,
wasm20".

* `mem_stepModel20_iff`: the step facts of `stepModel20 B` are `SStepB (simEnv20 B)` (`Iff.rfl`).
* `bwd_scalar`: **unconditional backward half on the scalar fragment `DomS`**, at the spec's
  scalar builtins `floatIntB P`, every profile, host and encoding: every step fact of the model
  from the image of `c` is the image of a V2 step. `bwd_of_rest3`: on all of `DomW`, conditional
  on `Sim20.Whole.BwdRestW3`.
* `toModelS` (universal sentences, `preserves`) and `toModelSE` (existential sentences,
  `reflects`): transitions from the V2 step chart on `DomS` to `modelChart (stepModel20
  (floatIntB P))`; `sat_univ_exist` states them directly. `toModelW`, `toModelWE`: on `DomW`,
  conditional on `BwdRestW3`.
* `not_fwd_progress`, `not_bwd_stuck`, `not_equal_progress`: at `nop nop` (in `DomS`), V2 steps
  and every `stepModel20 B` is stuck, so no transition along `configV` preserves `progress`,
  reflects `stuckSen`, or is `equal` on a class containing `progress`. The wasm-3.0 shape
  (`Wasm30.sat_iff_stepModel`, two-sided) has no wasm-2.0 counterpart for the script as written.
* `model_step_nop1`: every `stepModel20 B` steps from the image of `nop` (a point of `DomS`), so
  the backward half has content.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Wasm20.bwd_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Wasm20.bwd_scalar

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Wasm20.bwd_of_rest3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Wasm20.bwd_of_rest3

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Wasm20.sat_univ_exist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Wasm20.sat_univ_exist

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Wasm20.not_fwd_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Wasm20.not_fwd_progress

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Wasm20.not_bwd_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Wasm20.not_bwd_stuck

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Wasm20.not_equal_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Wasm20.not_equal_progress

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Wasm20.model_step_nop1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Wasm20.model_step_nop1
