module

public import Silmaril.Wasm.SpecTec.Sim20.Route.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Route
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.RouteT

/-!
# The 2.0 composite route: what is proved

In `Silmaril.Wasm.SpecTec.Sim20` (proofs in `Sim20.Route`):

* `composite20R : Task.composite20R`, the composite target with a possibly empty run of
  wasm-3.0 backend steps (`RSteps`) in place of `Task.composite20`'s `TransGen`;
* `composite20_sim` and `composite20_steps`: one V2 step, and V2 runs, along the copied Track E
  simulation `Step.toCore`/`Steps.toCore` and Round 6's `runsR_backend`, with no `TrackEFwd`
  hypothesis;
* `composite10_steps`: the start of the 1.0 route, 1.0 runs through the copied 1.0 → Lime1 → 2.0
  simulation `V1.Execution.Steps.toV2` and then `composite20_steps` (again about the 3.0 script;
  the 1.0 script enters through the census `census_*_10_20`);
* `detSteps_of_steps`, `runGood_parts`: the glue.

* **`composite20 : Task.composite20`** (`Sim20.RouteT`, an earlier step): the target as stated,
  with a non-empty run (`TransGen`). The earlier obstruction (the one-step results land on
  `ConfigEq`-twins and do not chain) is avoided by chaining along Round 6's own invariant `SimRel`,
  as `Round6.Target.stepsR_sim` does, which takes exactly one reading step per Core step
  (`stepsT_sim`); Track E's obligation gives a non-empty Core run, and `RunGood` makes each of its
  steps go to the only successor (`detTrans_of_trans`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.composite20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.composite20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.composite20R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.composite20R
