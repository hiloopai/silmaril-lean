module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Target.Assemble
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Target.Multi

/-!
# SpecTec ↔ Core 3.0, round 6, track target: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.Target`; see `docs/projects/spectec/README.md`.

* `forwardR'`: every Core step from a bounded configuration whose redex is not a cast is matched
  by a declarative SpecTec step up to Core's choice (`FwdUpR`), at the concrete builtins, for an
  injective encoding and a finite host. No open leaf.
* `backwardNC`: every declarative SpecTec step from a typed `NoCastV` configuration (`ReadValidS`,
  no cast redex) is the image of a Core step up to `ConfigEq`, at the concrete builtins. No open
  leaf; the vector rules use `Round5.Convert.VecAgreeNC` and `VecConvertR` instead of the false
  `Vec.VecAgree`.
* `wholeStepValidR_of_open`: `Round6.Task.wholeStepValidR Rd` from `OpenR Rd` (the transfer lemma
  `Transfer` and the cast leaf `Casts`) alone.
* `fwdRelR_of_open`, `bwdRelR_of_open`, `runsR_of_open`: the multi-step corollary from `OpenR`:
  deterministic Core runs (`DetSteps`) are runs of the reading, and runs of the reading are Core
  runs, up to `ConfigEq`, from valid sources whose runs stay `BoundedSel`.
* `transfer_declarative`, `wholeStepValidR_declarative_of_sel`: at round 5's reading, the transfer
  lemma holds and the new target asks no more than `Round5.Task.wholeStepValidSel`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Target.forwardR'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round6.Target.forwardR'

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Target.backwardNC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round6.Target.backwardNC

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Target.wholeStepValidR_of_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Round6.Target.wholeStepValidR_of_open

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Target.runsR_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round6.Target.runsR_of_open
