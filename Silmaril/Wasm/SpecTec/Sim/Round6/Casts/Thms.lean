module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Casts.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Casts.Assemble

/-!
# SpecTec ↔ Core 3.0, round 6, track casts: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.Casts`; see `docs/projects/spectec/README.md`.

* `castStep_rec`: a Core step from a cast redex (`castB`, implied by `Target.CastRedex`) is a
  top-level cast step (`CastTop`) under values, labels, handlers and frames.
* `fwdB_cast`: such a step, from a bounded configuration, is an `SStepB` step between typed
  images, from `Reading.RefOkBB` (`castsFwdB_of`, lifted with `sstepB_ctxt*`).
* `fires_of_firesB_read`: every non-cast rule of `Step_read` that fires under the new reading
  fires under the old one, at **every** left-hand side (`readCheck`, over the script).
* `backwardB`: every `SStepB` step from a typed `ReadValidS` configuration is the image of a Core
  step up to `ConfigEq`, from `RefOkBB`; no cast redex and no transfer lemma is assumed.
* `succTypedB`: SpecTec successors of typed witnesses are typed, under the new reading.
* `casts_backend_of_refOkBB`, `casts_backend_spec_of_refOkBB`: **`Target.Casts Int.backend`
  from `RefOkBB`**, for an injective encoding and a finite `HostOk` host.
* `backwardR_backend_of_refOkBB`: the backward half of `Round6.Task.wholeStepValidR
  Int.backend`, from `RefOkBB`.
* `wholeStepValidR_backend_of_refOkBB`: `Round6.Task.wholeStepValidR Int.backend` from `RefOkBB`
  and the forward transfer lemma `TransferFwd` alone (no backward transfer lemma).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Casts.casts_backend_of_refOkBB' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Casts.casts_backend_of_refOkBB

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Casts.casts_backend_spec_of_refOkBB' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Casts.casts_backend_spec_of_refOkBB

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Casts.backwardB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Casts.backwardB

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Casts.backwardR_backend_of_refOkBB' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Casts.backwardR_backend_of_refOkBB

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Casts.fwdB_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Casts.fwdB_cast

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Casts.wholeStepValidR_backend_of_refOkBB' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Casts.wholeStepValidR_backend_of_refOkBB
