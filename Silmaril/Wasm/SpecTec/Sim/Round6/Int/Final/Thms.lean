module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Int.Final.Assemble

/-!
# SpecTec ↔ Core 3.0, round 6, integration (pass 4): the target, proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.Int`; see `docs/projects/spectec/README.md`.

* `agreeTy_BI`: `RefOkV.AgreeTy (simEnv (BI P hn host))` for every profile `P`, encoding `hn`
  and host, from tracks agreety-okintro, agreety-subintro and agreety-elim.
* `wholeStepValidR_backend : Round6.Task.wholeStepValidR Int.backend`: the restated round-6
  target, proved outright.
* `runsR_backend`: its multi-step corollary; `openR_backend`: `Target.OpenR Int.backend`.
* `round6_summary`: the proved target together with the refutations below.

The targets it replaces are refuted: `Round4.Task.wholeStepValid` (`Round5.Pos.not_wholeStepValid`),
`Round5.Task.wholeStepValidOk` (`Round5.Target.not_wholeStepValidOk`),
`Round5.Task.wholeStepValidSel` (`Round6.Refute.not_wholeStepValidSel`), and the same restated
target at the declarative reading (`Round6.Int.not_wholeStepValidR_declarative`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.agreeTy_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.agreeTy_BI

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.openR_backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.openR_backend

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.wholeStepValidR_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.wholeStepValidR_backend

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.runsR_backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.runsR_backend

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Int.round6_summary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Int.round6_summary
