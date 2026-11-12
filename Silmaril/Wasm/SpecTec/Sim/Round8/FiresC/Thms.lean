module

public import Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.FiresC.Assemble

/-!
# Round 8, function code erasure under the declarative reading (round 8, pass 3, rm)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round8.FiresC`; see `docs/projects/spectec/README.md`. Definitions are in `Round8/FiresC/Defs.lean`; the unrefined proofs are in
`Raw/…/Round8/FiresC/`.

* `hasTyp_erase`: **typing goes across `eraseC`**, at every type over `tyC` (every type `Step`
  reaches), in a scope whose type variables are bound to closed checked types. The `CODE` field is
  the one non-congruent case: `hostC u'` is a `funccode` whenever any `u` is, at the same fuel
  (`hasTyp_code`). Round 7's `EraseDer.TypFwd`, copied for `CODE` with every value in the swap set.
* `quantsOk_erase`, `premW_erase`, `ruleBody_erase`: quantifier typing, premises (given that
  their relation and `otherwise` premises move) and rule bodies go across `eraseC`.
* `dderives_erase`: **derivations of `Ref_ok`, `Expand` and the 25 validation relations they
  reach (`relG`) go across `eraseC`**, under any reading of `otherwise` (none of them has an
  `otherwise` premise; `relGOk_fixed`).
* `fires_erase_rel`: a rule with no `otherwise` premise whose relation premises are in `relG`
  (`relRule`) of a relation `Step` reaches keeps firing (`Sim.Fires`) at `eraseC v`.
* `firesEraseD_read`, `firesEraseD_step`: `RMCode.FiresEraseD` for the 75 rules of `Step_read`
  without `otherwise` (`relRead`) and every rule of `Step` from 6 on but 7–9 (`relStep`).
* `wholeStepValidRM_of_restDPF`: `Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPF`,
  which asks `FiresEraseD` only for the 28 `Step_read` rules with an `otherwise` premise.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.hasTyp_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hasTyp_erase

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.dderives_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dderives_erase

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.fires_erase_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fires_erase_rel

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.firesEraseD_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesEraseD_read

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.firesEraseD_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesEraseD_step

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.wholeStepValidRM_of_restDPF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restDPF

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
