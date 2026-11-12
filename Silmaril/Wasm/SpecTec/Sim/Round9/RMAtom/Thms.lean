module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.RMAtom.Assemble

/-!
# Round 9, rm: the flat rules are silent at memory SIMD code (round 9, pass 1, track rm)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom`; see `docs/projects/spectec/README.md`.

* `atomCode_sound`, `adminsMS_of_atomCfg`, `adminsMS_of_atomPure`: a rule whose left-hand code is
  flat (`atomCode`: values, `val`/`ref` quantifiers and instructions without bodies, none a memory
  SIMD instruction) fires only at code without memory SIMD instructions.
* `pureAtoms`, `readAtoms`, `stepAtoms` (kernel checks): 64 of the 79 rules of `Step_pure`, 77 of
  the 93 rules of `Step_read` off 42–51, and every rule of `Step` from 6 on off 22–25 are flat.
* `pure_adminsMS`, `read_adminsMS`, `step_adminsMS`: hence they fire only at such code.
* `restMSHCG_of_H`, `wholeStepValidRM_of_restDPH`: `Round7.MemSimd.Task.wholeStepValidRM` from
  `OpenRMRestDPH`, which has no `Step` obligation at memory SIMD code and asks the `Step_pure` and
  `Step_read` ones only at the 15 + 16 rules that are not flat (`structPure`, `structRead`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom.atomCode_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms atomCode_sound

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom.readAtoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readAtoms

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom.restMSHCG_of_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms restMSHCG_of_H

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom.wholeStepValidRM_of_restDPH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restDPH

end Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom
