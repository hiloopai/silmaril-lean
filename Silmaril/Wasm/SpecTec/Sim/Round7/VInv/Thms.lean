module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VInv.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VInv.Assemble
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VInv.Whole

/-!
# Round 7, memory SIMD: `OpenRMRest.rest` off memory SIMD code, and a concrete step invariant

* **`rest` on the memory-SIMD-free domain** (`backwardUpToDRestS_noMSDom`,
  `backwardUpToDRestS_noMSDom_BM`): at `BI` and at `BM`, the per-rule backward obligations off the
  memory SIMD rules hold at every `NoCastVM` configuration without memory SIMD code (code and store
  function bodies, at any depth) whose Core successors have none either (`NoMSDom`). Round 6's
  leaves (`Round6.Target.backwardUpToNC`) apply there because `configVD` is `configV` off memory
  SIMD code, and `CodeEq` keeps memory-SIMD-free code (`adminsMS_of_codeEq`).
* **What is left of `rest`** (`rest_of_restMS`, `restMS_of_rest`): `OpenRMRest.rest` is
  equivalent to `RestMS`, the same obligations at `BI` on the `NoCastVM` configurations outside
  `NoMSDom`. `openRMRest_of_MS`, `wholeStepValidRM_of_restMS`: the frozen target from
  `OpenRMRestMS` (`OpenRMRest` with `RestMS` for `rest`).
* **A concrete step invariant** (`stepInv_noMS`, `stepInvB_noMS`): `LhsNoAtoms msAtoms`, no memory
  SIMD instruction in the left-hand side at any depth, is a `VDecl.StepInv` and a `StepInvB`. The
  passage through `Step` rules 1–5 reads their conclusions on values: the left-hand sides are in a
  small fragment (kernel check `ctx_lhsOk`), and evaluation in that fragment moves `NoAtoms`
  between a value and the variables it reads (`vars_of_eval`, `noAtoms_of_eval`).
  `sstep_withVBytes_iff_noMS`: the whole step reads alike at `withVBytes B` and at `B` on such
  values.
* **The backend reading** (`sstepB_withVBytes_iff`, `sstepB_withVBytes_iff_noMS`,
  `sreadB_withVBytes_iff_of_noAtoms`): the same for `SStepB` and `SReadB`, under a `StepInvB`
  (`Raw/…/Round7/VInv/StepB.lean`, `VDecl.dderivesQ`'s recursion for `DDerivesB`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VInv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VInv.ctx_lhsOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ctx_lhsOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VInv.backwardUpToDRestS_noMSDom_BM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms backwardUpToDRestS_noMSDom_BM

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VInv.rest_of_restMS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rest_of_restMS

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VInv.wholeStepValidRM_of_restMS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restMS

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VInv.stepInv_noMS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepInv_noMS

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VInv.stepInvB_noMS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepInvB_noMS

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VInv.sstep_withVBytes_iff_noMS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_withVBytes_iff_noMS

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VInv.sstepB_withVBytes_iff_noMS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstepB_withVBytes_iff_noMS

end Silmaril.Wasm.SpecTec.Sim.Round7.VInv
