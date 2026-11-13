module

public import Silmaril.Wasm.SpecTec.Institution.FwdB30D.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30DDeep
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30DCtrl
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30DTables
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30DArity
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30DStore
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30DW20

/-!
# `Step` facts at `Wasm30.builtins` at non-rigid successors: results

Namespace `Silmaril.Wasm.SpecTec.Institution.FwdB30D`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.{FwdB30DDeep,FwdB30DCtrl,FwdB30DTables,FwdB30DArity,`
`FwdB30DStore,FwdB30DW20}`; see
`docs/projects/wasm-components.md`, "Stretch, instfwd (ws5 an earlier step)".

As in `FwdB30S`, the only knowledge of `Wasm30.builtins` used is `FwdX30Fin.stepObs_builtins`
(directly or through `FwdB30X.readX_two_sided`); everything else is about `Bwd.AdminEq` or
inversion of `Step` derivations at an arbitrary `B`.

* **Deep rigidity.** `cfgRel_exact_deep`: `CfgRel` from the image of a configuration whose code
  has no `CALL_REF` at the top, nor at the top of any label, handler or frame body at any depth
  (`deepRigidL`), is equality.
* **Labels and handlers.** `readX_exact_deep`: at a `ReadHeadX` redex with such a successor, the
  `Step_read` fact of `stepModel builtins` to the image of Core's successor exists, and it is the
  only one to typed code. `block_exact`, `loop_exact`, `tryTable_exact` (when the body has no
  `call_ref` at the top, `callFree`) and `throwRefHandlerNext_exact` (unconditionally).
  `ctrlRead_deep_cases`: the other `CtrlRead` successors not covered are `call`'s
  (`[ref, CALL_REF]`) and those of blocks whose body has a `call_ref` at the top.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30D.cfgRel_exact_deep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30D.cfgRel_exact_deep

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30D.readX_exact_deep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30D.readX_exact_deep

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30D.ctrlRead_deep_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30D.ctrlRead_deep_cases

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30D.block_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30D.block_exact

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30D.tryTable_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30D.tryTable_exact

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30D.throwRefHandlerNext_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30D.throwRefHandlerNext_exact

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30D.sstep_head_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30D.sstep_head_tail

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30D.structNew_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30D.structNew_exact

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30D.arrayNewFixed_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30D.arrayNewFixed_exact

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30D.throw_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30D.throw_exact

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30D.callRefNull_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30D.callRefNull_exact

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30D.callRefFunc_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30D.callRefFunc_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30D.callRefFunc_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30D.callRefFunc_exact

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30D.stepModel20_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30D.stepModel20_head
