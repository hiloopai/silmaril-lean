module

public import Silmaril.Wasm.SpecTec.Sim.Prims.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Prims.Assembly

/-!
# The concrete `B` (builtins track, integrated): what is proved

`Prims.builtins prof hn host : Builtins` (`Prims/Defs.lean`) interprets the float and conversion
primitives of the profile `prof` (`Floats.floatCall prof`, also `$wrap__`/`$extend__` at every
width), the integer primitives (`IntNumeric.intCall`), `$hostcall`, `$unrolldt` and `$blocktype_`
at `_IDX`. For it:

* `floatB_builtins`, `intB_builtins`: `Floats.FloatB prof` and `IntNumeric.IntB` hold together.
* `assumptions_builtins`: `Whole.Assumptions (builtins prof hn host) hn host` from the typing parts
  (`TypingInputs`), `HostFinite host`, `HostRespects hn host` and three residual facts
  (`Residual`: `RefOkBridge`, `$inst_reftype`, `CtrlCall.default`). Discharged: `IntB`, `RFuns`,
  `RStoreFuns` but `instReftype`, `CtrlState`, `CtrlCall.expand`, `CtrlHost.hostcall`/`liftResult`,
  all of `Exn.Helpers` (including `tag_inv`, `expand_inv`, `blocktype_inv`).
* Pieces: `dderives_expand`/`expand_of_dderives` (SpecTec's `Expand` on images is Core's),
  `applies_unrolldt`, `applies_blocktype`/`blocktype_inv`, `ctrlHost_hostcall`, `applies_tag`/
  `tag_inv`, `applies_addExn`, `applies_liftResult`, `applies_asDeftype`.

Round 2's refutation `not_ctrlCallDefault` (no `B` satisfies `CtrlCall.default`) depended on the
evaluator not testing `SubE` argument patterns; after the typing track's fix (`Sem.argSubOk`) it
no longer holds and is retired (`Prims/Default.lean`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim.Prims

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Prims.assumptions_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms assumptions_builtins
/-- info: 'Silmaril.Wasm.SpecTec.Sim.Prims.intB_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intB_builtins
/-- info: 'Silmaril.Wasm.SpecTec.Sim.Prims.expand_of_dderives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms expand_of_dderives
/-- info: 'Silmaril.Wasm.SpecTec.Sim.Prims.blocktype_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blocktype_inv
