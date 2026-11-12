module

public import Silmaril.Wasm.SpecTec.Sim10.Whole.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Assemble9
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Assemble11

/-!
# The 1.0 backward target: what is proved

* `Sim10.Whole.closed_step10`, `sstepB10_iff`: on 1.0's `Step` the backend reading is the
  declarative reading (kernel `rfl` closedness check).
* `Sim10.Whole.backward10_of_parts`: the five structural rules of 1.0's `Step` (`pure`, `read`,
  `ctxt-label`, `ctxt-frame`, `ctxt-instrs`) are V1's `pure`, state-keeping steps, `label`, `frame`
  and `context`, for every configuration and any invariant passing to bodies and infixes.
* `Sim10.Whole.wholeStepBwd10_of_parts`: `Task.wholeStepBwd10` from the per-rule obligations
  `BwdParts10 GoodV1` at the spec's builtins.
* `Sim10.Whole.wholeStepBwd10_of_rest`: `Task.wholeStepBwd10` from `BwdRest10`, the rules not yet
  discharged. `Step_pure` 0–6, 10, 11, 18, 19, 28 are discharged (`PureCtrl`); for the 12 rules the
  census finds shared with 2.0, the 2.0 rule constants are the 1.0 rules (`hasRuleAt10_*`, kernel
  `rfl`).
* `Sim10.Whole.wholeStepBwd10_of_rest2`: `Task.wholeStepBwd10` from `BwdRest10b`. On top,
  `Step_read` 0–2, 6, 7 and `Step` 5 are discharged at every builtins (`StateVar`, `ReadCtrl`) and
  `Step` 11 (`memory.grow-succeed`) is dead at the spec's builtins.
* `Sim10.Whole.wholeStepBwd10_of_rest3`: `Task.wholeStepBwd10` from `BwdRest10c`. On top,
  `Step_pure` 7, 8, 14–17 are discharged with 2.0's environment-generic evaluation lemmas
  (`PureVals`).
* `Sim10.Whole.wholeStepBwd10_of_rest4`: `Task.wholeStepBwd10` from `BwdRest10d`. On top,
  `Step_pure` 12, 13 (`br_table-*`), which are 2.0's rules with 1.0's quantifiers (`withQs`).
* `Sim10.Whole.wholeStepBwd10_of_rest5`: `Task.wholeStepBwd10` from `BwdRest10e`. On top,
  `Step` 12 (`memory.grow-fail`), through `$inv_signed_`'s one shared definition.
  **Left** (`BwdRest10e`): `Step_pure` 9 (`br-succ`), 20–27 (numeric); `Step_read` 3–5
  (`call_indirect-*`, `call_addr`), 8–11 (loads), 12 (`memory.size`); `Step` 6 (`global.set`),
  7–10 (stores).
* `Sim10.Whole.wholeStepBwd10_of_rest6`: `Task.wholeStepBwd10` from `BwdRest10f`. On top,
  `Step_pure` 9 (`br-succ`, through the 1.0 typing inversion `labelidx10_inv`) and `Step` 6
  (`global.set`, under `GoodV1`'s `GSetOk`). **Left** (`BwdRest10f`): `Step_pure` 20–27; `Step_read`
  3–5, 8–12; `Step` 7–10.
* `Sim10.Whole.wholeStepBwd10_of_rest7`: `Task.wholeStepBwd10` from `BwdRest10g`. On top, the four
  load/store trap rules (`Step_read` 8, 10; `Step` 7, 9), at every builtins, and the four
  load/store value rules (`Step_read` 9, 11; `Step` 8, 10), which never fire at `floatIntB`
  (it answers neither `$bytes_` nor `$ibytes_`; vacuous, as for 2.0). **Left** (`BwdRest10g`):
  `Step_pure` 20–27; `Step_read` 3–5, 12.
* `Sim10.Whole.wholeStepBwd10_of_rest8`: `Task.wholeStepBwd10` from `BwdRest10h`. On top,
  `Step_read` 12 (`memory.size`; the page count is below `2 ^ 32` by the IL typing of the result,
  `lt_of_typed_constI32_10`). **Left** (`BwdRest10h`): `Step_pure` 20–27; `Step_read` 3–5.
* `Sim10.Whole.wholeStepBwd10_of_rest9`: `Task.wholeStepBwd10` from `BwdRest10i`. On top,
  `Step_read` 3 (`call_indirect-call`) and 5 (`call_addr`, V1's `invokeWasm`). **Left**
  (`BwdRest10i`): `Step_pure` 20–27 (numeric) and `Step_read` 4 (`call_indirect-trap`).
* `Sim10.Whole.wholeStepBwd10_of_rest10`: `Task.wholeStepBwd10` from `BwdRest10j`. On top,
  `Step_pure` 20–27 (the numeric rules, `bwd10_num`) under the 1.0 numeric agreement
  `Sim10.NumAgree10`, which holds at the spec's builtins (`numAgree10_floatIntB`, `Sim10.Num.Thms`).
  **Left** (`BwdRest10j`): `Step_read` 4 (`call_indirect-trap`).
* **`Sim10.Whole.wholeStepBwd10 : Task.wholeStepBwd10`.** `call_indirect-trap` is discharged at
  every builtins (`bwd10_callIndirectTrap`): where V1 would call, `call_indirect-call` fires forward
  (`body10_callIndirect`), with its quantifiers typed by the trap rule's own (`z : state`,
  `i : val_(I32)`, `x : idx`), against the `otherwise` premise.

The axiom audit of the reduction:
-/

/--
info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10_of_rest5' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10_of_rest5

/--
info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10_of_rest6' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10_of_rest6

/--
info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10_of_rest7' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10_of_rest7

/--
info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10_of_rest8' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10_of_rest8

/--
info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10_of_rest9' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10_of_rest9

/--
info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10_of_rest10' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10_of_rest10

/--
info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.wholeStepBwd10
