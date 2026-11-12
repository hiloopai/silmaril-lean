module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.Encode
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.Ops
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.Reduce
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.Host
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.Ops2
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.Comp

/-!
# SpecTec ↔ Core 3.0, round 7: the export swap at the value level (round 2, pass 4)

The value layer of `Round7.Task.swapEquiv`. `Task.swapEquiv` itself is **not** proved here.

* `eraseV_inj`, `unerase_eraseV`: under `QInj Q`, `eraseV` is injective on `AllIn Q` values.
* `eraseV_configV`: `eraseV (configV hn c) = configV hn (stripConfig c)`.
* `allIn_configV`: the only records of `configV hn c` with an `EXPORTS` field are the images of
  the module instances of `c`.
* `qInj_QC`: under `StripInj c`, `eraseV` is injective on `QC c`.
* `eq_configV_unstrip`: under `StripInj c`, a value that is `AllIn (QC c)` and erases to the
  image of an export-free `d` is the image of `mapConfig (unstrip c) d`.
* `field?_eraseV`, `setField_eraseV`, `idx?_eraseV`, `setIdx_eraseV`, `slice?_eraseV`,
  `setSlice_eraseV`, `len?_eraseV`, `beq_eraseV`, `contains_eraseV`: `eraseV` commutes with the
  value operations of the evaluator that do not name `EXPORTS`, and equality reads alike on
  `AllIn Q` values. `AllIn.setField` keeps `AllIn Q` only at records without an `EXPORTS` field.

* `swapEquiv_of_stepErase : Task.stepErase → Round7.Task.swapEquiv`, and
  `wholeStepValidREI_of_stepErase : Task.stepErase → Round7.Task.wholeStepValidREI`: the encoding
  side of `Task.swapEquiv` is done; what remains is the evaluator-level leaf `Task.stepErase`.

* `host_mods_sub` (pass 5): a finite, export-parametric host returns only module instances of
  the store it was called in; `allIn_outcomeV_of_host`: so its outcomes stay in `AllIn Q` when
  the calling store's module records satisfy `Q`; `hostcallCall_erase`,
  `hostcallCall_erase_typed`: round 4's `$hostcall` commutes with `eraseV` up to the order of its
  answer (item 3 of the plan for `Task.stepErase`).
* `asTuple?_eraseV`, `asList?_eraseV`, `asOpt?_eraseV`, `asCase?_eraseV`, `cat?_eraseV`,
  `AllIn.cat?`, `unValue_eraseV`, `binValues_eraseV`, `boolShort_eraseV`, `cmpValues_eraseV`,
  `memValue_eraseV`, `eraseV_struct_of_noExp`, `allIn_struct_of_noExp` (pass 5): the remaining
  value operations of the evaluator (`Swap/Ops2.lean`).
* `comp?_eraseV`, `compFields?_eraseVf`, `nxB_comp?`, `AllIn.comp?_of_nxB` (round 3, pass 1):
  record composition `Value.comp?` commutes with `eraseV` when every `EXPORTS` field holds a list
  (`expLB`), and composes values without `EXPORTS` records to such values (`Swap/Comp.lean`).

**Open:** `Task.stepErase`, i.e. the evaluator layer (an invariant over the 29 members of `Sem.evalExp` relating
evaluation at a scope `ρ` with evaluation at `eraseV ∘ ρ`), which needs every field update to
hit a record without an `EXPORTS` field (typed update roots, G9 §3.1), and the `$hostcall`
primitive up to the order of its outcome list (G9 §3.2).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Swap

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Swap.eraseV_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eraseV_inj

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Swap.eraseV_configV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eraseV_configV

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Swap.allIn_configV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allIn_configV

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Swap.qInj_QC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms qInj_QC

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Swap.eq_configV_unstrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eq_configV_unstrip

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Swap.beq_eraseV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms beq_eraseV

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Swap.wholeStepValidREI_of_stepErase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidREI_of_stepErase

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Swap.host_mods_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms host_mods_sub

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Swap.hostcallCall_erase_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hostcallCall_erase_typed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Swap.memValue_eraseV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memValue_eraseV

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Swap.comp?_eraseV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms comp?_eraseV

end Silmaril.Wasm.SpecTec.Sim.Round7.Swap
