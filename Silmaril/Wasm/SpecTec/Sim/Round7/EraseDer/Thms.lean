module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.HostRule

/-!
# Round 7, the export swap: derivations move across erasure (round 4, pass 1)

Item 4 of the plan for `Round7.Swap.Task.stepErase`, for the relations of the checked part of the
wasm-3.0 script (`Round7.EraseAll.grE`: every relation `Step` reaches except `Step` and
`Step_read`). All proofs are unrefined, under `Raw/…/Round7/EraseDer/`.

**Kernel checks** (`decide +kernel`): every reachable rule is closed over its quantifiers
(`closedRels_fixed`); every type over `tyB` passes the typing check `xTy` (its expressions pass
the evaluator-level check, its type arguments are closed, and `moduleinst`'s `EXPORTS` field has
type `exportinst*`, no premises, and sits in an instance without argument patterns)
(`xTypMap_fixed`); every quantifier type of a reachable rule passes it (`xRelQuants_fixed`).

**Derivations.**

* `dderivesB_fwd`: a derivation whose rule instances bind every quantifier to a swap-set value
  (`DDerivesBQ (AllIn Q)`) gives one at the erased arguments and value, given typing towards the
  erased side (`TypFwd`) and a reading of `otherwise` that goes across.
* `dderivesB_bwd`: a derivation on the erased side whose quantifiers are in the erased swap set
  (`AllIn (EImg Q)`) gives one of `unerase Q` of its value, given `TypBwd`.
* `otherwiseAtB_erase_iff`: `otherwise` reads alike at a swap-set input and at its erasure.
* `dderivesB_erase_fwd`, `dderivesB_erase_bwd`: the two with SpecTec's `otherwise`.

**Typing.** `typFwd_utf8Env` (typing goes to the erased side) and `typBwd_utf8Env` (it comes back,
given that the export lists of the swap set's records are typed, `QExp`). An ill-typed export
list is typed after erasure, so the forward statement is an implication.

**At a configuration** (`StripInj c`, `NamesBnd c`, round 6's primitives):
`dderivesB_QC_fwd` and `dderivesB_QC_bwd` hold without further hypotheses.

**`Step_read`** (round 4, pass 2). The mode analysis holds at any checked part (`GFacts`,
`dderivesB_AIg`), and typing across erasure does not depend on the definition set (`typFwd_gd`).
So the transfers hold at `grB` (`grE` with `Step_read`): `dderivesB_QCB_fwd`, `dderivesB_QCB_bwd`,
and for `Step_read` itself `sReadB_QC_fwd`.

**`Step`** (round 4, pass 2). Every rule of `Step` except four passes a kernel check at `grB`
(`xStepOk_fixed`): its premises are `Step` premises or checked premises without `otherwise`. The
four (`excNames`) are `call_ref-hostfunc-res`/`-div` (`$hostcall`) and `table.grow-succeed`/
`memory.grow-succeed` (`$with_tableinst`/`$with_meminst`). `stepFwd`, `stepBwd`: `Step` commutes
with erasure given those four (`RuleFwd`, `RuleBwd`), by recursion through the context rules. At a
configuration this is `sStepB_QC_fwd`/`_bwd`, and the frozen `Task.stepExc` (the four rules at
`QC c`) gives `Round7.Swap.Task.stepErase` (`stepErase_of_stepExc`), hence
`swapEquiv_of_stepExc` and `wholeStepValidREI_of_stepExc`.

**The grow rules** (round 4, pass 2). A typed `z : state` is a state whose store has no `EXPORTS`
field (`state_inv`), so round 3's `callDef_with*_state` applies to the conclusion
`(…; $with_*(z, x, y); …)` (`growConcl`, kernel check `xGrowOk_fixed`). So `table.grow-succeed` and
`memory.grow-succeed` commute with erasure (`ruleFwd_grow`, `ruleBwd_grow`), and only the two
host-call rules are left: the frozen `Task.stepHost` gives `Task.stepExc`
(`stepExc_of_stepHost`), hence `stepErase_of_stepHost`, `swapEquiv_of_stepHost` and
`wholeStepValidREI_of_stepHost`.

**The host-call rules** (round 4, pass 3). A kernel check (`xHostOk_fixed`) shows that
`call_ref-hostfunc-res`/`-div` have three checked premises and a fourth
`pat <- $hostcall(_HOSTFUNC hf, s, val^n)`, that the mode analysis on the three knows the
arguments and the store `s : store`, and that every other quantifier is bound by `pat`. The
pattern's value is an outcome of the host, so in the swap set (`Swap.allIn_outcomeV_of_host`).
The image of an export-free store typed `store` has one preimage (`storeV_uniq_typed`); an
erased-side store is export-free (`storeNE_of_eImg`); and a swap-set value that erases to its
image is the image of the un-stripped store (`storeV_unstrip`, the store form of
`Swap.eq_configV_unstrip`). With both halves of `HostExportBlind` this gives `ruleFwd_host`,
`ruleBwd_host`, so **`Task.stepHost` holds** (`stepHost_holds`), and with it `stepExc_holds`,
`stepErase_holds` (`Round7.Swap.Task.stepErase`), `swapEquiv_holds` (`Round7.Task.swapEquiv`)
and `wholeStepValidREI_holds` (`Round7.Task.wholeStepValidREI`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.closedRels_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms closedRels_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.xTypMap_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms xTypMap_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.dderivesB_fwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dderivesB_fwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.dderivesB_bwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dderivesB_bwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.otherwiseAtB_erase_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms otherwiseAtB_erase_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.typFwd_utf8Env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typFwd_utf8Env

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.typBwd_utf8Env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typBwd_utf8Env

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.dderivesB_QC_fwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dderivesB_QC_fwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.dderivesB_QC_bwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dderivesB_QC_bwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.dderivesB_QCB_fwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dderivesB_QCB_fwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.dderivesB_QCB_bwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dderivesB_QCB_bwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.sReadB_QC_fwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sReadB_QC_fwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.xStepOk_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms xStepOk_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.stepFwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepFwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.stepBwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepBwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.stepErase_of_stepExc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepErase_of_stepExc

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.swapEquiv_of_stepExc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms swapEquiv_of_stepExc

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.wholeStepValidREI_of_stepExc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidREI_of_stepExc

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.state_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms state_inv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.xGrowOk_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms xGrowOk_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.ruleFwd_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ruleFwd_grow

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.ruleBwd_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ruleBwd_grow

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.stepExc_of_stepHost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepExc_of_stepHost

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.stepErase_of_stepHost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepErase_of_stepHost

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.swapEquiv_of_stepHost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms swapEquiv_of_stepHost

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.wholeStepValidREI_of_stepHost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidREI_of_stepHost

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.xHostOk_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms xHostOk_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.storeV_uniq_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storeV_uniq_typed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.storeNE_of_eImg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storeNE_of_eImg

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.storeV_unstrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storeV_unstrip

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.evalExp_hostMem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalExp_hostMem_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.ruleFwd_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ruleFwd_host

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.ruleBwd_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ruleBwd_host

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.stepHost_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepHost_holds

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.stepExc_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepExc_holds

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.stepErase_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepErase_holds

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.swapEquiv_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms swapEquiv_holds

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.wholeStepValidREI_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidREI_holds

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
