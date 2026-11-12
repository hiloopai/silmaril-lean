module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxErase.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxErase.StepRest
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.Assemble
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxErase.Rule

/-!
# Round 7, REH route 2: the expression members commute with erasure without `QInj` (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.NxErase`; see `docs/projects/spectec/README.md`. Definitions are in `Round7/NxErase/Defs.lean`; the proofs are unrefined, in
`Silmaril/Raw/…/Round7/NxErase/`.

* **`nAt`**: given that the primitives of `gd` names commute with erasure
  (`EraseAll.BIErase QT gd env`), `NAt gr gd env k` holds at every fuel: the twelve expression
  members of the evaluator, run on the erased scope, give the erased answer, on syntax that
  passes the flow check, the side conditions, the site check and round 3's syntactic check, in
  a conforming scope whose calls conform and whose clause bodies commute with erasure
  (`CallE`). No swap set, and so no injectivity of erasure, is assumed.
* The proof is round 3's `EraseAll.step_*` with every value in the swap set. At `=`, `≠` and
  membership tests the site check gives an `nxE` operand, `NxFlow.expAt` makes its value
  export-free (`nx_of_site`), and `NxSites.cmpValues_eraseV_nx`/`memValue_eraseV_nx` replace
  the uses of `QInj`. The rounds of an iteration conform by `NxFlow.rowScope_opt`/`_list`.
* **`xItems_fixed`** (kernel, twenty slices): the side conditions of the copy hold on the fixed
  script. Every clause of every reachable definition, in every mode, passes the site check in
  its own signature (`NxTyped.clauseSig`, which the soundness proof uses, rather than
  `NxSites.sigFixed`, which the site check of round 6 used), and its argument patterns,
  premises and body pass `auxX`; every reachable rule passes `auxX`.
* **At rule instances** (`Round7/NxErase/Rule.lean`): in a rule instance of a reachable relation
  whose quantifiers `Sim.QuantsOk` types, every conclusion alternative (`erase_alt`) and every
  top-level `if` condition other than the six binding sites (`erase_ifPr`) evaluates on the
  erased scope to the erased value, given `CallE` in the instance's quantifier scope.
  `Task.clauseErase` (frozen, open) states `CallE` for every such scope; `erase_ifPr_of_task`
  is the result conditional on it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxErase

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxErase.nAt' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms nAt

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxErase.xItems_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms xItems_fixed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxErase.erase_ifPr_of_task' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms erase_ifPr_of_task

end Silmaril.Wasm.SpecTec.Sim.Round7.NxErase
