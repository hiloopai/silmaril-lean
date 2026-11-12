module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Erase.FO
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Erase.Path

/-!
# Round 7, the export swap: the evaluator layer, first-order fragment (round 3, pass 1, proved)

Item 1 of the plan for `Round7.Swap.Task.stepErase`, on its first fragment. Definitions are in
`Round7/Erase/Defs.lean`; see `docs/projects/spectec/README.md`.

* `eraseFO`: at every fuel, on a scope in the swap set (`ScopeIn Q ρ`, `QInj Q`) and a first-order
  expression (`FO e`: no call, iteration, update, extension, composition or `EXPORTS` atom),
  `evalExp n env (eraseScope ρ) e` is `evalExp n env ρ e` with its answer erased, and that answer
  is `AllIn Q`. `foAt` is the three-member induction (`evalExp`, `evalExps`, `evalExpFields`).
* `find?_eraseScope`, `ScopeIn.find?`, `EOK.bind`, `EOK.map`, `EOK.ofOption`, `mapM_erase`: the
  pieces the full 29-member induction reuses.

* `pathGet_erase`, `pathSet_erase_eq`: on first-order paths (`FOp`), reading and writing commute
  with erasing scope, root and written value.
* `eraseUpd`, `eraseExt`: the update `e₁[p = e₂]` and the extension `e₁[p =.. e₂]` with first-order
  parts commute with erasing the scope, and stay in the swap set **under `SafeWrites`** at the root
  `e₁` evaluates to (`Round7.Roots.allIn_pathSet`). This is where item 2 enters item 1: the
  hypothesis fails at `.TABLES[i]`/`.MEMS[i]` of a module image (`Roots.not_allIn_QC_tables`).

Not covered: `callDef`, `evalIterE`, matching, premises and relations. The proofs are in
`Raw/…/Round7/Erase/{FO,Path}.lean`, unrefined like the other round-7 evaluator inductions.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Erase

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Erase.eraseFO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eraseFO

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Erase.eraseUpd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eraseUpd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Erase.eraseExt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eraseExt

end Silmaril.Wasm.SpecTec.Sim.Round7.Erase
