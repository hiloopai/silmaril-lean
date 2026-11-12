module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxSites.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Value
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Assemble
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Typing

/-!
# Round 7, REH route 2: which comparisons reachable from `Step` can see a module record (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.NxSites`; see `docs/projects/spectec/README.md`. Definitions are in `Round7/NxSites/Defs.lean`.

* **The static check** (kernel, over the fixed wasm-3.0 script):
  * `itemsOk_fixed`: every signature entry of `sigFixed` agrees with the script, and every
    definition, relation and type reachable from `Step` has no comparison, membership test,
    repeated pattern variable or `matchDefault` form where both sides may hold an `EXPORTS`
    record, except at binding sites of rules;
  * `bindSites_fixed`: there are six binding sites, all top-level positive premises of the
    `call_ref-func`, `call_ref-hostfunc-res` and `call_ref-hostfunc-div` rules of `Step`;
  * `reachBad_fixed`: the ten reachable types that may hold a module record.
* **The value facts** that make a passing site safe without injectivity:
  `eraseV_eq_iff_of_nx`, `cmpValues_eraseV_nx`, `memValue_eraseV_nx`.
* **The link for checked types**: `nxB_of_HasTyp_utf8Env`. A value of an export-free type (in
  the sense of `sigFixed`) in `utf8Env B` is export-free. So every rule quantifier of an
  export-free type, which `Sim.QuantsOk` types at runtime, holds an export-free value
  (`nxB_of_quantsOk`).

Not proved here: that the static types of definition clause variables and call results are
their runtime types (evaluator type preservation). So the check does not yet discharge any
`QInj` use in `Round7.EraseAll`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxSites

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxSites.itemsOk_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms itemsOk_fixed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxSites.bindSites_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms bindSites_fixed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxSites.cmpValues_eraseV_nx' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms cmpValues_eraseV_nx

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxSites.memValue_eraseV_nx' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms memValue_eraseV_nx

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxSites.nxB_of_HasTyp_utf8Env' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms nxB_of_HasTyp_utf8Env

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxSites.nxB_of_quantsOk' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms nxB_of_quantsOk

end Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
