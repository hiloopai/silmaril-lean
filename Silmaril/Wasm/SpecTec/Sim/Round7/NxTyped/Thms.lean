module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Value
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Ops
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Assemble

/-!
# Round 7, REH route 2: abstract typing of values, and the flow check (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped`; see `docs/projects/spectec/README.md`. Definitions are in `Round7/NxTyped/Defs.lean`.

* **The flow check** (kernel, over the fixed wasm-3.0 script):
  * `typItemsOk_fixed`: the aliases, fields and cases `sigExtra` records for the ten reachable
    types that may hold a module record agree with their type definitions;
  * `flowItems_fixed`: every definition and relation reachable from `Step` passes the flow
    check with `sigX` and `tsigFixed`: argument patterns bind conforming values, arguments flow
    into parameter types, bodies into result types, conclusions of relation premises into
    the relation's type, and every inferred type is justified. Generic definitions pass in
    both modes (type parameters unknown, and export-free). In the unknown mode their comparison
    sites pass `NxSites` with the type parameters no longer counted as export-free.
* **Conformance** (`Proofs/…/NxTyped/Value.lean`): `vtB_of_nxB`, `nxB_of_vtB`, `vtB_unk`,
  `vtB_of_triv`, `atEq_iff`, `vtB_of_atLe`.
* **The value operations preserve conformance** (`Proofs/…/NxTyped/Ops.lean`): reading
  (`vtB_field?`, `vtB_payload`, `vtB_proj`, `vtB_elem`, `vtB_elemOpt`), building (`vtB_take`,
  `vtB_drop`, `vtB_slice?`, `vtB_cat?`, `vtB_comp?`, `vtB_lift`, `vtB_list_of`,
  `vtB_optSome_of`) and writing (`vtB_setField`, `vtB_setIdx`, `vtB_setSlice`), each at the
  abstract types the flow check assigns.

Not proved here: that the evaluator preserves conformance (the soundness of the flow check).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped.flowItems_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms flowItems_fixed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped.typItemsOk_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms typItemsOk_fixed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped.vtB_of_atLe' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms vtB_of_atLe

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped.vtB_comp?' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms vtB_comp?

end Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
