module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Roots.Basic

/-!
# Round 7, the export swap: record updates and their roots (round 3, pass 1)

Item 2 of the plan for `Round7.Swap.Task.stepErase`, at the level of `pathSet`. Definitions are in
`Round7/Roots/Defs.lean`; see `docs/projects/spectec/README.md`.

* `allIn_pathGet`, `allIn_pathSet`: reading through a path keeps `AllIn Q`; a path update keeps it
  under `SafeWrites` (every record written into has no `EXPORTS` field or stays in `Q`), and
  `safeWrites_of_noExp` gives `SafeWrites` when no written record has an `EXPORTS` field.
* On a module-instance image (`modImg m`), the reachable update shapes:
  * `pathGet_modImg_absent`, `pathSet_modImg_absent_idx`, `pathSet_modImg_absent_slice`: a first
    step at an atom that is not a field of `moduleinst` (`LOCALS`, `STRUCTS`, `ARRAYS`, `EXNS`)
    fails;
  * `pathSet_modImg_dot`, `pathSet_modImg_dot_idx`, `pathSet_modImg_dot_slice`: `.A[e].B…` with `A`
    an address-list field (`GLOBALS`, `TABLES`, `MEMS`, `ELEMS`, `DATAS`, …) fails;
  * `pathSet_modImg_tables`, `pathSet_modImg_mems`: `.TABLES[0] = r` and `.MEMS[0] = r` succeed;
    `not_allIn_QC_tables`, `not_allIn_QC_mems`: with a record `r` their result leaves the swap set,
    although the root is in it (`allIn_QC_modImg`).

So the narrowed item 2 of pass 5 now holds in Lean at the value level: the swap set is lost only at
the two single-step updates `$with_tableinst`/`$with_meminst` make, and only when their root
`$sof(z)` is a module image. The shapes of the reachable update paths are read from the spec
source (`4.0-execution.configurations.spectec:293-311`); they are not checked against the IL here.
That `$sof(z)` is not a module image for a typed `state` `z`, and threading that through `callDef`,
is still open.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Roots

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Roots.allIn_pathSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allIn_pathSet

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Roots.pathSet_modImg_dot_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pathSet_modImg_dot_slice

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Roots.not_allIn_QC_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_allIn_QC_tables

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Roots.pathSet_modImg_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pathSet_modImg_tables

end Silmaril.Wasm.SpecTec.Sim.Round7.Roots
