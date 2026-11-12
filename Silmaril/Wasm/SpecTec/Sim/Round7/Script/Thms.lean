module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Env
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Witness
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.AgreeEq

/-!
# SpecTec ↔ Core 3.0, round 7: what SpecTec's `Step` can reach (pass 7, proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.Script`; see `docs/projects/spectec/README.md`.
Definitions are in `Round7/Script/Defs.lean`. Every fact below is a kernel computation
(`decide +kernel`) over the fixed wasm-3.0 script, split into ten chunks
(`Round7/Script/Chunk0.lean` … `Chunk9.lean`) and put together in `Round7/Script/Assemble.lean`.

* **Closure**: `stepReach_closed`. The 430 names of `stepReach` (relations, definitions, types)
  contain `Step` (`step_mem_stepReach`) and every reference made by one of them.
* **No `EXPORTS` in expressions**: `stepReach_noExports`. No reachable expression builds a record
  with an `EXPORTS` field, projects `.EXPORTS` or updates along `.EXPORTS`. The atom occurs only in
  the declaration of the type `moduleinst` (`moduleinst_declares_exports`).
* **`$utf8` only from `name`**: `stepReach_utf8`. Among reachable definitions only `$utf8` itself
  and the type `name` call `$utf8` (and `name` does: `name_calls_utf8`).
* **Record composition only in `Deftype_ok`**: `stepReach_comp` (`deftype_ok_comp`). It composes
  validation contexts, not module instances.
* **Record updates**: `stepReach_upd`. Every reachable update `e[p = e']` or `e[p =.. e']` starts at
  `$sof(…)`, `$fof(…)` or `$lanes_(…)`, and its path has no `MODULE`, `FUNCS` or `EXPORTS` step
  (`with_tableinst_upd` is one).
* **Lookups**: `findDef?_reach`, `findRel?_reach`, `findTyp?_reach`. What `simEnv B` returns for a
  reachable name is closed and harmless; `findDef?_utf8Env_item` adds `$utf8` without clauses in
  `utf8Env B`.

**`simEnv B` and `utf8Env B` agree away from `$utf8`** (`AgreeEq.lean`, from the unrefined
`Raw/…/Round7/Script/Agree.lean`), for `B` that leaves `$utf8` uninterpreted: at every fuel,
`evalExp_utf8Env_eq`, `matchExp_utf8Env_eq`, `premsHold_utf8Env_eq`, `callDef_utf8Env_eq` and
`derives_utf8Env_eq` on terms whose references are `GoodEvs` (reachable, not `$utf8`), in
`DefsOk` scopes with `ArgOk` arguments; fuel-free, `evalExp_utf8Env_iff` and
`derives_utf8Env_iff`. In particular the evaluator's own (fuelled, untyped) reading of `Step`
is unchanged by the erratum at every value: `derives_step_utf8Env_iff`.

These are the script facts the planned proofs of `Round7.Task.swapEquiv` and
`Round7.Task.envAgreeNE` need. They are not those proofs: see the doc section for what remains,
and for why the update fact does not by itself make the value swap commute with `pathSet`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Script.scriptOk_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.Script.scriptOk_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Script.stepReach_upd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.Script.stepReach_upd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Script.findDef?_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.Script.findDef?_reach

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Script.evalExp_utf8Env_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.Script.evalExp_utf8Env_eq

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Script.derives_step_utf8Env_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round7.Script.derives_step_utf8Env_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Script.name_calls_utf8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.Script.name_calls_utf8
