module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Utf8.Export
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Utf8.CrossCheck
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Utf8.MonoDerive

/-!
# SpecTec ↔ Core 3.0, round 7: what the `$utf8` erratum gives (proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7`; see `docs/projects/spectec/README.md`

* **The erratum changes only `$utf8`**: `findDef_utf8_base` (the fixed script's `$utf8` has the
  signature `utf8Params → utf8Res` and the looping first clause), `findDef?_utf8Env` (no clauses
  in `utf8Env B`), `findDef?_utf8Env_of_ne`, `findTyp?_utf8Env`, `findRel?_utf8Env`,
  `findGram?_utf8Env` and `call_utf8Env_of_ne` (everything else is `simEnv B`'s).
* **The primitive is `String.toUTF8`**: `utf8Call_string`, `applies_utf8`.
* **Names and exports are typed**: `hasTyp_char`, `hasTyp_name`, `hasTyp_externaddr`,
  `hasTyp_exportinst`, for names with fewer than `2 ^ 32` UTF-8 bytes.
* **The contrast with round 5/6**: `name_erratum` and `exportinst_erratum`. A one-character name
  or export is untyped in every `simEnv B` and typed in every `utf8Env B`.

* **Cross-check with the main stream (#656, pass 3)**: `utf8_crossCheck_656`. On U+1F601 the
  erratum answers `F0 9F 98 81` (`applies_utf8_grin`); main's `$utf8single` accepts those bytes
  in its four-byte clause, and the pinned script's own four-byte clause of `$utf8` rejects them.
  The erratum is per character, like main's `$utf8 = concat_($utf8single(ch)*)`
  (`utf8Call_concat`). This is a one-character witness, not a proof that main's clauses define
  `String.utf8EncodeChar` everywhere.

**Pass 4:** `Round7.Task.wholeStepValidREH` (frozen in `Defs.lean`) is the target with
`HostExportBlind host` added: the host's behaviour commutes with removing every export from the
store (`stripStore`, `stripOutcome`). `wholeStepValidREH_of_wholeStepValidRE` shows it is weaker.

**Pass 5: environment monotonicity from `simEnv B` to `utf8Env B`** (for `B` that leaves `$utf8`
uninterpreted, which round 6's `BI P hn host` does: `BI_utf8`):

* `envMonoAt`, `envMonoTypAt` (unrefined copies of `Sem.monoAt_succ` and `Sem.monoTypAt_succ`
  with the environment varying instead of the fuel): every member of the evaluator and typing
  blocks answers in `utf8Env B` at least what it answers in `simEnv B`, in `Res.Le`. The one
  non-congruence case is `utf8_le`: `$utf8` by `simEnv B`'s clauses is below the primitive.
* Fuel-free: `evalExp_utf8Env`, `evalArgs_utf8Env`, `evalDoms_utf8Env`, `hasTyp_utf8Env`,
  `typedV_utf8Env`, `quantsOk_utf8Env`, and positive derivations `dderivesB_utf8Env` (along any
  inclusion of `otherwise` readings; `dderivesB_noElse_utf8Env`).
* Not moved: `SStepB`, whose `otherwiseB` premises are negative.

**Open:** `Round7.Task.wholeStepValidRE` and `Round7.Task.wholeStepValidREH`. Monotonicity moves
values, typings and positive derivations, but not `SStepB` (its `otherwise` premises are
negative), so the round-6 chain still does not transfer. The planned route also needs export
stripping of SpecTec derivations, which is not formalised; see `docs/projects/spectec/README.md`.
-/

/-! ## The host-blind restatement (pass 4) -/

public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

/-- **The host-blind restatement is weaker than the frozen target.** `Task.wholeStepValidREH` adds
the hypothesis `HostExportBlind host`; it is the statement the planned export-stripping route can
prove. -/
theorem wholeStepValidREH_of_wholeStepValidRE (h : Task.wholeStepValidRE) :
    Task.wholeStepValidREH :=
  fun H hn hinj host hf hh _ nd r => h H hn hinj host hf hh nd r

/-- `HostExportBlind` is satisfiable by a `HostOk`, finite host: round 5's diverging host. -/
theorem hostExportBlind_divHost : HostExportBlind Round5.Pos.divHost :=
  ⟨fun _ _ _ o (h : o = .diverged) => by subst h; rfl,
    fun _ _ _ o' (h : o' = .diverged) => ⟨.diverged, rfl, h⟩⟩

end Silmaril.Wasm.SpecTec.Sim.Round7

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.applies_utf8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.applies_utf8

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.hasTyp_name' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.hasTyp_name

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.name_erratum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.name_erratum

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.hasTyp_exportinst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.hasTyp_exportinst

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.exportinst_erratum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.exportinst_erratum

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.findDef?_utf8Env_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.findDef?_utf8Env_of_ne

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.utf8_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.utf8_le

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.envMonoAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.envMonoAt

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.envMonoTypAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.envMonoTypAt

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.dderivesB_utf8Env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.dderivesB_utf8Env

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.BI_utf8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.BI_utf8

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.utf8_crossCheck_656' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.utf8_crossCheck_656
