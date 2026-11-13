module

public import Silmaril.Wasm.SpecTec.Institution.Instr30V.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30VBrnn

/-!
# Module typing of the wasm-3.0 script, ws5 results

Namespace `Silmaril.Wasm.SpecTec.Institution.Instr30V`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30V*`; see `docs/projects/spectec/README.md`,
"ws5 insttyp".

* `ruleAt_instrConst`, `ruleAt_exprConst`, `ruleAt_exprOk`, `ruleAt_exprOkConst`,
  `ruleAt_datamodeActive`: the rules of constant expressions and of active data, located by `rfl`.
* `dd_instrConstInt`, `dd_exprConst`, `dd_exprOk`, `dd_exprOkConst`, `dd_exprOkConstInt`:
  `Expr_ok_const(C, [CONST nt c], nt)` in every typed context, under every reading of `otherwise`.
* `dd_datamodeActive`, `dd_dataOkOf`, `dd_dataOkA`, `typedV_dataVA`: `Datamode_ok/active` and
  `Data_ok` at the image of every passive or constant-active data segment (`DataShape`).
* `quantsOk_modV`, `evalExp_modConclV`, `dprem7_V`, `dprems_modV`: `Module_ok`'s scope and
  premises at memories and arbitrary data images; `moduleOk_mdv`: `Module_ok` at any typed images
  with `Data_ok` facts; `moduleOk_mda`: at `DataShape` segments; `moduleOk_mdv_inv`: reflection of
  the memories and of `v` at any images; `moduleOk_mda_iff`: exact at `withClosMod B`.
* `dataOk_of_shape`, `mdaModule_ok_iff`: Core's side; `mdaModule_sat_iff`: **the satisfaction
  condition is exact** on modules of memories and passive or constant-active data, at
  `stepModel (withClosMod BI)`; `mdvModuleV_passive`: agreement with an earlier image;
  `activeModule_ok`: non-vacuity.
* `not_evalExp_mutOpt`, `not_dd_globalOk`, `globalsOk_nil`, `not_moduleOk_global`: `Global_ok`'s
  premise `globaltype = %%(MUT?, t)` has an option iteration without a domain, which never
  evaluates; so `Global_ok` has no facts, `Globals_ok` holds only at `[]`, and no module with a
  global is a `Module_ok` fact, in every `simEnv B`. `globalModule_ok`, `globalModule_not_sat`:
  Core validates `(module (global i32 (i32.const 0)))`, so **the satisfaction condition fails at
  modules with globals**.
* `nullOptStuck`, `not_dpremB_stuck`, `brnnCheck`, `instrOk_brnnCheck`, `not_dd_brOnNonNull`:
  the same defect in `Instr_ok/br_on_non_null` (`NULL?`): no `Instr_ok` fact has the instruction
  `BR_ON_NON_NULL l`; `brOnNonNull_not_sat`: Core types `br_on_non_null 0` under a label
  `[ref n ht]`, so the instruction-typing satisfaction condition fails there.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30V.dd_exprOkConstInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30V.dd_exprOkConstInt

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30V.dd_dataOkA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30V.dd_dataOkA

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30V.moduleOk_mdv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30V.moduleOk_mdv

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30V.moduleOk_mda_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30V.moduleOk_mda_iff

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30V.mdaModule_sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30V.mdaModule_sat_iff

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30V.activeModule_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30V.activeModule_ok

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30V.not_dd_globalOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30V.not_dd_globalOk

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30V.globalModule_not_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30V.globalModule_not_sat

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30V.brOnNonNull_not_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30V.brOnNonNull_not_sat
