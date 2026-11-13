module

public import Silmaril.Wasm.SpecTec.Institution.Instr30W.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30WRefl
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30WModDOk
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30WSubEx

/-!
# Module typing of the wasm-3.0 script, results

Namespace `Silmaril.Wasm.SpecTec.Institution.Instr30W`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30W*`; see `docs/projects/spectec/README.md`,
"insttyp".

* `evalDoms_forall₂`, `iterLen_of_dom`, `star_inv`, `pctStar_inv`, `modConcl_inv`: generic
  inversions of iteration domains and of `Module_ok`'s conclusion (`import*`, `mem*`, `export*`
  and the arguments of `$clos_moduletype` read back); `iterNil_two`, `iterNil_three`: a domain of
  an iterated premise is empty when another one is; `prem4_inv`: premise 4 (`Mem_ok` over
  `mem* = MEMORY mt*`) gives `mt.Valid` for every `mt`.
* `moduleOk_memL_inv`: **reflection of `Module_ok` at memory-only modules**, in every evaluator
  `simEnv B` and under every reading of `otherwise`; `moduleOk_memL_iff`: at `withClosMod B`,
  `Module_ok(memModuleV mts, v)` holds exactly when `v = [] -> []` and every `mt` is valid;
  `memModule_sat_iff`: the satisfaction condition at `stepModel (withClosMod BI)` is exact on
  memory-only modules.
* `ruleAt_datamodePassive`, `ruleAt_dataOk`, `dd_datamodePassive`, `dd_dataOk`: `Datamode_ok/passive`
  and `Data_ok` fire at `DATA(b*, PASSIVE)` in every typed context; `typedV_dataV`, `typedV_okV`,
  `ctxT_ctxMD`: the values of a data module are typed.
* `quantsOk_modD`, `evalExp_modConclD`, `dprem4_D`, `dprem7_D`, `dprem12_D`, `dprem14_D`,
  `dprem*_D`, `dprems_modD`: `Module_ok`'s twenty premises in the scope `modσD mts ds` of a module of
  memories and data segments.
* `moduleOk_md`: `Module_ok` validates `mdModuleV mts ds` when every `mt` is Core-valid;
  `moduleOk_md_inv`, `moduleOk_md_iff`: the converse, exact at `withClosMod B`;
  `mdModule_ok_iff`: Core's side, for passive data; `mdModule_sat_iff`: the satisfaction condition
  at `stepModel (withClosMod BI)` is exact on modules of memories and passive data segments;
  `dataModule_ok`: non-vacuity at a module with one passive data segment.
* `ctxRX`, `typedV_ctxRX`, `dd_typeuseOkRecX`, `dd_recKindX`, `dd_recSubX`, `applies_unrollht_recX`,
  `applies_unrollht_dtX`, `dd_deftypeOkX`: round 6's rule lemmas that read `RECS`, restated at
  `{LOCALS ls, GLOBALS gs, RECS l}`; `okDX_of`, `subOk2DX_of`, `groupDX_of`, `subDX_of`: round 6's
  canonical validity and subtyping derivations read by `DDerivesB` at `ctxOfX ls gs Δ`.
* `valtypeOkLG_of`, `resulttypeOkLG_of`, `instrtypeOkLG_of`, `resulttypeSubLG_of`: bounded valid
  Core types and subtypings are `Valtype_ok`, `Resulttype_ok`, `Instrtype_ok`, `Resulttype_sub`
  facts in `ctxLGV L G`; `dd_frameW`, `dd_subW`: `Instrs_ok/frame` and `Instrs_ok/sub` there at any
  bounded valid types; `fragOkW_sound`, `fragOkW_dd`: `FragOkW` derivations are Core derivations
  and `Instrs_ok` facts; `unreachableBotDef`, `nopFrameDef`: non-vacuity at `ref dFn` in
  `{locals := [i32], globals := [mut f64]}`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30W.moduleOk_memL_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30W.moduleOk_memL_inv

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30W.moduleOk_memL_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30W.moduleOk_memL_iff

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30W.memModule_sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30W.memModule_sat_iff

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30W.dd_dataOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30W.dd_dataOk

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30W.moduleOk_md' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30W.moduleOk_md

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30W.moduleOk_md_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30W.moduleOk_md_iff

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30W.mdModule_sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30W.mdModule_sat_iff

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30W.dataModule_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30W.dataModule_ok

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30W.okDX_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30W.okDX_of

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30W.subDX_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30W.subDX_of

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30W.fragOkW_dd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30W.fragOkW_dd

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30W.unreachableBotDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30W.unreachableBotDef

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30W.nopFrameDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30W.nopFrameDef
