module

public import Silmaril.Wasm.SpecTec.Institution.Instr30Z.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZModOk
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZModLOk
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZCvt
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZSubEx
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZMemInv

/-!
# Module typing of the wasm-3.0 script, results

Namespace `Silmaril.Wasm.SpecTec.Institution.Instr30Z`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.{Instr30ZMem,Instr30ZFree,Instr30ZMod,Instr30ZModA,Instr30ZModB,Instr30ZModOk,Instr30ZFreeL,Instr30ZModL,Instr30ZModLA,Instr30ZModLOk,Instr30ZCvt,Instr30ZSub,
Instr30ZSubEx,Instr30ZMemInv}`;
see `docs/projects/wasm-components.md`, "Stretch, insttyp (ws4 an earlier step)".

* `ruleAt_limitsOk`, `ruleAt_memtypeOk`, `ruleAt_memOk`, `dd_limitsOk`, `evalExp_memBound`,
  `dd_memtypeOk`, `dd_memOk`: `Limits_ok`, `Memtype_ok` and `Mem_ok` fire at every memory type
  Core validates, in every typed context; the bound `2 ^ ($size(at) - 16)` is evaluated through
  the script's `$size`.
* `dd_oneRule_inv`, `limitsOk_inv`, `memtypeOk_inv`, `memOk_inv`, `memOk_iff`: inversion of the
  three one-rule relations; `Mem_ok(C, MEMORY mt, v)` holds exactly when `v = mt` and Core
  validates `mt`, in every typed context and evaluator, under every reading of `otherwise`.
* `tc_fmem`, `tc_flistRep`, `fm_body1`, `tc_freeModule1`, `tc_funcidxNonfuncs1`: `$free_mem`,
  `$free_list` of copies of the empty record, `$free_module` and `$funcidx_nonfuncs` at a module
  with one memory, by per-shape matching lemmas and evaluation steps rather than one `simp`.
* `quantsOk_mod1`, `evalExp_modConcl1`, `dprem4_1`, `dprem12_1`, `dprem14_1`, `dprems_mod1`: the
  twenty premises of `Module_ok` in the scope `modσ1 mt`.
* `moduleOk_mem`, `moduleOk_mem_withClosMod`, `moduleOk_mem_repaired`: `stepModel (withClosMod B)`
  validates `memModuleV [mt]` at `[] -> []` whenever Core validates `mt`; `not_moduleOk_mem`:
  `stepModel BI` validates no module with memories.
* `memModule_ok_iff`, `memModule_sat`: Core validates `memModule mts` exactly when each memory type
  is valid, at `[] -> []`; every Core typing of a one-memory module is a `Module_ok` fact.
* `tc_funcidxNonfuncsL`, `quantsOk_modL`, `evalExp_modConclL`, `dprem4_L`, `dprem12_L`,
  `dprem14_L`, `moduleOk_memL`, `moduleOk_memL_repaired`, `memModule_satL`: the same at every list
  of memories (symbolic lists, evaluated by per-shape lemmas); every Core typing of a memory-only
  module is a `Module_ok` fact of `stepModel (withClosMod BI)`.
* `ruleAt_cvtop`, `hasTyp_cvtopRule`, `dd_convert`, `convert_preserves`, `numericAll_preserves`:
  `Instr_ok/cvtop` fires at Core's typing of every conversion (the operator sort
  `cvtop__(nt_2, nt_1)` is moved across the rule's renaming 's typing), so every Core
  typing of a numeric instruction is an `Instr_ok` fact in every typed context.
* `subB_results`, `resulttypeSub_of`, `dd_subZ`: `Instrs_ok/sub` in `{}` at every bounded valid
  Core subsumption without locals, at any value types (round 6's canonical subtyping derivations
  read Core's `ResultSub {}`). `fragOkZ_dd`, `fragOkZ_sound`: `FragOkZ` (`FragOkX` with `sub`)
  derivations are `Instrs_ok {}` facts and Core derivations; `unreachableDefSub`: non-vacuity at
  the non-flat `ref dFn <: ref null func`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Z.dd_memOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Z.dd_memOk

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Z.tc_funcidxNonfuncs1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Z.tc_funcidxNonfuncs1

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Z.moduleOk_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Z.moduleOk_mem

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Z.moduleOk_mem_repaired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Z.moduleOk_mem_repaired

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Z.memModule_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Z.memModule_ok_iff

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Z.memModule_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Z.memModule_sat

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Z.numericAll_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Z.numericAll_preserves

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Z.fragOkZ_dd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Z.fragOkZ_dd

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Z.unreachableDefSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Z.unreachableDefSub

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Z.memModule_satL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Z.memModule_satL

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Z.memOk_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Z.memOk_iff
