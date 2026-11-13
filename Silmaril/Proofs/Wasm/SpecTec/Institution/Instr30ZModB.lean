module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZMod

/-!
# Module typing of the wasm-3.0 script, `Module_ok`'s premises at one memory (B)

The side conditions of `Module_ok`, read in the scope `modσ1 mt`. Those that do not mention
`mem*`, `mt*` or `C` are copies of `Instr30XModEvalA`/`B`/`C` with the scope changed. The two
that do:

* premise 12, `C = C' ⊕ {…, MEMS mt_I* ++ mt*, …}`, holds at `C = {MEMS [mt]}`, `C' = {}`
  (`dprem12_1`);
* premise 14, `x* = $funcidx_nonfuncs(global*, mem*, table*, elem*, export*)`, holds at `x* = []`
  through `Instr30ZFree.tc_funcidxNonfuncs1` (`dprem14_1`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Z

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (callDef_iff applies_iff_callDef)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Institution.Instr30X (modPrem0 modPrem1 modPrem2
  modPrem3 modPrem4 modPrem5 modPrem6 modPrem7 modPrem8 modPrem9 modPrem10 modPrem11 modPrem12
  modPrem13 modPrem14 modPrem15 modPrem16 modPrem17 modPrem18 modPrem19 dpremB_iterNil
  dd_typesEmpty dd_globalsEmpty defClauses defSig memTyp_X fd_disj fd_tagsxt fd_globalsxt fd_memsxt
  fd_tablesxt fd_funcsxt fd_fnf)
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d13 Original.d161 Original.d162 Original.d163
  Original.d164 Original.d165)

variable {B : Builtins}

/-- `Module_ok`'s premise 11 holds at `memModuleV [mt]`. -/
theorem dprem11_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem11 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d13, fd_disj,
      evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1, Map.binds,
      Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows, Functor.map,
      Except.map, matchTypV, resolveTyp, VarEnv.findTyp?, VarEnv.bindTyp, memTyp_X,
      Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 13 holds at `memModuleV [mt]`. -/
theorem dprem13_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem13 :=
  .ifPr ⟨60, by
    simp [evalExp, evalExps, VarEnv.empty, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, evalExpFields, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 15 holds at `memModuleV [mt]`. -/
theorem dprem15_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem15 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d161,
      fd_tagsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 16 holds at `memModuleV [mt]`. -/
theorem dprem16_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem16 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d162,
      fd_globalsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 17 holds at `memModuleV [mt]`. -/
theorem dprem17_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem17 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d163,
      fd_memsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 18 holds at `memModuleV [mt]`. -/
theorem dprem18_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem18 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d164,
      fd_tablesxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 19 holds at `memModuleV [mt]`. -/
theorem dprem19_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem19 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d165,
      fd_funcsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- **`Module_ok`'s premise 12, `C = C' ⊕ {…}`, holds at `memModuleV [mt]`**: `C = {MEMS [mt]}`,
`C' = {}`. -/
theorem dprem12_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem12 :=
  .ifPr (evalExp_cmpE_iff.2 ⟨_, _, Sim.evalExp_var rfl, evalExp_compE_iff.2 ⟨_, _,
    Sim.evalExp_var rfl, evalExp_strE_iff.2 ⟨_, ⟨20, by
      simp [evalExp, evalExpFields, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?,
        VarEnv.bindVals, ρ1, modσ1, Map.binds, Map.bind, Map.find?, evalIterList, evalRounds,
        Value.asList?, iterRows, iterRow, Functor.map, Except.map, Bind.bind, Except.bind,
        Res.ofOption, Pure.pure, Except.pure, Round6.RefOkV.ctxEmptyV, evalExps]
      exact rfl⟩, rfl⟩, rfl⟩, Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩)

/-- **`Module_ok`'s premise 14, `x* = $funcidx_nonfuncs(…)`, holds at `memModuleV [mt]`.** -/
theorem dprem14_1 (mt : Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρ1 mt) modPrem14 :=
  .ifPr (evalExp_cmpE_iff.2 ⟨_, _, ⟨10, by
      simp [evalExp, evalIterE, evalIterList, evalRounds, iterRows, Value.asList?, evalDoms,
        domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρ1, modσ1, Map.binds, Map.bind,
        Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure]⟩,
    evalExp_callE_iff.2 ((applies_iff_callDef (Memory.findDef_bindVals_empty _ _) ⟨10, by
      simp [evalArgs, evalArg, evalExps, evalIterE, evalIterList, evalRounds, iterRows, iterRow,
        Value.asList?, Functor.map, Except.map, evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?,
        VarEnv.bindVals, modσ1, Map.binds, Map.bind, Map.find?, Bind.bind, Except.bind,
        Res.ofOption, Pure.pure, Except.pure]⟩).1
        ⟨_, _, _, fd_fnf, .inl (tc_funcidxNonfuncs1 mt)⟩),
    Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩)

end Silmaril.Wasm.SpecTec.Institution.Instr30Z
