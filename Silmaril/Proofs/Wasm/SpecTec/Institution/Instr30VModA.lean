module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30VMod

/-!
# Module typing of the wasm-3.0 script, ws5 `Module_ok`'s other premises at memories and data images

The sixteen premises of `Module_ok` that do not mention `mem*`, `mt*`, `data*`, `ok*` or `C` in a
non-trivial way, read in the scope `modσV mts dvs` of arbitrary data images `dvs` (copies of
`Instr30WModDA` with the scope changed; the symbolic lists are only passed over by the variable
lookups).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30V

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

/-- The scope `modσV` reads list variables as given. -/
theorem evalDoms_modV {mts : List Silmaril.Wasm.MemoryType} {dd : List Value} {ds : List Dom}
    {xvs : List (IL.Id × Value)}
    (h : evalDoms 5 (simEnv B) (ρV mts dd) ds = .ok xvs) : EvalDoms (simEnv B) (ρV mts dd) ds xvs := ⟨5, h⟩

/-- `Module_ok`'s premise 0, `Types_ok`, holds at `mdvModuleV mts dvs`. -/
theorem dprem0_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem0 :=
  .rulePr (evalArgs_nil _ _) ⟨20, by
    simp [Round6.RefOkV.ctxEmptyV, evalExp, evalExps, evalExpFields, evalIterE, evalDoms, domSrc,
      domVar, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV, Map.binds, Map.bind, Map.find?, evalIterList,
      evalRounds, Value.asList?, iterRows, Functor.map, Except.map, Bind.bind, Except.bind,
      Res.ofOption, Pure.pure, Except.pure]⟩ (dd_typesEmpty O)

/-- `Module_ok`'s premise 3, `Globals_ok`, holds at `mdvModuleV mts dvs`. -/
theorem dprem3_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem3 :=
  .rulePr (evalArgs_nil _ _) ⟨20, by
    simp [evalExp, evalExps, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals,
      ρV, modσV, Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure]⟩ (dd_globalsEmpty O)

/-- `Module_ok`'s premise 1, an iteration over empty lists, holds at `mdvModuleV mts dvs`. -/
theorem dprem1_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem1 :=
  dpremB_iterNil (xvs := [("import", .list []), ("xt_I", .list [])]) (evalDoms_modV (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 2, an iteration over empty lists, holds at `mdvModuleV mts dvs`. -/
theorem dprem2_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem2 :=
  dpremB_iterNil (xvs := [("jt", .list []), ("tag", .list [])]) (evalDoms_modV (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 5, an iteration over empty lists, holds at `mdvModuleV mts dvs`. -/
theorem dprem5_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem5 :=
  dpremB_iterNil (xvs := [("table", .list []), ("tt", .list [])]) (evalDoms_modV (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 6, an iteration over empty lists, holds at `mdvModuleV mts dvs`. -/
theorem dprem6_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem6 :=
  dpremB_iterNil (xvs := [("dt", .list []), ("func", .list [])]) (evalDoms_modV (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 8, an iteration over empty lists, holds at `mdvModuleV mts dvs`. -/
theorem dprem8_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem8 :=
  dpremB_iterNil (xvs := [("elem", .list []), ("rt", .list [])]) (evalDoms_modV (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 10, an iteration over empty lists, holds at `mdvModuleV mts dvs`. -/
theorem dprem10_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem10 :=
  dpremB_iterNil (xvs := [("export", .list []), ("nm", .list []), ("xt_E", .list [])]) (evalDoms_modV (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 9, `Start_ok` over the absent start function, holds vacuously. -/
theorem dprem9_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem9 :=
  .iterOptNone (xvs := [("start", .opt none)]) (evalDoms_modV (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

variable {B : Builtins}

/-- `Module_ok`'s premise 11 holds at `mdvModuleV mts dvs`. -/
theorem dprem11_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem11 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d13, fd_disj,
      evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV, Map.binds,
      Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows, Functor.map,
      Except.map, matchTypV, resolveTyp, VarEnv.findTyp?, VarEnv.bindTyp, memTyp_X,
      Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 13 holds at `mdvModuleV mts dvs`. -/
theorem dprem13_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem13 :=
  .ifPr ⟨60, by
    simp [evalExp, evalExps, VarEnv.empty, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, evalExpFields, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 15 holds at `mdvModuleV mts dvs`. -/
theorem dprem15_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem15 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d161,
      fd_tagsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 16 holds at `mdvModuleV mts dvs`. -/
theorem dprem16_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem16 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d162,
      fd_globalsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 17 holds at `mdvModuleV mts dvs`. -/
theorem dprem17_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem17 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d163,
      fd_memsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 18 holds at `mdvModuleV mts dvs`. -/
theorem dprem18_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem18 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d164,
      fd_tablesxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 19 holds at `mdvModuleV mts dvs`. -/
theorem dprem19_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem19 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d165,
      fd_funcsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30V
