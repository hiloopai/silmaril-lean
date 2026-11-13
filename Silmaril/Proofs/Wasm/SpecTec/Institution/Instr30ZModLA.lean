module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZModL

/-!
# Module typing of the wasm-3.0 script, `Module_ok`'s other premises at any list of memories

The seventeen premises of `Module_ok` that do not mention `mem*`, `mt*` or `C` in a non-trivial
way, read in the scope `modσL mts` (copies of `Instr30ZModA`/`Instr30ZModB` with the scope changed;
the symbolic lists are only passed over by the variable lookups).
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

/-- The scope `modσL` reads list variables as given. -/
theorem evalDoms_modL {mts : List Silmaril.Wasm.MemoryType} {ds : List Dom}
    {xvs : List (IL.Id × Value)}
    (h : evalDoms 5 (simEnv B) (ρL mts) ds = .ok xvs) : EvalDoms (simEnv B) (ρL mts) ds xvs := ⟨5, h⟩

/-- `Module_ok`'s premise 0, `Types_ok`, holds at `memModuleV mts`. -/
theorem dprem0_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem0 :=
  .rulePr (evalArgs_nil _ _) ⟨20, by
    simp [Round6.RefOkV.ctxEmptyV, evalExp, evalExps, evalExpFields, evalIterE, evalDoms, domSrc,
      domVar, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL, Map.binds, Map.bind, Map.find?, evalIterList,
      evalRounds, Value.asList?, iterRows, Functor.map, Except.map, Bind.bind, Except.bind,
      Res.ofOption, Pure.pure, Except.pure]⟩ (dd_typesEmpty O)

/-- `Module_ok`'s premise 3, `Globals_ok`, holds at `memModuleV mts`. -/
theorem dprem3_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem3 :=
  .rulePr (evalArgs_nil _ _) ⟨20, by
    simp [evalExp, evalExps, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals,
      ρL, modσL, Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure]⟩ (dd_globalsEmpty O)

/-- `Module_ok`'s premise 1, an iteration over empty lists, holds at `memModuleV mts`. -/
theorem dprem1_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem1 :=
  dpremB_iterNil (xvs := [("import", .list []), ("xt_I", .list [])]) (evalDoms_modL (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 2, an iteration over empty lists, holds at `memModuleV mts`. -/
theorem dprem2_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem2 :=
  dpremB_iterNil (xvs := [("jt", .list []), ("tag", .list [])]) (evalDoms_modL (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 5, an iteration over empty lists, holds at `memModuleV mts`. -/
theorem dprem5_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem5 :=
  dpremB_iterNil (xvs := [("table", .list []), ("tt", .list [])]) (evalDoms_modL (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 6, an iteration over empty lists, holds at `memModuleV mts`. -/
theorem dprem6_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem6 :=
  dpremB_iterNil (xvs := [("dt", .list []), ("func", .list [])]) (evalDoms_modL (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 7, an iteration over empty lists, holds at `memModuleV mts`. -/
theorem dprem7_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem7 :=
  dpremB_iterNil (xvs := [("data", .list []), ("ok", .list [])]) (evalDoms_modL (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 8, an iteration over empty lists, holds at `memModuleV mts`. -/
theorem dprem8_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem8 :=
  dpremB_iterNil (xvs := [("elem", .list []), ("rt", .list [])]) (evalDoms_modL (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 10, an iteration over empty lists, holds at `memModuleV mts`. -/
theorem dprem10_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem10 :=
  dpremB_iterNil (xvs := [("export", .list []), ("nm", .list []), ("xt_E", .list [])]) (evalDoms_modL (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 9, `Start_ok` over the absent start function, holds vacuously. -/
theorem dprem9_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem9 :=
  .iterOptNone (xvs := [("start", .opt none)]) (evalDoms_modL (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

variable {B : Builtins}

/-- `Module_ok`'s premise 11 holds at `memModuleV mts`. -/
theorem dprem11_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem11 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d13, fd_disj,
      evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL, Map.binds,
      Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows, Functor.map,
      Except.map, matchTypV, resolveTyp, VarEnv.findTyp?, VarEnv.bindTyp, memTyp_X,
      Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 13 holds at `memModuleV mts`. -/
theorem dprem13_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem13 :=
  .ifPr ⟨60, by
    simp [evalExp, evalExps, VarEnv.empty, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, evalExpFields, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 15 holds at `memModuleV mts`. -/
theorem dprem15_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem15 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d161,
      fd_tagsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 16 holds at `memModuleV mts`. -/
theorem dprem16_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem16 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d162,
      fd_globalsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 17 holds at `memModuleV mts`. -/
theorem dprem17_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem17 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d163,
      fd_memsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 18 holds at `memModuleV mts`. -/
theorem dprem18_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem18 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d164,
      fd_tablesxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 19 holds at `memModuleV mts`. -/
theorem dprem19_L (mts : List Silmaril.Wasm.MemoryType) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρL mts) modPrem19 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d165,
      fd_funcsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, ρL, modσL,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30Z
