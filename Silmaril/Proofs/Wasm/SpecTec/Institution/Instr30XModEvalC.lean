module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XModFns

/-!
# Instruction typing of the wasm-3.0 script, extended: `Module_ok`'s side conditions (C)

`if` premises of `Module_ok` that hold in the scope `modσ`, in every evaluator `simEnv B`, by
evaluating them clause by clause (`simp` over the evaluator's equations and the clauses of
`Instr30XModFns`): `[] = $tablesxt([])` and `[] = $funcsxt([])`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d164 Original.d165)

variable {B : Builtins}

/-- `Module_ok`'s premise 18 holds at the empty module. -/
theorem dprem18 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem18 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d164,
      fd_tablesxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, modσ,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 19 holds at the empty module. -/
theorem dprem19 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem19 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d165,
      fd_funcsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, modσ,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30X
