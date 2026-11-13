module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XModFns

/-!
# Instruction typing of the wasm-3.0 script, extended: `Module_ok`'s side conditions (B)

`if` premises of `Module_ok` that hold in the scope `modσ`, in every evaluator `simEnv B`, by
evaluating them clause by clause (`simp` over the evaluator's equations and the clauses of
`Instr30XModFns`): `[] = $tagsxt([])`, `[] = $globalsxt([])` and `[] = $memsxt([])`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d161 Original.d162 Original.d163)

variable {B : Builtins}

/-- `Module_ok`'s premise 15 holds at the empty module. -/
theorem dprem15 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem15 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d161,
      fd_tagsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, modσ,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 16 holds at the empty module. -/
theorem dprem16 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem16 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d162,
      fd_globalsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, modσ,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 17 holds at the empty module. -/
theorem dprem17 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem17 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d163,
      fd_memsxt, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, modσ,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, Round6.RefOkV.ctxEmptyV]⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30X
