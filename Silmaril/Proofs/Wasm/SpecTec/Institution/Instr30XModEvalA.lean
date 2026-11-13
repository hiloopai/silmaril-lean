module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XModFns

/-!
# Instruction typing of the wasm-3.0 script, extended: `Module_ok`'s side conditions (A)

`if` premises of `Module_ok` that hold in the scope `modσ`, in every evaluator `simEnv B`, by
evaluating them clause by clause (`simp` over the evaluator's equations and the clauses of
`Instr30XModFns`): `$disjoint_(name, [])` is `true` (its first clause, with `X` a pattern
variable), and
`C = C' ⊕ {TAGS [] ++ [], …}`, `C' = {TYPES [], …}` hold at `C = C' = {}`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d13)

variable {B : Builtins}

/-- The record `C' ⊕ {…}` composes to `{}`. -/
theorem comp_ctxEmpty : Value.comp? Round6.RefOkV.ctxEmptyV Round6.RefOkV.ctxEmptyV =
    some Round6.RefOkV.ctxEmptyV := rfl

/-- `Module_ok`'s premise 11 holds at the empty module. -/
theorem dprem11 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem11 :=
  .ifPr ⟨60, by
    simp [evalExp, callDef, evalArgs, evalArg, tryClauses, matchArg, matchExp, premsHold,
      VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig, Original.d13, fd_disj,
      evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, modσ, Map.binds,
      Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows, Functor.map,
      Except.map, matchTypV, resolveTyp, VarEnv.findTyp?, VarEnv.bindTyp, memTyp_X,
      Round6.RefOkV.ctxEmptyV]⟩

/-- `Module_ok`'s premise 12, `C = C' ⊕ {…}`, holds at the empty module. -/
theorem dprem12 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem12 :=
  .ifPr (evalExp_cmpE_iff.2 ⟨_, _, Sim.evalExp_var rfl, evalExp_compE_iff.2 ⟨_, _,
    Sim.evalExp_var rfl, evalExp_strE_iff.2 ⟨_, ⟨20, by
      simp [evalExp, evalExpFields, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?,
        VarEnv.bindVals, modσ, Map.binds, Map.bind, Map.find?, evalIterList, evalRounds,
        Value.asList?, iterRows, Functor.map, Except.map, Bind.bind, Except.bind, Res.ofOption,
        Pure.pure, Except.pure, Round6.RefOkV.ctxEmptyV, evalExps]⟩, rfl⟩,
    comp_ctxEmpty⟩, Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩)

/-- `Module_ok`'s premise 13 holds at the empty module. -/
theorem dprem13 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem13 :=
  .ifPr ⟨60, by
    simp [evalExp, evalExps, VarEnv.empty, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals, modσ,
      Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, cmpValues, evalExpFields, Round6.RefOkV.ctxEmptyV]⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30X
