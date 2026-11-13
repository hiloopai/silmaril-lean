module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XModule
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XModEvalA
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XModEvalB
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XModEvalC
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XFuncidx

/-!
# Instruction typing of the wasm-3.0 script, extended: `Module_ok` at the empty module, repaired

`Instr30XModule` shows that `Module_ok` has no facts on the concrete primitives, because
`$clos_moduletype` never has a value. This module shows that this is the only obstacle at the empty
module: in every evaluator `simEnv B` whose primitives answer `$clos_moduletype({}, [] -> [])`
with some `mt`, `Module_ok` derives `(emptyModuleV, mt)` (`moduleOk_empty`, given `FuncidxEmpty`,
which holds in every evaluator by `Instr30XFuncidx.funcidxEmpty`), under every reading of
`otherwise`. `emptyModuleOk_repaired`: so `Instr30.Task.emptyModuleOk` holds once the concrete
primitives are extended by `withClosMod`.

The rule is read in the scope `modσ` (`quantsOk_mod`: well typed), its conclusion evaluates to
`(emptyModuleV, mt)` (`evalExp_modConcl`), and its twenty premises hold: `Types_ok` and
`Globals_ok` by their `empty` rules, the nine iterations over empty lists and the absent start
function vacuously, and the nine side conditions by `Instr30XModEvalA`/`B`/`C` and `FuncidxEmpty`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (callDef_iff applies_iff_callDef)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Institution.Instr30 (ctxT_empty evalExp_nil emptyModuleV)

variable {B : Builtins}

/-! ## The scope and the conclusion -/

/-- **`modσ` is a well-typed assignment of `Module_ok`'s quantifiers.** -/
theorem quantsOk_mod : QuantsOk (simEnv B) (VarEnv.empty.bindVals modσ) modParams :=
  have hl {t : Typ} : HasTyp (simEnv B) (VarEnv.empty.bindVals modσ) (.iterT t .list) (.list []) :=
    Round5.RefOk.typedV_listNil _ (valsOnly_bind _)
  have hc : HasTyp (simEnv B) (VarEnv.empty.bindVals modσ) (.varT "context" [])
      Round6.RefOkV.ctxEmptyV := ctxT_empty _ (valsOnly_bind _)
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl (hasTyp_iterT_opt_iff.2 (.inl rfl)) <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hc <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hc <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl QuantsOk.nil

/-- The module part of the conclusion evaluates to `emptyModuleV`. -/
theorem evalExp_modModule :
    EvalExp (simEnv B) (VarEnv.empty.bindVals modσ)
      (match modConcl with | .tupE (e :: _) => e | e => e) emptyModuleV :=
  ⟨10, by
    simp [modConcl, emptyModuleV, Instr30.pctNil, evalExp, evalExps, evalIterE, evalDoms, domSrc,
      domVar, VarEnv.findVal?, VarEnv.bindVals, modσ, Map.binds, Map.bind, Map.find?, evalIterList,
      evalRounds, Value.asList?, Value.asOpt?, iterRows, Functor.map, Except.map, Bind.bind,
      Except.bind, Res.ofOption, Pure.pure, Except.pure]⟩

/-- The arguments of `$clos_moduletype` in the conclusion evaluate to `({}, [] -> [])`. -/
theorem evalArgs_closMod :
    EvalArgs (simEnv B) (VarEnv.empty.bindVals modσ)
      [.expA (.varE "C"), .expA (.caseE "%->%" (.tupE [
        .iterE (.varE "xt_I") (.mk .list [.mk "xt_I" (.varE "xt_I*")]),
        .iterE (.varE "xt_E") (.mk .list [.mk "xt_E" (.varE "xt_E*")])]))]
      [.val Round6.RefOkV.ctxEmptyV, .val mtNil] :=
  ⟨10, by
    simp [mtNil, evalArgs, evalArg, evalExp, evalExps, evalIterE, evalDoms, domSrc, domVar,
      VarEnv.findVal?, VarEnv.bindVals, modσ, Map.binds, Map.bind, Map.find?, evalIterList,
      evalRounds, Value.asList?, iterRows, Functor.map, Except.map, Bind.bind, Except.bind,
      Res.ofOption, Pure.pure, Except.pure]⟩

/-- **The conclusion evaluates to `(emptyModuleV, mt)`** when the primitives answer
`$clos_moduletype({}, [] -> [])` with `mt`. -/
theorem evalExp_modConcl {mt : Value}
    (hB : B.call "clos_moduletype" [.val Round6.RefOkV.ctxEmptyV, .val mtNil] = some mt) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals modσ) modConcl (.tuple [emptyModuleV, mt]) := by
  obtain ⟨ps, t, hd⟩ := findDef_closMod (B := B)
  have hcall : CallDef (simEnv B) (VarEnv.empty.bindVals modσ) "clos_moduletype"
      [.expA (.varE "C"), .expA (.caseE "%->%" (.tupE [
        .iterE (.varE "xt_I") (.mk .list [.mk "xt_I" (.varE "xt_I*")]),
        .iterE (.varE "xt_E") (.mk .list [.mk "xt_E" (.varE "xt_E*")])]))] mt := by
    refine callDef_iff.2 ⟨_, ps, t, closModClauses, evalArgs_closMod, ?_, .inr ⟨?_, ?_⟩⟩
    · rw [Memory.findDef_bindVals_empty, Option.getD_none]
      exact hd
    · exact tryClausesUndef_closMod _ _
    · rw [Memory.findDef_bindVals_empty, Option.getD_none, simEnv, Env.builtins_withBuiltins]
      exact hB
  exact evalExp_tup2 evalExp_modModule (evalExp_callE_iff.2 hcall)

/-! ## The premises -/

/-- `Types_ok/empty` in `{}`. -/
theorem dd_typesEmpty (O : ElseI) :
    DDerivesB (simEnv B) O "Types_ok" "%|-%:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, .list [], .list []]) :=
  dderivesB_of_ruleAt ruleAt_typesEmpty (self_mem_conclAlts _) [("C", Round6.RefOkV.ctxEmptyV)]
    (QuantsOk.cons rfl (ctxT_empty _ (valsOnly_bind _)) QuantsOk.nil)
    (evalExp_tup3 (Sim.evalExp_var rfl) evalExp_nil evalExp_nil) premsB_nil

/-- `Globals_ok/empty` in `{}`. -/
theorem dd_globalsEmpty (O : ElseI) :
    DDerivesB (simEnv B) O "Globals_ok" "%|-%:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, .list [], .list []]) :=
  dderivesB_of_ruleAt ruleAt_globalsEmpty (self_mem_conclAlts _) [("C", Round6.RefOkV.ctxEmptyV)]
    (QuantsOk.cons rfl (ctxT_empty _ (valsOnly_bind _)) QuantsOk.nil)
    (evalExp_tup3 (Sim.evalExp_var rfl) evalExp_nil evalExp_nil) premsB_nil

/-- Domains that are all empty lists, read as lists. -/
theorem domLists_nil {xvs : List (IL.Id × Value)} (h : ∀ p ∈ xvs, p.2 = .list []) :
    domLists xvs = some (xvs.map fun p => (p.1, [])) := by
  induction xvs with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨x, v⟩ := p
    obtain rfl : v = .list [] := h _ List.mem_cons_self
    have ht := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [domLists, List.mapM_cons, Value.asList?, Option.map_some] at ht ⊢
    simp [ht]

/-- **An iteration over empty lists holds vacuously.** -/
theorem dpremB_iterNil {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem}
    {ds : List Dom} {xvs : List (IL.Id × Value)} (hd : EvalDoms env ρ ds xvs) (hne : ds ≠ [])
    (hall : ∀ p ∈ xvs, p.2 = .list []) : DPremB env O els ρ (.iterPr pr (.mk .list ds)) :=
  .iterList (k := 0) (.inl rfl) hd hne (domLists_nil hall) (by simp)
    (by simp [iterRows])

/-- The scope `modσ` reads list variables as empty. -/
theorem evalDoms_mod {ds : List Dom} {xvs : List (IL.Id × Value)}
    (h : evalDoms 5 (simEnv B) (VarEnv.empty.bindVals modσ) ds = .ok xvs) :
    EvalDoms (simEnv B) (VarEnv.empty.bindVals modσ) ds xvs := ⟨5, h⟩

/-! ## The twenty premises -/

/-- `Module_ok`'s premise 0, `Types_ok`, holds at the empty module. -/
theorem dprem0 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem0 :=
  .rulePr (evalArgs_nil _ _) ⟨20, by
    simp [Round6.RefOkV.ctxEmptyV, evalExp, evalExps, evalExpFields, evalIterE, evalDoms, domSrc,
      domVar, VarEnv.findVal?, VarEnv.bindVals, modσ, Map.binds, Map.bind, Map.find?, evalIterList,
      evalRounds, Value.asList?, iterRows, Functor.map, Except.map, Bind.bind, Except.bind,
      Res.ofOption, Pure.pure, Except.pure]⟩ (dd_typesEmpty O)

/-- `Module_ok`'s premise 3, `Globals_ok`, holds at the empty module. -/
theorem dprem3 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem3 :=
  .rulePr (evalArgs_nil _ _) ⟨20, by
    simp [evalExp, evalExps, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVals,
      modσ, Map.binds, Map.bind, Map.find?, evalIterList, evalRounds, Value.asList?, iterRows,
      Functor.map, Except.map, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure]⟩ (dd_globalsEmpty O)

/-- `Module_ok`'s premise 1, an iteration over empty lists, holds at the empty module. -/
theorem dprem1 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem1 :=
  dpremB_iterNil (xvs := [("import", .list []), ("xt_I", .list [])]) (evalDoms_mod (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, modσ, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 2, an iteration over empty lists, holds at the empty module. -/
theorem dprem2 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem2 :=
  dpremB_iterNil (xvs := [("jt", .list []), ("tag", .list [])]) (evalDoms_mod (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, modσ, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 4, an iteration over empty lists, holds at the empty module. -/
theorem dprem4 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem4 :=
  dpremB_iterNil (xvs := [("mem", .list []), ("mt", .list [])]) (evalDoms_mod (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, modσ, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 5, an iteration over empty lists, holds at the empty module. -/
theorem dprem5 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem5 :=
  dpremB_iterNil (xvs := [("table", .list []), ("tt", .list [])]) (evalDoms_mod (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, modσ, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 6, an iteration over empty lists, holds at the empty module. -/
theorem dprem6 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem6 :=
  dpremB_iterNil (xvs := [("dt", .list []), ("func", .list [])]) (evalDoms_mod (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, modσ, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 7, an iteration over empty lists, holds at the empty module. -/
theorem dprem7 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem7 :=
  dpremB_iterNil (xvs := [("data", .list []), ("ok", .list [])]) (evalDoms_mod (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, modσ, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 8, an iteration over empty lists, holds at the empty module. -/
theorem dprem8 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem8 :=
  dpremB_iterNil (xvs := [("elem", .list []), ("rt", .list [])]) (evalDoms_mod (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, modσ, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 10, an iteration over empty lists, holds at the empty module. -/
theorem dprem10 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem10 :=
  dpremB_iterNil (xvs := [("export", .list []), ("nm", .list []), ("xt_E", .list [])]) (evalDoms_mod (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, modσ, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 9, `Start_ok` over the absent start function, holds vacuously. -/
theorem dprem9 (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem9 :=
  .iterOptNone (xvs := [("start", .opt none)]) (evalDoms_mod (by
    simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, modσ, Map.binds,
      Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure])) (by simp) (by simp)

/-- `Module_ok`'s premise 14, `x* = $funcidx_nonfuncs(…)`, holds at the empty module when
`FuncidxEmpty B`. -/
theorem dprem14 (hf : FuncidxEmpty B) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) modPrem14 :=
  .ifPr (evalExp_cmpE_iff.2 ⟨_, _, ⟨10, by
      simp [evalExp, evalIterE, evalIterList, evalRounds, iterRows, Value.asList?, evalDoms,
        domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, modσ, Map.binds, Map.bind,
        Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure]⟩,
    evalExp_callE_iff.2 ((applies_iff_callDef (Memory.findDef_bindVals_empty _ _) ⟨10, by
      simp [evalArgs, evalArg, evalExps, evalIterE, evalIterList, evalRounds, iterRows,
        Value.asList?, Functor.map, Except.map, evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?,
        VarEnv.bindVals, modσ, Map.binds, Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption,
        Pure.pure, Except.pure]⟩).1 hf),
    Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩)

/-- **Every premise of `Module_ok` holds at the empty module**, given `FuncidxEmpty B`. -/
theorem dprems_mod (hf : FuncidxEmpty B) (O : ElseI) (els : Prop) :
    ∀ pr ∈ modPrems, DPremB (simEnv B) O els (VarEnv.empty.bindVals modσ) pr := by
  intro pr hpr
  simp only [modPrems, List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [dprem0 O els, dprem1 O els, dprem2 O els, dprem3 O els, dprem4 O els, dprem5 O els,
    dprem6 O els, dprem7 O els, dprem8 O els, dprem9 O els, dprem10 O els, dprem11 O els,
    dprem12 O els, dprem13 O els, dprem14 hf O els, dprem15 O els, dprem16 O els,
    dprem17 O els, dprem18 O els, dprem19 O els]

/-- **`Module_ok` validates the empty module**, at the module type `mt` the primitives give
`$clos_moduletype({}, [] -> [])`, in every evaluator where `$funcidx_nonfuncs` gives `[]` on
empty lists, under every reading of `otherwise`. -/
theorem moduleOk_empty (O : ElseI) {mt : Value}
    (hB : B.call "clos_moduletype" [.val Round6.RefOkV.ctxEmptyV, .val mtNil] = some mt)
    (hf : FuncidxEmpty B) :
    DDerivesB (simEnv B) O "Module_ok" "|-%:%" [] (.tuple [emptyModuleV, mt]) :=
  dderivesB_of_ruleAt ruleAt_moduleOk (self_mem_conclAlts _) modσ quantsOk_mod
    (evalExp_modConcl hB) (dprems_mod hf O _)

/-- **The repaired evaluator validates the empty module** at `[] -> []`: `stepModel (withClosMod B)`
has the `Module_ok` fact, given `FuncidxEmpty (withClosMod B)`. -/
theorem moduleOk_withClosMod (B : Builtins) (hf : FuncidxEmpty (withClosMod B)) :
    (Wasm30.stepModel (withClosMod B)).D "Module_ok" "|-%:%" [] (.tuple [emptyModuleV, mtNil]) :=
  moduleOk_empty _ rfl hf

/-- **`Instr30.Task.emptyModuleOk`, restated and reduced**: given the open `Task.funcidxEmpty`,
`stepModel (withClosMod BI)` validates the empty module, for every host and profile. -/
theorem emptyModuleOk_withClosMod (ht : Task.funcidxEmpty) {H : Type}
    (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) :
    ∃ mt, (Wasm30.stepModel (withClosMod (Round4Int.BI P hn host))).D "Module_ok" "|-%:%" []
      (.tuple [emptyModuleV, mt]) :=
  ⟨mtNil, moduleOk_withClosMod _ (ht _)⟩

/-- **`Instr30.Task.emptyModuleOk`, repaired**: `stepModel (withClosMod BI)` validates the empty
module at `[] -> []`, for every host and profile. -/
theorem emptyModuleOk_repaired {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) :
    (Wasm30.stepModel (withClosMod (Round4Int.BI P hn host))).D "Module_ok" "|-%:%" []
      (.tuple [emptyModuleV, mtNil]) :=
  moduleOk_withClosMod _ (funcidxEmpty _)

end Silmaril.Wasm.SpecTec.Institution.Instr30X
