module

public import Silmaril.Wasm.SpecTec.Institution.Instr30.Thms
public import Silmaril.Wasm.SpecTec.Institution.Instr30X.Defs

/-!
# Instruction typing of the wasm-3.0 script, extended: `Module_ok` has no facts

`Instr30` froze `Task.emptyModuleOk`: `stepModel BI` validates the empty module at some module
type. Unfolding `Module_ok`'s one rule at the empty module shows the target is false, for a reason
that has nothing to do with the empty module:

* the rule's conclusion is `(MODULE …, $clos_moduletype(C, xt_I* -> xt_E*))`
  (`moduleOk_rules`, checked on the rule list of `simEnv B` by a kernel `rfl`);
* `$clos_moduletype`'s one clause binds `dt*` only in its premise
  `if dt* = $clos_deftypes(C.TYPES)`. The evaluator reads an `if` premise as a test, not a
  binding, so the clause definitely fails (`tryClausesUndef_closMod`), and the concrete primitives
  `Prims.builtins` have no entry for it (`call_closMod`): **`$clos_moduletype` never has a value**
  (`not_callDef_closMod`), exactly as round 6 found for `$clos_deftype`
  (`Round6.TyElim.not_applies_closDeftype`);
* so no conclusion of `Module_ok` evaluates, and `Module_ok` has no `DDerivesB` facts at all
  (`not_moduleOk`), under every reading of `otherwise`, at every argument and value.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (TryClausesUndef not_tryClauses_and_undef callDef_iff)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading

/-- `$clos_moduletype`'s clause, copied from `Raw/…/Scripts/Wasm30/Original/Part1.lean`
(definition 323). -/
def closModClauses : List Clause :=
  [(Clause.defD [(Param.expP "C" (Typ.varT "context"
  [])), (Param.expP "mmt" (Typ.varT "moduletype" [])), (Param.expP "dt*" (Typ.iterT (Typ.varT "deftype"
  []) Iter.list))] [(Arg.expA (Exp.varE "C")), (Arg.expA (Exp.varE "mmt"))] (Exp.callE "subst_all_moduletype"
  [(Arg.expA (Exp.varE "mmt")), (Arg.expA (Exp.iterE (Exp.subE (Exp.varE "dt") (Typ.varT "deftype"
  []) (Typ.varT "typeuse" [])) (IterExp.mk Iter.list [(Dom.mk "dt" (Exp.varE "dt*"))])))]) [(Prem.ifPr
  (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.iterE (Exp.varE "dt") (IterExp.mk Iter.list [(Dom.mk "dt"
  (Exp.varE "dt*"))])) (Exp.callE "clos_deftypes" [(Arg.expA (Exp.dotE (Exp.varE "C") "TYPES"))])))])]

variable {B : Builtins}

set_option maxRecDepth 100000 in
/-- `$clos_moduletype`'s clauses in `simEnv B`. -/
theorem findDef_closMod : ∃ ps t, (simEnv B).findDef? "clos_moduletype" = some (ps, t, closModClauses) :=
  ⟨_, _, rfl⟩

/-- The concrete primitives do not answer `$clos_moduletype`. -/
theorem call_closMod {H : Type} {prof : Silmaril.Wasm.Numerics.Profile} (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H)
    (ws : List ArgV) : (Prims.builtins prof hn host).call "clos_moduletype" ws = none := by
  simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]

/-- `$clos_moduletype`'s clause definitely fails: `dt*` is unbound in its `if` premise. -/
theorem tryClausesUndef_closMod (c m : Value) :
    TryClausesUndef (simEnv B) closModClauses [.val c, .val m] :=
  IntNumeric.tryClausesUndef_skip_prem (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
    (Prims.premsUndef_if (Prims.evalExpUndef_cmpL (Prims.evalExpUndef_iterList
      (Prims.evalExpUndef_var rfl)))) IntNumeric.tryClausesUndef_nil

/-- The shape of a conclusion `(_, $clos_moduletype(_, _))`. -/
def closConcl : Exp → Bool
  | .tupE [_, .callE f [.expA _, .expA _]] => f == "clos_moduletype"
  | _ => false

/-- A rule whose conclusion is `(_, $clos_moduletype(_, _))`, with no optional atoms. -/
def ruleClos : Rule → Bool
  | .ruleD _ _ _ e _ => closConcl e && !hasOptNil e

set_option maxRecDepth 100000 in
/-- **`Module_ok` has no parameters, and each of its rules concludes with a call of
`$clos_moduletype`.** -/
theorem moduleOk_rules : ∃ t rules, (simEnv B).findRel? "Module_ok" = some ([], "|-%:%", t, rules) ∧
    rules.all ruleClos = true :=
  ⟨_, _, rfl, rfl⟩


/-- The shape `closConcl` checks. -/
theorem closConcl_inv {e : Exp} (h : closConcl e = true) :
    ∃ a x y, e = .tupE [a, .callE "clos_moduletype" [.expA x, .expA y]] := by
  unfold closConcl at h
  split at h
  · obtain rfl := beq_iff_eq.1 h
    exact ⟨_, _, _, rfl⟩
  · cases h

/-- `$clos_moduletype` has no value, on the concrete primitives. -/
theorem not_callDef_closMod {H : Type} {prof : Silmaril.Wasm.Numerics.Profile} {hn : H → String}
    {host : Silmaril.Wasm.Execution.Core.HostSemantics H} {ρ : VarEnv} {x y : Exp} {v : Value}
    (hρ : ρ.findDef? "clos_moduletype" = none) :
    ¬ CallDef (simEnv (Prims.builtins prof hn host)) ρ "clos_moduletype" [.expA x, .expA y] v := by
  intro h
  obtain ⟨ws, ps, t, cs, ha, hd, hc⟩ := callDef_iff.1 h
  rw [hρ, Option.getD_none] at hd hc
  obtain ⟨c, ws₁, -, ha₁, rfl⟩ := Round5.BwdStep.evalArgs_cons_inv ha
  obtain ⟨m, ws₂, -, ha₂, rfl⟩ := Round5.BwdStep.evalArgs_cons_inv ha₁
  obtain rfl := evalArgs_nil_iff.1 ha₂
  obtain ⟨ps', t', hd'⟩ := findDef_closMod (B := Prims.builtins prof hn host)
  obtain rfl : cs = closModClauses := by rw [hd'] at hd; cases hd; rfl
  rcases hc with hc | ⟨-, hb⟩
  · exact not_tryClauses_and_undef hc (tryClausesUndef_closMod c m)
  · rw [simEnv, Env.builtins_withBuiltins, call_closMod] at hb
    cases hb

/-- **`Module_ok` has no facts** under `DDerivesB`, on the concrete primitives: its one rule
concludes `$clos_moduletype(C, …)`, which has no value. -/
theorem not_moduleOk {H : Type} {prof : Silmaril.Wasm.Numerics.Profile} {hn : H → String}
    {host : Silmaril.Wasm.Execution.Core.HostSemantics H} {O : ElseI} {op : MixopS}
    {args : List ArgV} {v : Value} :
    ¬ DDerivesB (simEnv (Prims.builtins prof hn host)) O "Module_ok" op args v := by
  intro h
  cases h with
  | rule hrel hrule halt hps _ he _ =>
    obtain ⟨t₀, rules₀, hrel₀, hall⟩ := moduleOk_rules (B := Prims.builtins prof hn host)
    rw [hrel₀] at hrel
    cases hrel
    have hr := List.all_eq_true.1 hall _ (List.mem_of_getElem? hrule)
    simp only [ruleClos, Bool.and_eq_true, Bool.not_eq_true'] at hr
    obtain ⟨a, x, y, rfl⟩ := closConcl_inv hr.1
    simp only [conclAlts, hr.2, List.mem_cons, List.not_mem_nil, or_false, Bool.false_eq_true,
      ite_false] at halt
    subst halt
    cases args <;> simp only [bindParams, Option.some.injEq, reduceCtorEq] at hps
    subst hps
    obtain ⟨vs, hvs, -⟩ := evalExp_tupE_iff.1 he
    obtain ⟨-, ws, -, -, hws⟩ := Silmaril.SpecTec.Equiv.Validation.evalExps_cons_iff.1 hvs
    obtain ⟨w, -, -, hw, -⟩ := Silmaril.SpecTec.Equiv.Validation.evalExps_cons_iff.1 hws
    exact not_callDef_closMod (Memory.findDef_bindVals_empty _ _) (evalExp_callE_iff.1 hw)

/-- **`stepModel BI` has no `Module_ok` fact**, at any argument and value. -/
theorem stepModel_not_moduleOk {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) (args : List ArgV) (v : Value) :
    ¬ (Wasm30.stepModel (Round4Int.BI P hn host)).D "Module_ok" "|-%:%" args v :=
  not_moduleOk

/-- **Refutation of `Instr30.Task.emptyModuleOk`**: at `H = Empty`, the deterministic profile that
never grows, and the host that never answers, `stepModel BI` validates the empty module at no
module type (at no module at all). -/
theorem not_emptyModuleOk : ¬ Instr30.Task.emptyModuleOk := fun h =>
  let ⟨_, hm⟩ := h Empty (Silmaril.Wasm.Numerics.Profile.deterministic fun _ _ _ _ => false)
    Empty.elim (fun _ _ _ _ => False)
  stepModel_not_moduleOk _ _ _ _ _ hm

end Silmaril.Wasm.SpecTec.Institution.Instr30X
