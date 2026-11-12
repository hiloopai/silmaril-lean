module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30VModOk

/-!
# Module typing of the wasm-3.0 script, ws5 `Global_ok` has no facts

`Global_ok`'s rule (definition 368) has the premise `globaltype = %%(MUT?, t)`, in which `MUT?` is
an option iteration **without a domain**. The evaluator never evaluates such an iteration
(`evalIterE`, after `eval.ml:377-379`), and Round 6's reading `DDerivesB` repairs only
conclusions (`conclAlts`), not premises. So:

* `not_evalExp_mutOpt`, `not_evalExp_globalEq`: the premise never evaluates;
* `not_dd_globalOk`: `Global_ok` has no facts, in every `simEnv B`, under every reading of
  `otherwise`;
* `globalsOk_nil`: `Globals_ok` has facts only at the empty list of globals (its `cons` rule needs
  a `Global_ok` fact);
* `not_moduleOk_global`: no module value with a non-empty global position is a `Module_ok` fact;
* `globalModule_ok`, `globalModule_not_sat`: Core validates `(module (global i32 (i32.const 0)))`,
  so **the satisfaction condition fails at every module with a global**, in every `stepModel B`,
  with or without `withClosMod`.

The documented restatement (not built here): read an empty-domain `e?` in a premise as SpecTec's
backends do, as a fresh option variable (Round 6's `optAlts`, applied to premises as well as to
conclusions); under that reading `Global_ok`'s premise becomes `globaltype = %%(mut?, t)` for some
`mut?`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30V

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (ctxP)

variable {B : Builtins}

/-- `MUT?`, an option iteration with no domain. -/
def mutOptE : Exp := .iterE (.caseE "MUT" (.tupE [])) (.mk .opt [])

/-- `globaltype = %%(MUT?, t)`, `Global_ok`'s second premise. -/
def globalEqE : Exp :=
  .cmpE .eqOp .boolT (.varE "globaltype") (.caseE "%%" (.tupE [mutOptE, .varE "t"]))

/-- `Global_ok`'s rule. -/
def globalOkRule : Rule :=
  .ruleD "" [ctxP, .expP "globaltype" (.varT "globaltype" []), .expP "expr" (.varT "expr" []),
      .expP "t" (.varT "valtype" [])] "%|-%:%"
    (.tupE [.varE "C", .caseE "GLOBAL" (.tupE [.varE "globaltype", .varE "expr"]), .varE "globaltype"])
    [.rulePr "Globaltype_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "globaltype"]),
     .ifPr globalEqE,
     .rulePr "Expr_ok_const" [] "%|-%:%CONST" (.tupE [.varE "C", .varE "expr", .varE "t"])]

set_option maxRecDepth 100000 in
theorem rel_globalOk :
    ∃ t, (simEnv B).findRel? "Global_ok" = some ([], "%|-%:%", t, [globalOkRule]) := ⟨_, rfl⟩

/-- `MUT?` without a domain never evaluates. -/
theorem not_evalExp_mutOpt {env : Env} {ρ : VarEnv} {w : Value} : ¬ EvalExp env ρ mutOptE w := by
  rintro ⟨n, h⟩
  rcases n with _ | n
  · simp [evalExp] at h
  · simp only [mutOptE, evalExp] at h
    rcases n with _ | n
    · simp [evalIterE] at h
    · simp only [evalIterE, Bind.bind, Except.bind] at h
      split at h <;> simp [Res.assert] at h

/-- `globaltype = %%(MUT?, t)` never evaluates. -/
theorem not_evalExp_globalEq {env : Env} {ρ : VarEnv} {w : Value} : ¬ EvalExp env ρ globalEqE w := by
  intro h
  obtain ⟨_, _, -, h₂, -⟩ := evalExp_cmpE_iff.1 h
  obtain ⟨u, hu, -⟩ := evalExp_caseE_iff.1 h₂
  obtain ⟨us, hus, -⟩ := evalExp_tupE_iff.1 hu
  obtain ⟨_, _, hm, -, -⟩ := evalExps_cons_iff.1 hus
  exact not_evalExp_mutOpt hm

/-- **`Global_ok` has no facts**, in every evaluator `simEnv B` and under every reading of
`otherwise`: its premise `globaltype = %%(MUT?, t)` contains an option iteration without a domain,
which the evaluator never evaluates. -/
theorem not_dd_globalOk {O : ElseI} {v : Value} :
    ¬ DDerivesB (simEnv B) O "Global_ok" "%|-%:%" [] v := by
  intro h
  obtain ⟨t, hrel⟩ := rel_globalOk (B := B)
  obtain ⟨σ, -, hp⟩ := Instr30Z.dd_oneRule_inv hrel rfl h
  have h₂ := hp (.ifPr globalEqE) (by simp)
  cases h₂ with
  | ifPr he => exact not_evalExp_globalEq he

/-- `Globals_ok/empty`. -/
def globalsEmptyRule : Rule :=
  .ruleD "empty" [ctxP] "%|-%:%" (.tupE [.varE "C", .listE [], .listE []]) []

set_option maxRecDepth 100000 in
/-- `Globals_ok` has two rules: `empty`, and a `cons` rule whose first premise is `Global_ok`. -/
theorem rel_globalsOk : ∃ t qs e prems, (simEnv B).findRel? "Globals_ok" = some ([], "%|-%:%", t,
    [globalsEmptyRule, .ruleD "cons" qs "%|-%:%" e
      (.rulePr "Global_ok" [] "%|-%:%" (.tupE [.varE "C", .varE "global_1", .varE "gt_1"]) :: prems)]) ∧
    conclAlts e = [e] :=
  ⟨_, _, _, _, rfl, rfl⟩

/-- `Globals_ok/empty`'s conclusion `(C, [], [])` evaluates only to triples with `[]` second. -/
theorem globalsEmpty_concl_inv {env : Env} {ρ : VarEnv} {c w : Value} {gs : List Value}
    (he : EvalExp env ρ (.tupE [.varE "C", .listE [], .listE []]) (.tuple [c, .list gs, w])) :
    gs = [] := by
  obtain ⟨a, b, d, heq, -, hb, -⟩ := Round6.RefOkV.evalExp_tup3_ex he
  have hb' : b = .list [] := by
    obtain ⟨vs, hvs, hbv⟩ := evalExp_listE_iff.1 hb
    rw [hbv, evalExps_nil_iff.1 hvs]
  have hgs : Value.list gs = b := by
    simp only [Value.tuple.injEq, List.cons.injEq] at heq
    exact heq.2.1
  exact Value.list.inj (hgs.trans hb')

/-- A rule whose first premise is `Global_ok(C, global_1, gt_1)` never fires. -/
theorem not_globalPrem {O : ElseI} {els : Prop} {ρ : VarEnv} {prems : List Prem}
    (hp : ∀ pr ∈ .rulePr "Global_ok" [] "%|-%:%" (.tupE [.varE "C", .varE "global_1",
      .varE "gt_1"]) :: prems, DPremB (simEnv B) O els ρ pr) : False := by
  have h₀ := hp _ List.mem_cons_self
  cases h₀ with
  | rulePr ha _ hd =>
    have hav := Sem.evalArgs_nil_iff.1 ha
    exact not_dd_globalOk (hav ▸ hd)

/-- **`Globals_ok` has facts only at the empty list of globals.** -/
theorem globalsOk_nil {O : ElseI} {c w : Value} {gs : List Value}
    (h : DDerivesB (simEnv B) O "Globals_ok" "%|-%:%" [] (.tuple [c, .list gs, w])) : gs = [] := by
  obtain ⟨t, qs, e, prems, hrel, -⟩ := rel_globalsOk (B := B)
  cases h with
  | @rule _ _ _ _ _ _ _ i _ _ _ e' _ ρ₀ σ hrel' hrule halt hps _ he hp =>
    rw [hrel] at hrel'
    cases hrel'
    rcases i with _ | _ | i
    · show gs = []
      cases hrule
      have he' : e' = .tupE [.varE "C", .listE [], .listE []] :=
        List.mem_singleton.1 (show e' ∈ [_] from halt)
      exact globalsEmpty_concl_inv (he' ▸ he)
    · show gs = []
      cases hrule
      exact (not_globalPrem hp).elim
    · simp at hrule

/-- The module part of `Module_ok`'s conclusion, read back at the global position. -/
theorem modGlobals_inv {env : Env} {ρ : VarEnv} {a₀ a₁ a₂ G a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ : Value}
    (h : EvalExp env ρ Instr30W.modModE (.case "MODULE" (.tuple [a₀, a₁, a₂, .case "%" (.tuple [G]),
      a₄, a₅, a₆, a₇, a₈, a₉, a₁₀]))) : ρ.findVal? "global*" = some G := by
  have hc := Instr30W.evalExp_tupE_forall₂ (Instr30Z.evalExp_case_inv h)
  have hc₃ := List.forall₂_cons.1 (List.forall₂_cons.1 (List.forall₂_cons.1
    (List.forall₂_cons.1 hc).2).2).2
  exact Instr30W.pctStar_inv (by decide) hc₃.1

/-- Premise 3, `Globals_ok(C', global*, gt*)`, binds `global*` to `[]`. -/
theorem prem3_globals_nil {O : ElseI} {els : Prop} {ρ : VarEnv} {l : List Value}
    (hg : ρ.findVal? "global*" = some (.list l)) (h : DPremB (simEnv B) O els ρ Instr30X.modPrem3) :
    l = [] := by
  cases h with
  | rulePr ha hw hd =>
    have hav := Sem.evalArgs_nil_iff.1 ha
    obtain ⟨a, b, d, hwv, -, hb, -⟩ := Round6.RefOkV.evalExp_tup3_ex hw
    obtain ⟨l', hl', hbl⟩ := Instr30W.star_inv (by decide) hb
    have hll : l' = l := Value.list.inj (Option.some.inj (hl'.symm.trans hg))
    have hd' : DDerivesB (simEnv B) O "Globals_ok" "%|-%:%" [] (.tuple [a, .list l, d]) := by
      rw [← hll, ← hbl, ← hwv, ← hav]
      exact hd
    exact globalsOk_nil hd'

/-- **No module with a global is a `Module_ok` fact**, in every evaluator `simEnv B` and under
every reading of `otherwise`: premise 3, `Globals_ok(C', global*, gt*)`, would be a `Globals_ok`
fact at a non-empty list. -/
theorem not_moduleOk_global {O : ElseI} {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ g v : Value}
    {gs : List Value} :
    ¬ DDerivesB (simEnv B) O "Module_ok" "|-%:%" []
      (.tuple [.case "MODULE" (.tuple [a₀, a₁, a₂, .case "%" (.tuple [.list (g :: gs)]), a₄, a₅,
        a₆, a₇, a₈, a₉, a₁₀]), v]) := by
  intro h
  obtain ⟨t, hrel⟩ := Instr30W.rel_moduleOk (B := B)
  obtain ⟨σ, he, hp⟩ := Instr30Z.dd_oneRule_inv hrel Instr30W.conclAlts_modConcl h
  obtain ⟨hmod, -⟩ := Instr30Z.evalExp_tup2_inv' (Instr30W.modConcl_eq ▸ he)
  have hg : (VarEnv.empty.bindVals σ).findVal? "global*" = some (.list (g :: gs)) :=
    modGlobals_inv hmod
  have h₃ := hp Instr30X.modPrem3 (by simp [Instr30X.modPrems])
  exact List.cons_ne_nil _ _ (prem3_globals_nil hg h₃)

/-! ## Core validates modules with globals -/

/-- The immutable global `(global i32 (i32.const 0))`. -/
def global0 : Silmaril.Wasm.Global := ⟨⟨.const, .num (.int .i32)⟩, [.intConst .i32 0]⟩

/-- The Core module whose only definition is `global0`. -/
def globalModule : Silmaril.Wasm.Module := { globals := [global0] }

/-- **Core validates `globalModule`**, at `[] -> []`. -/
theorem globalModule_ok : Silmaril.Wasm.Validation.ModuleOk globalModule ⟨[], []⟩ :=
  .mk (dts := []) (jts := []) (gts := [⟨.const, .num (.int .i32)⟩]) (tts := []) (fdts := [])
    (rts := []) .nil .nil rfl rfl .nil
    (.cons ⟨rfl, Silmaril.Wasm.Validation.GlobalTypeOk.check_sound rfl,
      ⟨.instr (.numeric (.intConst _ _)), fun i hi => by
        obtain rfl := List.mem_singleton.1 hi
        exact .intConst _ _⟩⟩ .nil)
    (fun _ h => nomatch h) .nil .nil (fun _ h => nomatch h) .nil (fun _ h => nomatch h) .nil
    List.nodup_nil

/-- **Refutation of the satisfaction condition at modules with globals**: Core validates
`globalModule`, but in every evaluator `simEnv B` (so in every `stepModel B`, repaired by
`withClosMod` or not), no value with a global in the global position, in particular no image of
`globalModule`, is a `Module_ok` fact. -/
theorem globalModule_not_sat (O : ElseI) {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ g v : Value} :
    Silmaril.Wasm.Validation.ModuleOk globalModule ⟨[], []⟩ ∧
      ¬ DDerivesB (simEnv B) O "Module_ok" "|-%:%" []
        (.tuple [.case "MODULE" (.tuple [a₀, a₁, a₂, .case "%" (.tuple [.list [g]]), a₄, a₅,
          a₆, a₇, a₈, a₉, a₁₀]), v]) :=
  ⟨globalModule_ok, not_moduleOk_global⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30V
