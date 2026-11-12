module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30VGlobal

/-!
# Instruction typing of the wasm-3.0 script, ws5 `br_on_non_null` has no type

`Instr_ok/br_on_non_null` has the premise `C.LABELS[l] = %(t* ++ [REF NULL? ht])`, whose `NULL?`
is an option iteration without a domain, like `Global_ok`'s `MUT?` (`Instr30VGlobal`). The
evaluator never evaluates it, and `DDerivesB` repairs only conclusions, so:

* `brnnCheck`, `instrOk_brnnCheck`: by `decide` on the rule list of `simEnv B`, every rule of
  `Instr_ok` whose instruction head is `BR_ON_NON_NULL` has a premise of the stuck shape
  (`nullOptStuck`);
* `not_dpremB_stuck`: a premise of that shape never holds;
* `not_dd_brOnNonNull`: **no `Instr_ok` fact has the instruction `BR_ON_NON_NULL l`**, in every
  `simEnv B`, context, label and type, under every reading of `otherwise`;
* `brOnNonNull_not_sat`: Core types `br_on_non_null 0` in `{labels := [[ref n ht]]}` at
  `[ref null ht] -> []`, so the satisfaction condition of the instruction-typing comorphism fails
  there.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30V

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Institution.Instr30 (instrHead ruleHead instrHead_some eval_head
  mem_conclAlts_head head_of_headsOk instrOk_heads)

variable {B : Builtins}

/-- An option iteration without a domain never evaluates, whatever its body. -/
theorem not_evalExp_optNil {env : Env} {ρ : VarEnv} {e : Exp} {w : Value} :
    ¬ EvalExp env ρ (.iterE e (.mk .opt [])) w := by
  rintro ⟨n, h⟩
  rcases n with _ | n
  · simp [evalExp] at h
  · simp only [evalExp] at h
    rcases n with _ | n
    · simp [evalIterE] at h
    · simp only [evalIterE, Bind.bind, Except.bind] at h
      split at h <;> simp [Res.assert] at h

/-- The stuck shape: `if a = %(b ++ [REF(e?, c)])` with `e?` an option iteration without a
domain. -/
def nullOptStuck : Prem → Bool
  | .ifPr (.cmpE .eqOp .boolT _ (.caseE "%" (.tupE [.catE _
      (.listE [.caseE "REF" (.tupE [.iterE _ (.mk .opt []), _])])]))) => true
  | _ => false

/-- **A premise of the stuck shape never holds.** -/
theorem not_dpremB_stuck {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem}
    (hs : nullOptStuck pr = true) : ¬ DPremB env O els ρ pr := by
  unfold nullOptStuck at hs
  split at hs
  · intro h
    cases h with
    | ifPr he =>
      obtain ⟨_, _, -, h₂, -⟩ := evalExp_cmpE_iff.1 he
      obtain ⟨_, hu, -⟩ := evalExp_caseE_iff.1 h₂
      obtain ⟨_, hus, -⟩ := evalExp_tupE_iff.1 hu
      obtain ⟨_, _, hc, -, -⟩ := evalExps_cons_iff.1 hus
      obtain ⟨_, _, -, hl, -⟩ := evalExp_catE_iff.1 hc
      obtain ⟨_, hls, -⟩ := evalExp_listE_iff.1 hl
      obtain ⟨_, _, hr, -, -⟩ := evalExps_cons_iff.1 hls
      obtain ⟨_, hr', -⟩ := evalExp_caseE_iff.1 hr
      obtain ⟨_, hrs, -⟩ := evalExp_tupE_iff.1 hr'
      obtain ⟨_, _, ho, -, -⟩ := evalExps_cons_iff.1 hrs
      exact not_evalExp_optNil ho
  · exact absurd hs Bool.false_ne_true

/-- Every rule of the list typing `BR_ON_NON_NULL` has a premise of the stuck shape. -/
def brnnCheck (rules : List Rule) : Bool :=
  rules.all fun
    | .ruleD _ _ _ e prems => instrHead e != some "BR_ON_NON_NULL" || prems.any nullOptStuck

set_option maxRecDepth 100000 in
/-- **The rule list of `Instr_ok` passes `brnnCheck`.** -/
theorem instrOk_brnnCheck : ∃ ps t rules,
    (simEnv B).findRel? "Instr_ok" = some (ps, "%|-%:%", t, rules) ∧ brnnCheck rules = true :=
  ⟨_, _, _, rfl, by decide⟩

/-- **No `Instr_ok` fact has the instruction `BR_ON_NON_NULL l`**, in every evaluator `simEnv B`,
at every context, label and type, under every reading of `otherwise`. -/
theorem not_dd_brOnNonNull {O : ElseI} {c w it : Value} :
    ¬ DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" [] (.tuple [c, .case "BR_ON_NON_NULL" w, it]) := by
  intro h
  cases h with
  | @rule _ _ _ _ _ _ rules j nm qs e e' prems ρ₀ σ hrel hrule halt hps _ he hp =>
    obtain ⟨ps₁, t₁, rules₁, hrel₁, hchk⟩ := instrOk_brnnCheck (B := B)
    obtain ⟨ps₀, t₀, rules₀, hrel₀, hok⟩ := instrOk_heads (B := B)
    rw [hrel] at hrel₁ hrel₀
    obtain rfl : rules = rules₁ := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj
      (Option.some.inj hrel₁)).2).2).2
    obtain rfl : rules = rules₀ := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj
      (Option.some.inj hrel₀)).2).2).2
    obtain ⟨o, hho, -⟩ := head_of_headsOk hok hrule
    obtain ⟨a, b, c', rfl⟩ := instrHead_some hho
    obtain ⟨a', b', c'', rfl⟩ := mem_conclAlts_head halt
    have hoe : o = "BR_ON_NON_NULL" := eval_head he
    have hr := List.all_eq_true.1 hchk _ (List.mem_of_getElem? hrule)
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true] at hr
    rcases hr with hr | ⟨pr, hpr, hs⟩
    · exact hr (hoe ▸ hho)
    · exact not_dpremB_stuck hs (hp pr hpr)

/-- **Refutation of the satisfaction condition at `br_on_non_null`**: Core types
`br_on_non_null 0` in the context whose one label is `[ref n ht]`, at `[ref null ht] -> []`, while
no context value, type or label index makes its image an `Instr_ok` fact of any `simEnv B`. -/
theorem brOnNonNull_not_sat (O : ElseI) (n : Bool) (ht : Silmaril.Wasm.Validation.CHeapType)
    {c it : Value} :
    Silmaril.Wasm.Validation.InstrOk { labels := [[.refT n ht]] } (.brOnNonNull ⟨0⟩)
        (.plain [.refT true ht] []) ∧
      ¬ DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
        (.tuple [c, instrToV (.brOnNonNull ⟨0⟩), it]) :=
  ⟨.brOnNonNull (ts := []) rfl, not_dd_brOnNonNull⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30V
