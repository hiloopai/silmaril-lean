module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Determ.FwdOn
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Determ.Inv
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Determ.Typ

/-!
# Round 7, determination: the mode check is sound

At a rule instance in `utf8Env B` (with `B` preserving `ExpFree`), each premise that holds gives a
fact (`PremFact`): an `if` evaluates to `true`, a `let` has a value both sides evaluate to, and a
relation premise evaluates to a value that is `ExpFree` whenever its input is (this is the
induction hypothesis of the determination proof). From these facts, every variable the mode
check (`Round7.Determ.ruleK`) adds is bound to an `ExpFree` value (`efOn_ruleK`):

* the quantifiers typed over `tyA`, by typing (`Round7.Determ.ef_of_hasTyp_A`);
* the `invVars` of the conclusion's input, by inverting the evaluator (`Round7.Determ.ef_inv`);
* each round of `premStep`, by the forward lemma (`Round7.Determ.ef_eval_on`) on the known side
  and inversion on the other.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (ExpFree tyA tyOk TypsOk)

/-! ## Facts about evaluation -/

theorem efOn_append {ρ : VarEnv} {K L : List IL.Id} (hK : EFOn ρ K) (hL : EFOn ρ L) :
    EFOn ρ (K ++ L) := fun x hx => (List.mem_append.1 hx).elim (hK x) (hL x)

theorem efOn_nil (ρ : VarEnv) : EFOn ρ [] := fun _ h => by cases h

theorem efOn_invVars {env : Env} {ρ : VarEnv} {e : Exp} {v : Value} (h : EvalExp env ρ e v)
    (hv : ExpFree v) : EFOn ρ (invVars e) := by
  obtain ⟨n, hn⟩ := h
  exact ef_inv env n ρ e v hn hv

theorem evalExp_cmpE_eq {env : Env} {ρ : VarEnv} {t : OpTyp} {a b : Exp}
    (h : EvalExp env ρ (.cmpE .eqOp t a b) (.bool true)) :
    ∃ v, EvalExp env ρ a v ∧ EvalExp env ρ b v := by
  obtain ⟨n, hn⟩ := h
  rcases n with _ | n
  · simp [evalExp] at hn
  simp only [evalExp, Res.bind_eq_ok, cmpValues, Except.ok.injEq, Value.bool.injEq,
    beq_iff_eq] at hn
  obtain ⟨va, ha, vb, hb, rfl⟩ := hn
  exact ⟨va, ⟨n, ha⟩, ⟨n, hb⟩⟩

theorem evalExp_memE_true {env : Env} {ρ : VarEnv} {a b : Exp}
    (h : EvalExp env ρ (.memE a b) (.bool true)) :
    ∃ va vb, EvalExp env ρ a va ∧ EvalExp env ρ b vb ∧ (ExpFree vb → ExpFree va) := by
  obtain ⟨n, hn⟩ := h
  rcases n with _ | n
  · simp [evalExp] at hn
  simp only [evalExp, Res.bind_eq_ok] at hn
  obtain ⟨va, ha, vb, hb, hm⟩ := hn
  refine ⟨va, vb, ⟨n, ha⟩, ⟨n, hb⟩, fun hvb => ?_⟩
  unfold memValue at hm
  split at hm
  · simp at hm
  · simp only [Except.ok.injEq, Value.bool.injEq, beq_iff_eq] at hm
    subst hm
    exact ef_optSome.1 hvb
  · simp only [Except.ok.injEq, Value.bool.injEq, List.contains_iff_mem] at hm
    exact ef_list.1 hvb va hm
  · cases hm

theorem evalExp_tupE_cons {env : Env} {ρ : VarEnv} {a : Exp} {rest : List Exp} {w : Value}
    (h : EvalExp env ρ (.tupE (a :: rest)) w) :
    ∃ va vs, w = .tuple (va :: vs) ∧ EvalExp env ρ a va := by
  obtain ⟨n, hn⟩ := h
  rcases n with _ | _ | n
  · simp [evalExp] at hn
  · simp [evalExp, evalExps] at hn
  simp only [evalExp, evalExps, Res.map_eq_ok, List.mapM_cons, Res.bind_eq_ok] at hn
  obtain ⟨_, ⟨va, ha, vs, _, hp⟩, hw⟩ := hn
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hp
  subst hp; subst hw
  exact ⟨va, vs, rfl, ⟨n, ha⟩⟩

/-! ## One premise -/

variable {B : Builtins}

/-- What a premise that holds says about its scope, for the mode check. -/
def PremFact (B : Builtins) (ρ : VarEnv) : Prem → Prop
  | .ifPr e => EvalExp (utf8Env B) ρ e (.bool true)
  | .letPr e₁ e₂ => ∃ w, EvalExp (utf8Env B) ρ e₂ w ∧ EvalExp (utf8Env B) ρ e₁ w
  | .rulePr _ _ _ e => ∃ w, EvalExp (utf8Env B) ρ e w ∧ (InEF w → ExpFree w)
  | _ => True

theorem premStep_cmp (hB : BuiltinsEF B) {ρ : VarEnv} {K : List IL.Id} {t : OpTyp} {a b : Exp}
    (hD : DefsOk ρ) (hGa : GoodXs (evExp a)) (hGb : GoodXs (evExp b)) (hK : EFOn ρ K)
    (h : EvalExp (utf8Env B) ρ (.cmpE .eqOp t a b) (.bool true)) :
    EFOn ρ ((if fvIn K a then invVars b else []) ++ (if fvIn K b then invVars a else [])) := by
  obtain ⟨v, ha, hb⟩ := evalExp_cmpE_eq h
  have h₁ : EFOn ρ (if fvIn K a then invVars b else []) := by
    split
    · exact efOn_invVars hb (ef_eval_on hB hD hGa hK (by assumption) ha)
    · exact efOn_nil ρ
  have h₂ : EFOn ρ (if fvIn K b then invVars a else []) := by
    split
    · exact efOn_invVars ha (ef_eval_on hB hD hGb hK (by assumption) hb)
    · exact efOn_nil ρ
  exact efOn_append h₁ h₂

theorem premStep_mem (hB : BuiltinsEF B) {ρ : VarEnv} {K : List IL.Id} {a b : Exp}
    (hD : DefsOk ρ) (hGb : GoodXs (evExp b)) (hK : EFOn ρ K)
    (h : EvalExp (utf8Env B) ρ (.memE a b) (.bool true)) :
    EFOn ρ (if fvIn K b then invVars a else []) := by
  obtain ⟨va, vb, ha, hb, himp⟩ := evalExp_memE_true h
  split
  · exact efOn_invVars ha (himp (ef_eval_on hB hD hGb hK (by assumption) hb))
  · exact efOn_nil ρ

theorem premStep_let (hB : BuiltinsEF B) {ρ : VarEnv} {K : List IL.Id} {a b : Exp}
    (hD : DefsOk ρ) (hGb : GoodXs (evExp b)) (hK : EFOn ρ K)
    (h : ∃ w, EvalExp (utf8Env B) ρ b w ∧ EvalExp (utf8Env B) ρ a w) :
    EFOn ρ (if fvIn K b then invVars a else []) := by
  obtain ⟨w, hb, ha⟩ := h
  split
  · exact efOn_invVars ha (ef_eval_on hB hD hGb hK (by assumption) hb)
  · exact efOn_nil ρ

theorem premStep_rule (hB : BuiltinsEF B) {ρ : VarEnv} {K : List IL.Id} {a : Exp}
    {rest : List Exp} (hD : DefsOk ρ) (hGa : GoodXs (evExp a)) (hK : EFOn ρ K)
    (h : ∃ w, EvalExp (utf8Env B) ρ (.tupE (a :: rest)) w ∧ (InEF w → ExpFree w)) :
    EFOn ρ (if fvIn K a then invVarsL (a :: rest) else []) := by
  obtain ⟨w, he, himp⟩ := h
  split
  · rename_i hfv
    obtain ⟨va, vs, rfl, ha⟩ := evalExp_tupE_cons he
    have hva : ExpFree va := ef_eval_on hB hD hGa hK hfv ha
    have hin : InEF (.tuple (va :: vs)) := fun a' r' heq => by
      cases heq; exact hva
    exact efOn_invVars (e := .tupE (a :: rest)) he (himp hin)
  · exact efOn_nil ρ

/-- **One premise that holds adds only `ExpFree` variables.** -/
theorem efOn_premStep (hB : BuiltinsEF B) {ρ : VarEnv} {K : List IL.Id} {pr : Prem}
    (hD : DefsOk ρ) (hG : GoodXs (evPrem pr)) (hK : EFOn ρ K) (hf : PremFact B ρ pr) :
    EFOn ρ (premStep K pr) := by
  unfold premStep
  split
  · simp only [evPrem, evExp, goodXs_append] at hG
    exact premStep_cmp hB hD hG.1 hG.2 hK hf
  · simp only [evPrem, evExp, goodXs_append] at hG
    exact premStep_mem hB hD hG.2 hK hf
  · simp only [evPrem, goodXs_append] at hG
    exact premStep_let hB hD hG.2 hK hf
  · simp only [evPrem, evExp, evExps, goodXs_cons, goodXs_append] at hG
    exact premStep_rule hB hD hG.2.2.1 hK hf
  · exact efOn_nil ρ

/-- **Every round of the mode check adds only `ExpFree` variables.** -/
theorem efOn_modeK (hB : BuiltinsEF B) {ρ : VarEnv} {prems : List Prem} (hD : DefsOk ρ)
    (hG : ∀ pr ∈ prems, GoodXs (evPrem pr)) (hf : ∀ pr ∈ prems, PremFact B ρ pr) :
    ∀ n K, EFOn ρ K → EFOn ρ (modeK prems n K)
  | 0, K, hK => hK
  | n + 1, K, hK => by
    have hstep : EFOn ρ (prems.flatMap (premStep K)) := fun x hx => by
      obtain ⟨pr, hpr, hx'⟩ := List.mem_flatMap.1 hx
      exact efOn_premStep hB hD (hG pr hpr) hK (hf pr hpr) x hx'
    exact efOn_modeK hB hD hG hf n _ (efOn_append hK hstep)

/-! ## The starting set -/

theorem efOn_quantsA {ρ : VarEnv} {qs : List Param} (hT : TypsOk tyA ρ)
    (hq : QuantsOk (utf8Env B) ρ qs) : EFOn ρ (quantsA qs) := by
  intro x hx w hw
  simp only [quantsA, List.mem_filterMap] at hx
  obtain ⟨q, hq', hqx⟩ := hx
  cases q with
  | expP y t =>
    simp only at hqx
    split at hqx
    · rename_i ht
      cases hqx
      obtain ⟨w', hw', hty⟩ := hq x t hq'
      rw [hw] at hw'
      cases hw'
      exact ef_of_hasTyp_A B hT ht hty
    · cases hqx
  | _ => simp at hqx

theorem efOn_concl {env : Env} {ρ : VarEnv} {e' : Exp} {v : Value} (he : EvalExp env ρ e' v)
    (hin : InEF v) : EFOn ρ (conclIn e') := by
  cases e' <;> try exact efOn_nil ρ
  rename_i es
  cases es with
  | nil => exact efOn_nil ρ
  | cons a rest =>
    obtain ⟨va, vs, hv, ha⟩ := evalExp_tupE_cons he
    exact efOn_invVars ha (hin va vs hv)

/-- **Every variable the mode check knows is bound to an `ExpFree` value.** -/
theorem efOn_ruleK (hB : BuiltinsEF B) {ρ : VarEnv} {qs : List Param} {e' : Exp}
    {prems : List Prem} {v : Value} (hD : DefsOk ρ) (hT : TypsOk tyA ρ)
    (hq : QuantsOk (utf8Env B) ρ qs) (he : EvalExp (utf8Env B) ρ e' v) (hin : InEF v)
    (hG : ∀ pr ∈ prems, GoodXs (evPrem pr)) (hf : ∀ pr ∈ prems, PremFact B ρ pr) :
    EFOn ρ (ruleK qs e' prems) :=
  efOn_modeK hB hD hG hf 3 _ (efOn_append (efOn_quantsA hT hq) (efOn_concl he hin))

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ
