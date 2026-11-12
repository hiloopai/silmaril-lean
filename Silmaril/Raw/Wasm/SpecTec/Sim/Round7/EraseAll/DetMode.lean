module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.DetInv
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.DetTyp
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Det.Defs

/-!
# Round 7, the export swap: the mode check keeps the swap set (unrefined)

The `AllIn Q` copy of `Round7.Determ.efOn_ruleK` and of the scope lemmas it uses.

* **Locality** (`ai_eval_on`): `Round7.EraseAll.eraseAt` needs every term binding of the scope in
  the swap set. A rule instance's scope may bind other names to anything. The evaluator reads only
  the free variables of the expression (`Silmaril.SpecTec.Sem.evalExp_agreeOn`), so it is enough
  that those are in the swap set: the scope `aiPart Q ρ`, which keeps only the swap-set bindings of
  `ρ`, agrees with `ρ` on them.
* `aiOn_ruleK`: at a rule instance whose premises hold (`PremFactQ`), every variable the mode
  check knows is bound to a value in the swap set: the quantifiers typed over `tyA` by typing
  (`nx_of_hasTyp_A`), the `invVars` of the conclusion's input by inversion (`ai_inv`), and each
  round of `premStep` by the forward lemma on the known side and inversion on the other.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (ScopeIn)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (mapM_ok_mem)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (tyA tyOk TypsOk)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (invVars invVarsL fvIn fvIn_mem premStep modeK quantsA
  conclIn ruleK evalExp_cmpE_eq evalExp_tupE_cons find?_binds mapM_option_mem)

variable {Q : Value → Prop}

/-! ## Locality -/

open Classical in
/-- The swap-set bindings of `ρ`. -/
noncomputable def aiPart (Q : Value → Prop) (ρ : VarEnv) : VarEnv :=
  { ρ with vals := ρ.vals.filter fun p => decide (AllIn Q p.2) }

theorem scopeIn_aiPart (ρ : VarEnv) : ScopeIn Q (aiPart Q ρ) := by
  intro p hp
  simp only [aiPart, List.mem_filter, decide_eq_true_eq] at hp
  exact hp.2

open Classical in
theorem find?_filter_ai {x : IL.Id} :
    ∀ l : Map Value, (∀ w, Map.find? l x = some w → AllIn Q w) →
      Map.find? (l.filter fun p => decide (AllIn Q p.2)) x = Map.find? l x
  | [], _ => rfl
  | (y, v) :: l, h => by
    by_cases hy : y = x
    · subst hy
      have hv : AllIn Q v := h v (by simp)
      simp [hv]
    · have hl : ∀ w, Map.find? l x = some w → AllIn Q w := fun w hw => h w (by simp [hy, hw])
      by_cases hv : AllIn Q v <;>
        simp [hv, hy, find?_filter_ai l hl]

theorem agreeOn_aiPart {ρ : VarEnv} {K : List IL.Id} {e : Exp} (hK : AIOn Q ρ K)
    (hfv : fvIn K e = true) : VarEnv.AgreeOn (freeExp e) ρ (aiPart Q ρ) := by
  refine ⟨fun x hx => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have hx' : ∀ w, Map.find? ρ.vals x = some w → AllIn Q w := hK x (fvIn_mem hfv x hx)
  exact (find?_filter_ai ρ.vals hx').symm

/-- **The evaluator answers a swap-set value** on checked syntax, when the free variables of the
expression are bound to swap-set values. -/
theorem ai_eval_on {gr gd : String → Bool} {env : Env} (H : Hyps Q gr gd env) {ρ : VarEnv}
    {K : List IL.Id} {e : Exp} {v : Value} (hD : DefsG gd ρ) (hx : xExp gr gd e = true)
    (hK : AIOn Q ρ K) (hfv : fvIn K e = true) (h : EvalExp env ρ e v) : AllIn Q v := by
  obtain ⟨n, hn⟩ := h
  have heq : evalExp n env ρ e = evalExp n env (aiPart Q ρ) e :=
    evalExp_agreeOn (agreeOn_aiPart hK hfv)
  exact allIn_of_evalExp H ⟨scopeIn_aiPart ρ, hD⟩ hx ⟨n, heq ▸ hn⟩

/-! ## Facts about evaluation -/

theorem aiOn_append {ρ : VarEnv} {K L : List IL.Id} (hK : AIOn Q ρ K) (hL : AIOn Q ρ L) :
    AIOn Q ρ (K ++ L) := fun x hx => (List.mem_append.1 hx).elim (hK x) (hL x)

theorem aiOn_nil (ρ : VarEnv) : AIOn Q ρ [] := fun _ h => by cases h

theorem aiOn_invVars {env : Env} {ρ : VarEnv} {e : Exp} {v : Value} (h : EvalExp env ρ e v)
    (hv : AllIn Q v) : AIOn Q ρ (invVars e) := by
  obtain ⟨n, hn⟩ := h
  exact ai_inv Q env n ρ e v hn hv

theorem evalExp_memE_true_ai {env : Env} {ρ : VarEnv} {a b : Exp}
    (h : EvalExp env ρ (.memE a b) (.bool true)) :
    ∃ va vb, EvalExp env ρ a va ∧ EvalExp env ρ b vb ∧ (AllIn Q vb → AllIn Q va) := by
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
    exact ai_optSome.1 hvb
  · simp only [Except.ok.injEq, Value.bool.injEq, List.contains_iff_mem] at hm
    exact ai_list.1 hvb va hm
  · cases hm

/-! ## One premise -/

/-- What a premise that holds says about its scope, for the mode check. -/
def PremFactQ (Q : Value → Prop) (env : Env) (ρ : VarEnv) : Prem → Prop
  | .ifPr e => EvalExp env ρ e (.bool true)
  | .letPr e₁ e₂ => ∃ w, EvalExp env ρ e₂ w ∧ EvalExp env ρ e₁ w
  | .rulePr _ _ _ e => ∃ w, EvalExp env ρ e w ∧ (InAI Q w → AllIn Q w)
  | _ => True

section
variable {gr gd : String → Bool} {env : Env}

theorem aiPremStep_cmp (H : Hyps Q gr gd env) {ρ : VarEnv} {K : List IL.Id} {t : OpTyp}
    {a b : Exp} (hD : DefsG gd ρ) (hxa : xExp gr gd a = true) (hxb : xExp gr gd b = true)
    (hK : AIOn Q ρ K) (h : EvalExp env ρ (.cmpE .eqOp t a b) (.bool true)) :
    AIOn Q ρ ((if fvIn K a then invVars b else []) ++ (if fvIn K b then invVars a else [])) := by
  obtain ⟨v, ha, hb⟩ := evalExp_cmpE_eq h
  have h₁ : AIOn Q ρ (if fvIn K a then invVars b else []) := by
    split
    · exact aiOn_invVars hb (ai_eval_on H hD hxa hK (by assumption) ha)
    · exact aiOn_nil ρ
  have h₂ : AIOn Q ρ (if fvIn K b then invVars a else []) := by
    split
    · exact aiOn_invVars ha (ai_eval_on H hD hxb hK (by assumption) hb)
    · exact aiOn_nil ρ
  exact aiOn_append h₁ h₂

theorem aiPremStep_mem (H : Hyps Q gr gd env) {ρ : VarEnv} {K : List IL.Id} {a b : Exp}
    (hD : DefsG gd ρ) (hxb : xExp gr gd b = true) (hK : AIOn Q ρ K)
    (h : EvalExp env ρ (.memE a b) (.bool true)) :
    AIOn Q ρ (if fvIn K b then invVars a else []) := by
  obtain ⟨va, vb, ha, hb, himp⟩ := evalExp_memE_true_ai (Q := Q) h
  split
  · exact aiOn_invVars ha (himp (ai_eval_on H hD hxb hK (by assumption) hb))
  · exact aiOn_nil ρ

theorem aiPremStep_let (H : Hyps Q gr gd env) {ρ : VarEnv} {K : List IL.Id} {a b : Exp}
    (hD : DefsG gd ρ) (hxb : xExp gr gd b = true) (hK : AIOn Q ρ K)
    (h : ∃ w, EvalExp env ρ b w ∧ EvalExp env ρ a w) :
    AIOn Q ρ (if fvIn K b then invVars a else []) := by
  obtain ⟨w, hb, ha⟩ := h
  split
  · exact aiOn_invVars ha (ai_eval_on H hD hxb hK (by assumption) hb)
  · exact aiOn_nil ρ

theorem aiPremStep_rule (H : Hyps Q gr gd env) {ρ : VarEnv} {K : List IL.Id} {a : Exp}
    {rest : List Exp} (hD : DefsG gd ρ) (hxa : xExp gr gd a = true) (hK : AIOn Q ρ K)
    (h : ∃ w, EvalExp env ρ (.tupE (a :: rest)) w ∧ (InAI Q w → AllIn Q w)) :
    AIOn Q ρ (if fvIn K a then invVarsL (a :: rest) else []) := by
  obtain ⟨w, he, himp⟩ := h
  split
  · rename_i hfv
    obtain ⟨va, vs, rfl, ha⟩ := evalExp_tupE_cons he
    have hva : AllIn Q va := ai_eval_on H hD hxa hK hfv ha
    have hin : InAI Q (.tuple (va :: vs)) := fun a' r' heq => by
      cases heq; exact hva
    exact aiOn_invVars (e := .tupE (a :: rest)) he (himp hin)
  · exact aiOn_nil ρ

/-- **One premise that holds adds only swap-set variables.** -/
theorem aiOn_premStep (H : Hyps Q gr gd env) {ρ : VarEnv} {K : List IL.Id} {pr : Prem}
    (hD : DefsG gd ρ) (hx : xPrem gr gd pr = true) (hK : AIOn Q ρ K)
    (hf : PremFactQ Q env ρ pr) : AIOn Q ρ (premStep K pr) := by
  unfold premStep
  split
  · simp only [xPrem, xExp, Bool.and_eq_true] at hx
    exact aiPremStep_cmp H hD hx.1 hx.2 hK hf
  · simp only [xPrem, xExp, Bool.and_eq_true] at hx
    exact aiPremStep_mem H hD hx.2 hK hf
  · simp only [xPrem, Bool.and_eq_true] at hx
    exact aiPremStep_let H hD hx.2 hK hf
  · simp only [xPrem, xExp, xExps, Bool.and_eq_true] at hx
    exact aiPremStep_rule H hD hx.2.1 hK hf
  · exact aiOn_nil ρ

/-- **Every round of the mode check adds only swap-set variables.** -/
theorem aiOn_modeK (H : Hyps Q gr gd env) {ρ : VarEnv} {prems : List Prem} (hD : DefsG gd ρ)
    (hx : ∀ pr ∈ prems, xPrem gr gd pr = true) (hf : ∀ pr ∈ prems, PremFactQ Q env ρ pr) :
    ∀ n K, AIOn Q ρ K → AIOn Q ρ (modeK prems n K)
  | 0, K, hK => hK
  | n + 1, K, hK => by
    have hstep : AIOn Q ρ (prems.flatMap (premStep K)) := fun x hx' => by
      obtain ⟨pr, hpr, hx''⟩ := List.mem_flatMap.1 hx'
      exact aiOn_premStep H hD (hx pr hpr) hK (hf pr hpr) x hx''
    exact aiOn_modeK H hD hx hf n _ (aiOn_append hK hstep)
end

/-! ## The starting set -/

theorem aiOn_quantsA {B : Builtins} {ρ : VarEnv} {qs : List Param} (hT : TypsOk tyA ρ)
    (hq : QuantsOk (utf8Env B) ρ qs) : AIOn Q ρ (quantsA qs) := by
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
      exact allIn_of_nxB Q w (nx_of_hasTyp_A B hT ht hty)
    · cases hqx
  | _ => simp at hqx

theorem aiOn_concl {env : Env} {ρ : VarEnv} {e' : Exp} {v : Value} (he : EvalExp env ρ e' v)
    (hin : InAI Q v) : AIOn Q ρ (conclIn e') := by
  cases e' <;> try exact aiOn_nil ρ
  rename_i es
  cases es with
  | nil => exact aiOn_nil ρ
  | cons a rest =>
    obtain ⟨va, vs, hv, ha⟩ := evalExp_tupE_cons he
    exact aiOn_invVars ha (hin va vs hv)

/-- **Every variable the mode check knows is bound to a swap-set value.** -/
theorem aiOn_ruleK {B : Builtins} {gr gd : String → Bool} (H : Hyps Q gr gd (utf8Env B))
    {ρ : VarEnv} {qs : List Param} {e' : Exp} {prems : List Prem} {v : Value}
    (hD : DefsG gd ρ) (hT : TypsOk tyA ρ) (hq : QuantsOk (utf8Env B) ρ qs)
    (he : EvalExp (utf8Env B) ρ e' v) (hin : InAI Q v)
    (hx : ∀ pr ∈ prems, xPrem gr gd pr = true)
    (hf : ∀ pr ∈ prems, PremFactQ Q (utf8Env B) ρ pr) : AIOn Q ρ (ruleK qs e' prems) :=
  aiOn_modeK H hD hx hf 3 _ (aiOn_append (aiOn_quantsA hT hq) (aiOn_concl he hin))

/-! ## Scopes -/

/-- **Binding swap-set rows keeps a scope in the swap set on `K`.** -/
theorem aiOn_bindVals {ρ : VarEnv} {K : List IL.Id} (hK : AIOn Q ρ K)
    {row : List (IL.Id × Value)} (hrow : ∀ p ∈ row, AllIn Q p.2) : AIOn Q (ρ.bindVals row) K := by
  intro x hx w hw
  rcases find?_binds row ρ.vals hw with ⟨p, hp, hpw⟩ | hm
  · exact hpw ▸ hrow p hp
  · exact hK x hx w hm

theorem defsG_bindVals {gd : String → Bool} {ρ : VarEnv} (hD : DefsG gd ρ)
    (row : List (IL.Id × Value)) : DefsG gd (ρ.bindVals row) := hD

/-- **The domains of an iteration over known variables are in the swap set.** -/
theorem ai_evalDoms {gr gd : String → Bool} {env : Env} (H : Hyps Q gr gd env) {ρ : VarEnv}
    {K : List IL.Id} {ds : List Dom} {xvs : List (IL.Id × Value)} (hD : DefsG gd ρ)
    (hx : xDoms gr gd ds = true) (hK : AIOn Q ρ K) (hfv : ∀ d ∈ ds, fvIn K (domSrc d) = true)
    (h : EvalDoms env ρ ds xvs) : ∀ p ∈ xvs, AllIn Q p.2 := by
  obtain ⟨n, hn⟩ := h
  rcases n with _ | n
  · simp [evalDoms] at hn
  intro p hp
  simp only [evalDoms] at hn
  obtain ⟨d, hd, hfd⟩ := mapM_ok_mem hn p hp
  obtain ⟨u, hu, rfl⟩ := Res.map_eq_ok.1 hfd
  exact ai_eval_on H hD (xDoms_mem hx d hd) hK (hfv d hd) ⟨n, hu⟩

theorem ai_domSomes {xvs row : List (IL.Id × Value)} (hx : ∀ p ∈ xvs, AllIn Q p.2)
    (h : domSomes xvs = some row) : ∀ p ∈ row, AllIn Q p.2 := by
  intro p hp
  obtain ⟨q, hq, hqp⟩ := mapM_option_mem h p hp
  have hq2 := hx q hq
  revert hqp hq2
  rcases q with ⟨y, v⟩
  cases v with
  | opt o =>
    cases o with
    | some w =>
      intro hqp hq2
      cases hqp
      exact ai_optSome.1 hq2
    | none => intro hqp; cases hqp
  | _ => intro hqp; cases hqp

theorem ai_rows {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)}
    (hx : ∀ p ∈ xvs, AllIn Q p.2) (h : domLists xvs = some dls) (ido : Option IL.Id) (k : Nat) :
    ∀ r ∈ iterRows dls ido k, ∀ p ∈ r, AllIn Q p.2 :=
  allIn_iterRows (allIn_asLists hx h) ido k

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
