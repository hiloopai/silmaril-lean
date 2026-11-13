module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreAgreeEnv

/-!
# Derivations move from `simEnv20S` to `simEnv20T`

Generic in two environments `e₁`, `e₂` that the evaluator cannot tell apart (`EnvSame`) and whose
type tables are related by a repair `g` (`TypRepair`):

* `evalExp_of`, `evalArgs_of`, `evalDoms_of`: evaluation agrees (`EvalExp e₁ ↔ EvalExp e₂`);
* `quantsOk_of`, `typedV_of`: typing grows;
* `fires_of_plain`: a firing of a rule whose premises consult no relation and no `otherwise`
  (`plainB`) is a firing in `e₂`;
* `dderives_of`: a declarative derivation in `e₁` is one in `e₂`, provided every `otherwise`
  premise it uses, at a point where the rest of its rule holds in `e₁` (`RuleCtx`), also holds in
  `e₂`. This is the one direction typing does not give for free: `otherwise` is a negation.

At the two 2.0 environments:

* `stepPlain20S` (kernel): the corrected `Step`'s rules 5–22, the original rules 4–21, are plain;
* **`sstepB20T_of_fires20`**: every firing of an original `Step` rule `k ≥ 4` in `simEnv20 B` is
  a step of `simEnv20T B`, with no hypothesis. In particular the four scalar store rules;
* **`sstepB20T_of_sstepB20S`**: every step of `simEnv20S B` is a step of `simEnv20T B`, under
  `ElseAgree20T B` (the `otherwise` premises of `simEnv20S B` hold in `simEnv20T B` where the rest
  of their rule holds). That condition is stated as `Task.elseAgree20T`, not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (Interp ElseI EvalDoms PremW QuantsOk DDerives DPrem RuleBody Fires
  TypedV ValsOnly otherwise SStep)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S)

variable {e₁ e₂ : Env} {g : TypCase → TypCase}

/-! ## Evaluation and typing -/

theorem evalExp_of (hS : EnvSame e₁ e₂) {ρ : VarEnv} {e : Exp} {v : Value}
    (h : EvalExp e₁ ρ e v) : EvalExp e₂ ρ e v :=
  let ⟨n, hn⟩ := h
  ⟨n, (evalExp_eq hS n ρ e).trans hn⟩

theorem evalArgs_of (hS : EnvSame e₁ e₂) {ρ : VarEnv} {xs : List Arg} {ws : List ArgV}
    (h : EvalArgs e₁ ρ xs ws) : EvalArgs e₂ ρ xs ws :=
  let ⟨n, hn⟩ := h
  ⟨n, (evalArgs_eq hS n ρ xs).trans hn⟩

theorem evalDoms_of (hS : EnvSame e₁ e₂) {ρ : VarEnv} {ds : List Dom}
    {xvs : List (IL.Id × Value)} (h : EvalDoms e₁ ρ ds xvs) : EvalDoms e₂ ρ ds xvs :=
  let ⟨n, hn⟩ := h
  ⟨n, (evalDoms_eq hS n ρ ds).trans hn⟩

theorem quantsOk_of (hS : EnvSame e₁ e₂) (hT : TypRepair e₁ e₂ g) {ρ : VarEnv} {qs : List Param}
    (h : QuantsOk e₁ ρ qs) : QuantsOk e₂ ρ qs := fun x t hx =>
  let ⟨w, hw, ht⟩ := h x t hx
  ⟨w, hw, hasTyp_repair hS hT ht⟩

theorem typedV_of (hS : EnvSame e₁ e₂) (hT : TypRepair e₁ e₂ g) {t : Typ} {v : Value}
    (h : TypedV e₁ t v) : TypedV e₂ t v := fun ρ hρ => hasTyp_repair hS hT (h ρ hρ)

/-! ## Plain premises -/

/-- A premise that consults no relation and no `otherwise`. -/
def plainB : Prem → Bool
  | .rulePr _ _ _ _ => false
  | .elsePr => false
  | .iterPr pr _ => plainB pr
  | _ => true

/-- A rule whose premises are all plain. -/
def rulePlainB : Rule → Bool
  | .ruleD _ _ _ _ prems => prems.all plainB

theorem premW_of_plain (hS : EnvSame e₁ e₂) {D₁ D₂ : Interp} {els₁ els₂ : Prop} {ρ : VarEnv}
    {pr : Prem} (h : PremW e₁ D₁ els₁ ρ pr) (hp : plainB pr = true) : PremW e₂ D₂ els₂ ρ pr := by
  induction h with
  | ifPr he => exact .ifPr (evalExp_of hS he)
  | elsePr => simp [plainB] at hp
  | letPr h₁ h₂ => exact .letPr (evalExp_of hS h₁) (evalExp_of hS h₂)
  | rulePr => simp [plainB] at hp
  | iterOptNone hd hne hall => exact .iterOptNone (evalDoms_of hS hd) hne hall
  | iterOptSome hd hne hs _ ih => exact .iterOptSome (evalDoms_of hS hd) hne hs (ih hp)
  | iterList hit hd hne hdl hlen _ ih =>
    exact .iterList hit (evalDoms_of hS hd) hne hdl hlen fun r hr => ih r hr hp
  | iterListN hd hn hk hdl hlen _ ih =>
    exact .iterListN (evalDoms_of hS hd) (evalExp_of hS hn) hk hdl hlen fun r hr => ih r hr hp

/-- **A plain rule fires alike.** -/
theorem fires_of_plain (hS : EnvSame e₁ e₂) (hT : TypRepair e₁ e₂ g) {x : IL.Id} {k : Nat}
    {v : Value}
    (hp : ∀ t rules r, e₁.findRel? x = some ([], "%~>%", t, rules) → rules[k]? = some r →
      rulePlainB r = true)
    (h : Fires e₁ x k v) : Fires e₂ x k v := by
  obtain ⟨t, rules, r, hrel, hr, hb⟩ := h
  refine ⟨t, rules, r, (hS.rels x).trans hrel, hr, ?_⟩
  have hpl := hp t rules r hrel hr
  rcases r with ⟨nm, qs, op, e, prems⟩
  obtain ⟨hop, ρ₀, σ, hps, hq, he, hpr⟩ := hb
  refine ⟨hop, ρ₀, σ, hps, quantsOk_of hS hT hq, evalExp_of hS he, fun pr hm => ?_⟩
  exact premW_of_plain hS (hpr pr hm) (List.all_eq_true.1 hpl pr hm)

/-! ## Declarative derivations -/

/-- A premise that contains an `otherwise`. -/
def hasElseB : Prem → Bool
  | .elsePr => true
  | .iterPr pr _ => hasElseB pr
  | _ => false

/-- The parts of a firing of rule `i` of `x` at `v` other than its premises, for a rule with an
`otherwise` premise. -/
def RuleCtx (env : Env) (x : IL.Id) (args : List ArgV) (i : Nat) (v : Value) : Prop :=
  ∃ ps op t rules nm qs e prems ρ₀ σ, env.findRel? x = some (ps, op, t, rules) ∧
    rules[i]? = some (.ruleD nm qs op e prems) ∧ (∃ pr ∈ prems, hasElseB pr = true) ∧
    bindParams VarEnv.empty ps args = some ρ₀ ∧
    QuantsOk env (ρ₀.bindVals σ) qs ∧ EvalExp env (ρ₀.bindVals σ) e v

mutual
/-- **A derivation moves**, given the `otherwise` premises it uses. -/
theorem dderives_of (hS : EnvSame e₁ e₂) (hT : TypRepair e₁ e₂ g) {O₁ O₂ : ElseI}
    (hO : ∀ x args i v, O₁ x args i v → RuleCtx e₁ x args i v → O₂ x args i v) :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value},
      DDerives e₁ O₁ x op args v → DDerives e₂ O₂ x op args v
  | _, _, _, _, .rule hrel hrule hps hq he hp =>
    .rule ((hS.rels _).trans hrel) hrule hps (quantsOk_of hS hT hq) (evalExp_of hS he)
      fun pr hm => dprem_of hS hT hO
        (fun hpe hel => hO _ _ _ _ hel
          ⟨_, _, _, _, _, _, _, _, _, _, hrel, hrule, ⟨pr, hm, hpe⟩, hps, hq, he⟩)
        (hp pr hm)

/-- A premise moves. -/
theorem dprem_of (hS : EnvSame e₁ e₂) (hT : TypRepair e₁ e₂ g) {O₁ O₂ : ElseI}
    (hO : ∀ x args i v, O₁ x args i v → RuleCtx e₁ x args i v → O₂ x args i v)
    {els₁ els₂ : Prop} :
    ∀ {ρ : VarEnv} {pr : Prem}, (hasElseB pr = true → els₁ → els₂) →
      DPrem e₁ O₁ els₁ ρ pr → DPrem e₂ O₂ els₂ ρ pr
  | _, _, _, .ifPr he => .ifPr (evalExp_of hS he)
  | _, _, hel, .elsePr h => .elsePr (hel rfl h)
  | _, _, _, .letPr h₁ h₂ => .letPr (evalExp_of hS h₁) (evalExp_of hS h₂)
  | _, _, _, .rulePr ha he hd =>
    .rulePr (evalArgs_of hS ha) (evalExp_of hS he) (dderives_of hS hT hO hd)
  | _, _, _, .iterOptNone hd hne hall => .iterOptNone (evalDoms_of hS hd) hne hall
  | _, _, hel, .iterOptSome hd hne hs h =>
    .iterOptSome (evalDoms_of hS hd) hne hs (dprem_of hS hT hO hel h)
  | _, _, hel, .iterList hit hd hne hdl hlen h =>
    .iterList hit (evalDoms_of hS hd) hne hdl hlen fun r hr => dprem_of hS hT hO hel (h r hr)
  | _, _, hel, .iterListN hd hn hk hdl hlen h =>
    .iterListN (evalDoms_of hS hd) (evalExp_of hS hn) hk hdl hlen fun r hr =>
      dprem_of hS hT hO hel (h r hr)
end

/-! ## At the two 2.0 environments -/

set_option maxRecDepth 100000 in
/-- The original `Step` rules 4–21, the corrected rules 5–22, are plain (kernel). -/
theorem stepPlain20S (B : Builtins) : ∃ t rules,
    (simEnv20S B).findRel? "Step" = some ([], "%~>%", t, rules) ∧
      (rules.drop 5).all rulePlainB = true :=
  ⟨_, _, rfl, by decide +kernel⟩

/-- **Every firing of an original `Step` rule `k ≥ 4` is a step of `simEnv20T B`.** -/
theorem sstepB20T_of_fires20 (B : Builtins) {k : Nat} (hk : 4 ≤ k) {c c' : Value}
    (h : Fires (simEnv20 B) "Step" k (.tuple [c, c'])) : SStepB (simEnv20T B) c c' := by
  have hS := Whole.stepAgreeS B k hk _ h
  have hT : Fires (simEnv20T B) "Step" (k + 1) (.tuple [c, c']) := by
    refine fires_of_plain (envSame20T B) (typRepair20T B) (fun t rules r hrel hr => ?_) hS
    obtain ⟨t', rules', hrel', hall⟩ := stepPlain20S B
    rw [hrel'] at hrel
    obtain ⟨-, -, -, rfl⟩ : ([] : List Param) = [] ∧ "%~>%" = "%~>%" ∧ t' = t ∧ rules' = rules := by
      simpa using hrel
    have hd : (rules'.drop 5)[k - 4]? = some r := by
      rw [List.getElem?_drop, show 5 + (k - 4) = k + 1 by omega]
      exact hr
    exact List.all_eq_true.1 hall r (List.mem_of_getElem? hd)
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAt_ctxtInstrsFixT B
  exact (sstepB20T_iff B).2 ((Sim.dderives_iff_fires hrel).2 ⟨k + 1, hT⟩)

/-- **The `otherwise` premises of `simEnv20S B` hold in `simEnv20T B`** where the rest of their
rule holds in `simEnv20S B`. In the 2.0 script seventeen rules have one: `Step_pure`'s
`ref.is_null-false` and `vtestop-false`, and `Step_read`'s `call_indirect-trap` and the `-zero`,
`-succ`, `-le` and `-gt` rules of the bulk table and memory instructions. -/
def ElseAgree20T (B : Builtins) : Prop :=
  ∀ x args i v, otherwise (simEnv20S B) x args i v → RuleCtx (simEnv20S B) x args i v →
    otherwise (simEnv20T B) x args i v

/-- **Open target**: `ElseAgree20T B` at every builtins. Typing grows from `simEnv20S` to
`simEnv20T` (`hasTyp_repair`), so an `otherwise` premise, a negation, does not move by itself:
an earlier rule may fire in `simEnv20T` on a left-hand side where it does not in `simEnv20S`.
For the rules above, the earlier rules that can fire on their left-hand sides quantify values
of the left-hand side, which the `otherwise` rule itself types in `simEnv20S` (references,
vectors, numbers, the state), and numbers computed from them, so the target is expected to hold;
it is not proved here. -/
def Task.elseAgree20T : Prop := ∀ B, ElseAgree20T B

/-- **Every step of `simEnv20S B` is a step of `simEnv20T B`**, under `ElseAgree20T B`. -/
theorem sstepB20T_of_sstepB20S {B : Builtins} (hE : ElseAgree20T B) {c c' : Value}
    (h : SStepB (simEnv20S B) c c') : SStepB (simEnv20T B) c c' :=
  (sstepB20T_iff B).2 (dderives_of (envSame20T B) (typRepair20T B) hE ((StepFix.sstepB20S_iff B).1 h))

end Silmaril.Wasm.SpecTec.Sim20.StoreAgree
