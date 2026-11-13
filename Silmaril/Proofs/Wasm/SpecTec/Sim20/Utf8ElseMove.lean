module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.Utf8Else.Typ

/-!
# `otherwise` moves forward when the earlier rules read back (the `DDerivesB` reading)

Generic in an `EnvExt e₁ e₂ x₀` pair. A step of `e₁` is a step of `e₂` when each `otherwise`
premise it uses holds in `e₂` (`Utf8Mono.sstepB_ext`). This file weakens that hypothesis to the
`otherwise` premises that actually occur, at a point where the rest of their rule holds in `e₁`
(`ElseMonoR`, `sstepB_extR`), and reduces it to a property of pairs of rules (`PairBackU`,
`otherwiseAtB_moveU`).

* `RuleCtxB e x args i v`: rule `i` of `x` has an `otherwise` premise, and its quantifiers and
  one of its conclusion alternatives hold in `e` at `v`.
* **`sstepB_extR`**: under `ElseMonoR e₁ e₂`, every `SStepB e₁` step is an `SStepB e₂` step.
* `PairBackU e₁ e₂ ps args ri rj`: wherever the `otherwise` rule `ri` holds in `e₁` and the earlier
  rule `rj` concludes in `e₂` on the same left-hand side with its quantifiers typed in `e₂`, those
  quantifiers are typed in `e₁`, the conclusion evaluates alike in `e₁`, and each premise of `rj`
  reads back (`PremBack`).
* **`otherwiseAtB_moveU`**: if every `otherwise` rule of `x` is in `PairBackU` with every earlier
  rule, then `otherwiseAtB e₁` implies `otherwiseAtB e₂` under `RuleCtxB e₁`. It is
  `Sim20.ElseAgree.otherwiseAt_move` for the `DDerivesB` reading and an `EnvExt` pair: earlier
  bodies move forward by monotonicity, and an earlier rule's own `otherwise` reads back through
  the rules before it, by strong induction.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Else

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (Interp ElseI PremW QuantsOk RuleBody SameLhs noElse EvalDoms)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (DDerivesB DPremB conclAlts RuleBodyB otherwiseAtB
  otherwiseB SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (hasElseB)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (EnvExt evalExp_ext evalArgs_ext evalDoms_ext
  quantsOk_ext dderivesB_noElse_ext)

variable {e₁ e₂ : Env} {x₀ : String}

/-! ## Steps under the `otherwise` premises that occur -/

/-- **Rule `i` of `x` at `v` apart from its premises**, for a rule with an `otherwise` premise. -/
def RuleCtxB (env : Env) (x : IL.Id) (args : List ArgV) (i : Nat) (v : Value) : Prop :=
  ∃ ps op t rules nm qs e prems ρ₀ σ e', env.findRel? x = some (ps, op, t, rules) ∧
    rules[i]? = some (.ruleD nm qs op e prems) ∧ (∃ pr ∈ prems, hasElseB pr = true) ∧
    e' ∈ conclAlts e ∧ bindParams VarEnv.empty ps args = some ρ₀ ∧
    QuantsOk env (ρ₀.bindVals σ) qs ∧ EvalExp env (ρ₀.bindVals σ) e' v

/-- **The `otherwise` premises of `e₁` that occur hold in `e₂`.** -/
def ElseMonoR (e₁ e₂ : Env) : Prop :=
  ∀ x args i v, RuleCtxB e₁ x args i v → otherwiseB e₁ x args i v → otherwiseB e₂ x args i v

mutual
/-- **A derivation moves from `e₁` to `e₂`** when the `otherwise` premises it uses do. -/
theorem dderivesB_extR (hS : EnvExt e₁ e₂ x₀) (hR : ElseMonoR e₁ e₂) :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value},
      DDerivesB e₁ (otherwiseB e₁) x op args v → DDerivesB e₂ (otherwiseB e₂) x op args v
  | _, _, _, _, .rule hrel hrule halt hps hq he hp =>
      .rule (by rw [hS.rels]; exact hrel) hrule halt hps (quantsOk_ext hS hq)
        (evalExp_ext hS he) fun pr hpr => dpremB_extR hS hR
          (fun hpe h => hR _ _ _ _
            ⟨_, _, _, _, _, _, _, _, _, _, _, hrel, hrule, ⟨pr, hpr, hpe⟩, halt, hps, hq, he⟩ h)
          (hp pr hpr)

/-- `dderivesB_extR` for premises. -/
theorem dpremB_extR (hS : EnvExt e₁ e₂ x₀) (hR : ElseMonoR e₁ e₂) {els els' : Prop} :
    ∀ {ρ : VarEnv} {pr : Prem}, (hasElseB pr = true → els → els') →
      DPremB e₁ (otherwiseB e₁) els ρ pr → DPremB e₂ (otherwiseB e₂) els' ρ pr
  | _, _, _, .ifPr h => .ifPr (evalExp_ext hS h)
  | _, _, hels, .elsePr h => .elsePr (hels rfl h)
  | _, _, _, .letPr h₂ h₁ => .letPr (evalExp_ext hS h₂) (evalExp_ext hS h₁)
  | _, _, _, .rulePr ha he hd =>
      .rulePr (evalArgs_ext hS ha) (evalExp_ext hS he) (dderivesB_extR hS hR hd)
  | _, _, _, .iterOptNone hd hne hall => .iterOptNone (evalDoms_ext hS hd) hne hall
  | _, _, hels, .iterOptSome hd hne hs hp =>
      .iterOptSome (evalDoms_ext hS hd) hne hs (dpremB_extR hS hR hels hp)
  | _, _, hels, .iterList hit hd hne hl hk hp =>
      .iterList hit (evalDoms_ext hS hd) hne hl hk fun r hr => dpremB_extR hS hR hels (hp r hr)
  | _, _, hels, .iterListN hd he hk hl hlen hp =>
      .iterListN (evalDoms_ext hS hd) (evalExp_ext hS he) hk hl hlen fun r hr =>
        dpremB_extR hS hR hels (hp r hr)
end

/-- **A step moves from `e₁` to `e₂` when the `otherwise` premises that occur do.** -/
theorem sstepB_extR (hS : EnvExt e₁ e₂ x₀) (hR : ElseMonoR e₁ e₂) {c c' : Value}
    (h : SStepB e₁ c c') : SStepB e₂ c c' :=
  dderivesB_extR hS hR h

/-! ## Pairs of rules that read back -/

/-- A premise of an earlier rule reads back from `e₂` to `e₁`, given its `otherwise` reading. -/
def PremBack (e₁ e₂ : Env) (ρ : VarEnv) (pr : Prem) : Prop :=
  ∀ els els' : Prop, (hasElseB pr = true → els → els') →
    PremW e₂ (DDerivesB e₂ noElse) els ρ pr → PremW e₁ (DDerivesB e₁ noElse) els' ρ pr

/-- **Rule `rj` reads back from `e₂` to `e₁` against the `otherwise` rule `ri`.** -/
def PairBackU (e₁ e₂ : Env) (ps : List Param) (args : List ArgV) : Rule → Rule → Prop
  | .ruleD _ qsi _ ei _, .ruleD _ qsj _ ej premsj =>
    ∀ ρ₀ σ σ' v w ei' ej', ei' ∈ conclAlts ei → ej' ∈ conclAlts ej →
      bindParams VarEnv.empty ps args = some ρ₀ →
      QuantsOk e₁ (ρ₀.bindVals σ) qsi → EvalExp e₁ (ρ₀.bindVals σ) ei' v →
      EvalExp e₂ (ρ₀.bindVals σ') ej' w → SameLhs v w → QuantsOk e₂ (ρ₀.bindVals σ') qsj →
      QuantsOk e₁ (ρ₀.bindVals σ') qsj ∧ EvalExp e₁ (ρ₀.bindVals σ') ej' w ∧
        ∀ pr ∈ premsj, PremBack e₁ e₂ (ρ₀.bindVals σ') pr

/-- A premise read through `DDerivesB · noElse` moves forward, given its `otherwise` reading. -/
theorem premW_ext (hS : EnvExt e₁ e₂ x₀) {els₁ els₂ : Prop} {ρ : VarEnv} {pr : Prem}
    (h : PremW e₁ (DDerivesB e₁ noElse) els₁ ρ pr) (hel : hasElseB pr = true → els₁ → els₂) :
    PremW e₂ (DDerivesB e₂ noElse) els₂ ρ pr := by
  induction h with
  | ifPr he => exact .ifPr (evalExp_ext hS he)
  | elsePr h => exact .elsePr (hel rfl h)
  | letPr h₁ h₂ => exact .letPr (evalExp_ext hS h₁) (evalExp_ext hS h₂)
  | rulePr ha he hd =>
    exact .rulePr (evalArgs_ext hS ha) (evalExp_ext hS he) (dderivesB_noElse_ext hS hd)
  | iterOptNone hd hne hall => exact .iterOptNone (evalDoms_ext hS hd) hne hall
  | iterOptSome hd hne hs _ ih => exact .iterOptSome (evalDoms_ext hS hd) hne hs (ih hel)
  | iterList hit hd hne hdl hlen _ ih =>
    exact .iterList hit (evalDoms_ext hS hd) hne hdl hlen fun r hr => ih r hr hel
  | iterListN hd hn hk hdl hlen _ ih =>
    exact .iterListN (evalDoms_ext hS hd) (evalExp_ext hS hn) hk hdl hlen fun r hr => ih r hr hel

/-- `otherwiseAtB`, unfolded once. -/
theorem otherwiseAtB_unfold' {env : Env} {x : IL.Id} {args : List ArgV} {i : Nat} {v : Value} :
    otherwiseAtB env x args i v ↔ ∀ j, j < i → ∀ ps op t rules r,
      env.findRel? x = some (ps, op, t, rules) → rules[j]? = some r → ∀ w, SameLhs v w →
      ¬ RuleBodyB env (DDerivesB env noElse) (otherwiseAtB env x args j w) ps args op r w := by
  rw [otherwiseAtB]

/-- A body of an earlier rule moves forward, given that its own `otherwise` does. -/
theorem bodyB_fwd (hS : EnvExt e₁ e₂ x₀) {x : IL.Id} {args : List ArgV} {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {j : Nat} {r : Rule} {w : Value}
    (hrel : e₁.findRel? x = some (ps, op, t, rules)) (hr : rules[j]? = some r)
    (ih : RuleCtxB e₁ x args j w → otherwiseAtB e₁ x args j w → otherwiseAtB e₂ x args j w)
    (h : RuleBodyB e₁ (DDerivesB e₁ noElse) (otherwiseAtB e₁ x args j w) ps args op r w) :
    RuleBodyB e₂ (DDerivesB e₂ noElse) (otherwiseAtB e₂ x args j w) ps args op r w := by
  rcases r with ⟨nm, qs, op', e, prems⟩
  obtain ⟨e', he', rfl, ρ₀, σ, hps, hq, he, hp⟩ := h
  refine ⟨e', he', rfl, ρ₀, σ, hps, quantsOk_ext hS hq, evalExp_ext hS he, fun pr hm => ?_⟩
  refine premW_ext hS (hp pr hm) fun hpe h₁ => ih ?_ h₁
  exact ⟨ps, op', t, rules, nm, qs, e, prems, ρ₀, σ, e', hrel, hr, ⟨pr, hm, hpe⟩, he', hps, hq, he⟩

/-- The `otherwise` of an earlier rule `j` reads back, through the rules before it, which move
forward. -/
theorem elseB_back (hS : EnvExt e₁ e₂ x₀) {x : IL.Id} {args : List ArgV} {j : Nat} {w : Value}
    (ih : ∀ j' < j, ∀ w', RuleCtxB e₁ x args j' w' → otherwiseAtB e₁ x args j' w' →
      otherwiseAtB e₂ x args j' w')
    (h₂ : otherwiseAtB e₂ x args j w) : otherwiseAtB e₁ x args j w := by
  refine otherwiseAtB_unfold'.2 fun j' hj' ps op t rules r hrel hr w' hsame hb => ?_
  have hrel₂ : e₂.findRel? x = some (ps, op, t, rules) := (hS.rels x).trans hrel
  exact otherwiseAtB_unfold'.1 h₂ j' hj' ps op t rules r hrel₂ hr w' hsame
    (bodyB_fwd hS hrel hr (ih j' hj' w') hb)

/-- **A body of an earlier rule `j` reads back from `e₂` to `e₁`**, against an `otherwise` rule
`i` whose rest holds in `e₁` on the same left-hand side. -/
theorem bodyB_back (hS : EnvExt e₁ e₂ x₀) {x : IL.Id} {args : List ArgV} {ps : List Param}
    {op : MixopS} {nmi : IL.Id} {qsi : List Param} {opi : MixopS} {ei ei' : Exp}
    {premsi : List Prem} {r : Rule} {j : Nat} {v w : Value} {ρ₀ : VarEnv}
    {σ : List (IL.Id × Value)}
    (hpair : PairBackU e₁ e₂ ps args (.ruleD nmi qsi opi ei premsi) r)
    (hei' : ei' ∈ conclAlts ei) (hps : bindParams VarEnv.empty ps args = some ρ₀)
    (hq : QuantsOk e₁ (ρ₀.bindVals σ) qsi) (he : EvalExp e₁ (ρ₀.bindVals σ) ei' v)
    (hsame : SameLhs v w)
    (ih : ∀ j' < j, ∀ w', RuleCtxB e₁ x args j' w' → otherwiseAtB e₁ x args j' w' →
      otherwiseAtB e₂ x args j' w')
    (hb : RuleBodyB e₂ (DDerivesB e₂ noElse) (otherwiseAtB e₂ x args j w) ps args op r w) :
    RuleBodyB e₁ (DDerivesB e₁ noElse) (otherwiseAtB e₁ x args j w) ps args op r w := by
  rcases r with ⟨nmj, qsj, opj, ej, premsj⟩
  obtain ⟨ej', hej', hopj, ρ₀', σ', hps', hq', he', hpr'⟩ := hb
  have e₀ : ρ₀' = ρ₀ := Option.some.inj (hps'.symm.trans hps)
  rw [e₀] at hq' he' hpr'
  obtain ⟨hq₁, he₁, hpb⟩ := hpair ρ₀ σ σ' v w ei' ej' hei' hej' hps hq he he' hsame hq'
  refine ⟨ej', hej', hopj, ρ₀, σ', hps, hq₁, he₁, fun pr hm => ?_⟩
  exact hpb pr hm _ _ (fun _ h₂ => elseB_back hS ih h₂) (hpr' pr hm)

/-- A rule with an `otherwise` premise. -/
def RuleHasElseB : Rule → Prop
  | .ruleD _ _ _ _ prems => ∃ pr ∈ prems, hasElseB pr = true

/-- **`otherwise` moves from `e₁` to `e₂`** under `RuleCtxB e₁`, when every `otherwise` rule reads
its earlier rules back (`PairBackU`). -/
theorem otherwiseAtB_moveU (hS : EnvExt e₁ e₂ x₀) {x : IL.Id} {ps : List Param} {op : MixopS}
    {t : Typ} {rules : List Rule} {args : List ArgV}
    (hrel : e₁.findRel? x = some (ps, op, t, rules))
    (hP : ∀ (i j : Nat) ri rj, j < i → rules[i]? = some ri → rules[j]? = some rj →
      RuleHasElseB ri → PairBackU e₁ e₂ ps args ri rj) :
    ∀ i v, RuleCtxB e₁ x args i v → otherwiseAtB e₁ x args i v → otherwiseAtB e₂ x args i v := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro v hC hO
  obtain ⟨ps₁, op₁, t₁, rules₁, nm, qs, e, prems, ρ₀, σ, e', hrel₁, hri, hel, he', hps, hq, he⟩ :=
    hC
  have h₁ : ps = ps₁ ∧ op = op₁ ∧ t = t₁ ∧ rules = rules₁ := by
    simpa [hrel] using hrel₁
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h₁
  refine otherwiseAtB_unfold'.2 fun j hj ps' op' t' rules' r hrel₂ hr w hsame hb => ?_
  have h₂ : ps = ps' ∧ op = op' ∧ t = t' ∧ rules = rules' := by
    simpa [hS.rels x, hrel] using hrel₂
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h₂
  refine otherwiseAtB_unfold'.1 hO j hj ps op t rules r hrel hr w hsame ?_
  exact bodyB_back hS (hP i j _ _ hj hri hr hel) he' hps hq he hsame
    (fun j' hj' => ih j' (by omega)) hb

end Silmaril.Wasm.SpecTec.Sim20.Utf8Else
