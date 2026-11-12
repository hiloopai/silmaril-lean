module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VInv.Defs

/-!
# Round 7, memory SIMD: the backend whole step moves across `withVBytes` under a `StepInvB`
(unrefined)

`dderivesBQ`: a `DDerivesB env (otherwiseB env)` derivation of a `GoodRel` relation, or of `Step`
or `Step_read` at a value satisfying a `StepInvB` predicate `Q`, moves from `B₁` to `B₂`. It is
`VDecl.dderivesQ` (`Raw/…/Round7/VDecl/Step.lean`) for the backend reading: each rule fires at
one of its conclusion alternatives (`conclAlts`), the `otherwise` premises are read by
`otherwiseB`, and the `GoodRel` premises move by `VDecl.dpremB_agree`.

* `Step_read` at a `Q` value: rule 43 is excluded by `StepInvB.read43`; every other rule is a
  `GoodRule`, whose `otherwise` premise moves by `VDecl.otherwiseAtB_read` (its conclusion
  alternative ends in an atom other than `VLOAD`, `VDecl.read_else_altAtom`);
* `Step` at a `Q` value: rule 23 is excluded by `StepInvB.step23`; the context rules 1–5 move
  premise by premise (`dpremBQ`), their `Step` and `Step_read` premises by recursion with `Q` from
  `StepInvB.ctx`; every other rule is a `GoodRule`. `Step` has no `otherwise`.

Kept unrefined, like `VDecl`'s `Step.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VInv

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script (evRefs evExp evArgs evPrem evPrems evRule stepReach)
open Round7.VAgree (GoodEvs GoodRel GoodRule DefsOk ArgOk AgreeOff agreeOff_symm
  defsOk_bindVals goodEvs_append goodEvs_prems evalExp_iff evalArgs_iff findRel?_simEnv)
open Round6.Reading (DDerivesB DPremB RuleBodyB otherwiseB otherwiseAtB conclAlts SStepB SReadB)
open VDecl (TypsG ctxPremOk elseFree relFacts_of_find bindParams_nil scope_ok quantsOk_iff
  quant_rg alt_rg goodEvs_of_rg ctxPrem_split goodEvs_of_ctxPremOk goodEvs_rulePr
  goodEvs_prems_of_rule read_mem_stepReach step_elseFree ctxPremOk_of mem_elseFreeIdx
  lhsAtom_of_eval otherwiseAtB_read otherwiseAtB_goodRel dderivesB_otherwise
  dpremB_agree)

variable {B₁ B₂ : Builtins}

/-- The derivations `dderivesBQ` covers: a `GoodRel` relation, or `Step`/`Step_read` at a `Q`
value. -/
def CovB (Q : Value → Prop) (x : IL.Id) (v : Value) : Prop :=
  GoodRel x ∨ ((x = "Step" ∨ x = "Step_read") ∧ Q v)

/-- `VDecl.read_else_altAtom` at any parameters and operator. -/
theorem readElseAlt {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {i : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e e' : Exp} {prems : List Prem}
    (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hr : rules[i]? = some (.ruleD nm qs op' e prems)) (hmem : i ∈ VDecl.elseFreeIdx rules)
    (hi : 43 < i) (he' : e' ∈ conclAlts e) :
    ∃ b, VElse.ruleAtom (.ruleD nm qs op' e' prems) = some b ∧ b ≠ "VLOAD" := by
  have hok := VDecl.elseAltsOk_read hrel
  simp only [VDecl.elseAltsOk, Bool.and_eq_true, List.all_eq_true] at hok
  have hj := hok.2 i hmem
  simp only [Bool.or_eq_true, decide_eq_true_eq, hr] at hj
  rcases hj with hj | hj
  · omega
  · split at hj
    · rename_i b _
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hj
      exact ⟨b, VDecl.altAtom hj.2 he', hj.1⟩
    · cases hj

section StepB

set_option linter.unusedSectionVars false

variable (hB : AgreeOff B₁ B₂) {Q : Value → Prop} (hQ : StepInvB Q)
include hB hQ

/-- The backend `otherwise` reading of `GoodRel` relations, as `dpremB_agree` takes it. -/
theorem hOB_goodRel : ∀ x args i v, GoodRel x →
    otherwiseB (simEnv B₁) x args i v → otherwiseB (simEnv B₂) x args i v :=
  fun _ args i w hy => otherwiseAtB_goodRel hB hy args i w

/-- A `Step_read` rule's backend `otherwise` premise moves, at a value one of its conclusion
alternatives evaluates to. -/
theorem readElseB {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {nm : IL.Id} {qs : List Param} {op' : MixopS} {e e' : Exp} {prems : List Prem} {ρ : VarEnv}
    {v : Value} {args : List ArgV}
    (hrel : (simEnv B₁).findRel? "Step_read" = some (ps, op, t, rules))
    (hr : rules[i]? = some (.ruleD nm qs op' e prems)) (halt : e' ∈ conclAlts e)
    (he : EvalExp (simEnv B₁) ρ e' v) (hf : prems.all elseFree = false) :
    otherwiseB (simEnv B₁) "Step_read" args i v → otherwiseB (simEnv B₂) "Step_read" args i v := by
  refine otherwiseAtB_read hB args ?_
  by_cases hle : i ≤ 43
  · exact .inl hle
  · obtain ⟨b, hb, hne⟩ := readElseAlt hrel hr (mem_elseFreeIdx hr hf) (by omega) halt
    exact .inr (by rw [lhsAtom_of_eval hb he]; exact fun h => hne (Option.some.inj h))

/- The equation compiler needs more than the default recursion depth for `dpremBQ`'s match. -/
set_option maxRecDepth 4000 in
mutual
/-- **A covered backend derivation moves from `B₁` to `B₂`.** -/
theorem dderivesBQ :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, CovB Q x v →
      DDerivesB (simEnv B₁) (otherwiseB (simEnv B₁)) x op args v →
      DDerivesB (simEnv B₂) (otherwiseB (simEnv B₂)) x op args v
  | x, op, args, v, hx, .rule (σ := σ) (ρ₀ := ρ₀) (i := i) (qs := qs) (e := e) (e' := e')
      (prems := prems) (rules := rules) (ps := ps) (nm := nm) (t := t)
      hrel hrule halt hps hq he hp => by
    rcases hx with hg | ⟨hxs, hv⟩
    · exact dderivesB_otherwise hB hg (.rule hrel hrule halt hps hq he hp)
    have hreach : (0, x) ∈ stepReach := by
      rcases hxs with h | h
      · rw [h]; exact Round7.Script.step_mem_stepReach
      · rw [h]; exact read_mem_stepReach
    have hF := relFacts_of_find hrel hreach
    have hr : Rule.ruleD nm qs op e prems ∈ rules := List.mem_of_getElem? hrule
    have hRF := hF.2 _ hr
    have hps0 : ps = [] := hF.1
    have hps' := hps
    rw [hps0] at hps'
    have hρ : ρ₀ = VarEnv.empty := (bindParams_nil hps').2
    have hs : DefsOk (ρ₀.bindVals σ) ∧ TypsG (ρ₀.bindVals σ) := hρ ▸ scope_ok σ
    have hrel₂ := (findRel?_simEnv B₂ B₁ x).trans hrel
    have hq₂ := (quantsOk_iff hB hs.1 hs.2 (quant_rg hRF)).1 hq
    have he₂ := (evalExp_iff hB hs.1 (goodEvs_of_rg (alt_rg hRF e' halt))).1 he
    have hbody : RuleBodyB (simEnv B₁) (DDerivesB (simEnv B₁) (otherwiseB (simEnv B₁)))
        (otherwiseB (simEnv B₁) x args i v) ps args op (.ruleD nm qs op e prems) v :=
      ⟨e', halt, rfl, ρ₀, σ, hps, hq, he, fun pr hpr => Round6.Reading.dpremB_toPremW (hp pr hpr)⟩
    rcases hxs with hx | hx
    · -- `Step`
      have hrelS : (simEnv B₁).findRel? "Step" = some (ps, op, t, rules) := hx ▸ hrel
      have hnoElse := step_elseFree hrelS hrule
      have hels : ∀ pr ∈ prems, elseFree pr = false →
          otherwiseB (simEnv B₁) x args i v → otherwiseB (simEnv B₂) x args i v :=
        fun pr hpr hf => absurd (List.all_eq_true.1 hnoElse pr hpr) (by simp [hf])
      by_cases h23 : i = 23
      · exact absurd hbody (hQ.step23 B₁ _ _ ps op t rules _ args op v hv hrelS (h23 ▸ hrule))
      by_cases hctx : i ∈ [1, 2, 3, 4, 5]
      · refine .rule hrel₂ hrule halt hps hq₂ he₂ fun pr hpr => ?_
        exact dpremBQ hs.1 (ctxPremOk_of hrelS hctx hrule pr hpr)
          (fun y ags op'' e'' w hpe hy hw => hQ.ctx B₁ ps op t rules i nm qs op e e' prems _ v y
            ags op'' e'' w hrelS hctx hrule halt he hv (hpe ▸ hpr) hy hw)
          (hels pr hpr) (hp pr hpr)
      · have hi : i ∉ [1, 2, 3, 4, 5, 23] := by
          intro hm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm hctx
          omega
        have hG : GoodEvs (evRule _) := VAgree.goodRule_step hi B₁ _ _ hrelS hrule
        refine .rule hrel₂ hrule halt hps hq₂ he₂ fun pr hpr => ?_
        exact dpremB_agree hB (hOB_goodRel hB hQ) hs.1
          (goodEvs_prems (goodEvs_prems_of_rule hG) pr hpr) (hels pr hpr) (hp pr hpr)
    · -- `Step_read`
      have hrelR : (simEnv B₁).findRel? "Step_read" = some (ps, op, t, rules) := hx ▸ hrel
      have h43 : i ≠ 43 := fun h =>
        hQ.read43 B₁ _ _ ps op t rules _ args op v hv hrelR (h ▸ hrule) hbody
      have hG : GoodEvs (evRule _) := VAgree.goodRule_read h43 B₁ _ _ hrelR hrule
      have hels : ∀ pr ∈ prems, elseFree pr = false →
          otherwiseB (simEnv B₁) x args i v → otherwiseB (simEnv B₂) x args i v := by
        intro pr hpr hf
        have hf' : prems.all elseFree = false :=
          List.all_eq_false.2 ⟨pr, hpr, by simp [hf]⟩
        subst hx
        exact readElseB hB hQ hrelR hrule halt he hf'
      refine .rule hrel₂ hrule halt hps hq₂ he₂ fun pr hpr => ?_
      exact dpremB_agree hB (hOB_goodRel hB hQ) hs.1
        (goodEvs_prems (goodEvs_prems_of_rule hG) pr hpr) (hels pr hpr) (hp pr hpr)
termination_by structural _ _ _ _ _ hd => hd

/-- **A backend premise of a context rule moves from `B₁` to `B₂`**, its `Step` and `Step_read`
calls at `Q` values. -/
theorem dpremBQ :
    ∀ {els₁ els₂ : Prop} {ρ : VarEnv} {pr : Prem}, DefsOk ρ → ctxPremOk pr = true →
      (∀ y args op e' w, pr = .rulePr y args op e' → (y = "Step" ∨ y = "Step_read") →
        EvalExp (simEnv B₁) ρ e' w → Q w) →
      (elseFree pr = false → els₁ → els₂) →
      DPremB (simEnv B₁) (otherwiseB (simEnv B₁)) els₁ ρ pr →
      DPremB (simEnv B₂) (otherwiseB (simEnv B₂)) els₂ ρ pr
  | _, _, _, .rulePr y args op e', hρ, hok, hQw, _, .rulePr ha he hd => by
    rcases ctxPrem_split hok with ⟨hy, hga, hge⟩ | hg
    · exact .rulePr ((evalArgs_iff hB hρ hga).1 ha) ((evalExp_iff hB hρ hge).1 he)
        (dderivesBQ (.inr ⟨hy, hQw y args op e' _ rfl hy he⟩) hd)
    · obtain ⟨hx, hga, hge⟩ := goodEvs_rulePr hg
      exact .rulePr ((evalArgs_iff hB hρ hga).1 ha) ((evalExp_iff hB hρ hge).1 he)
        (dderivesBQ (.inl hx) hd)
  | _, _, _, _, hρ, hok, _, hels, .ifPr h =>
    dpremB_agree hB (hOB_goodRel hB hQ) hρ (goodEvs_of_ctxPremOk hok (by intros; simp)) hels
      (.ifPr h)
  | _, _, _, _, hρ, hok, _, hels, .elsePr h =>
    dpremB_agree hB (hOB_goodRel hB hQ) hρ (goodEvs_of_ctxPremOk hok (by intros; simp)) hels
      (.elsePr h)
  | _, _, _, _, hρ, hok, _, hels, .letPr h₂ h₁ =>
    dpremB_agree hB (hOB_goodRel hB hQ) hρ (goodEvs_of_ctxPremOk hok (by intros; simp)) hels
      (.letPr h₂ h₁)
  | _, _, _, _, hρ, hok, _, hels, .iterOptNone hd hne hall =>
    dpremB_agree hB (hOB_goodRel hB hQ) hρ (goodEvs_of_ctxPremOk hok (by intros; simp)) hels
      (.iterOptNone hd hne hall)
  | _, _, _, _, hρ, hok, _, hels, .iterOptSome hd hne hs hp =>
    dpremB_agree hB (hOB_goodRel hB hQ) hρ (goodEvs_of_ctxPremOk hok (by intros; simp)) hels
      (.iterOptSome hd hne hs hp)
  | _, _, _, _, hρ, hok, _, hels, .iterList hit hd hne hl hlen hp =>
    dpremB_agree hB (hOB_goodRel hB hQ) hρ (goodEvs_of_ctxPremOk hok (by intros; simp)) hels
      (.iterList hit hd hne hl hlen hp)
  | _, _, _, _, hρ, hok, _, hels, .iterListN hd he hk hl hlen hp =>
    dpremB_agree hB (hOB_goodRel hB hQ) hρ (goodEvs_of_ctxPremOk hok (by intros; simp)) hels
      (.iterListN hd he hk hl hlen hp)
termination_by structural _ _ _ _ _ _ _ _ hd => hd
end

/-- **The backend whole step moves from `B₁` to `B₂` at a `Q` value.** -/
theorem sstepB_agree {c c' : Value} (hq : Q (.tuple [c, c'])) (h : SStepB (simEnv B₁) c c') :
    SStepB (simEnv B₂) c c' :=
  dderivesBQ hB hQ (.inr ⟨.inl rfl, hq⟩) h

/-- **Backend `Step_read` moves from `B₁` to `B₂` at a `Q` value.** -/
theorem sreadB_agree {c : Value} {js : List Value} (hq : Q (.tuple [c, .list js]))
    (h : SReadB (simEnv B₁) c js) : SReadB (simEnv B₂) c js :=
  dderivesBQ hB hQ (.inr ⟨.inr rfl, hq⟩) h

end StepB

/-- **Under a `StepInvB` predicate, the backend whole step reads alike at `withVBytes B` and at
`B`.** -/
theorem sstepB_withVBytes_iff (B : Builtins) {Q : Value → Prop} (hQ : StepInvB Q) {c c' : Value}
    (hq : Q (.tuple [c, c'])) :
    SStepB (simEnv (MemSimd.withVBytes B)) c c' ↔ SStepB (simEnv B) c c' :=
  ⟨sstepB_agree (VAgree.agreeOff_withVBytes B) hQ hq,
    sstepB_agree (agreeOff_symm (VAgree.agreeOff_withVBytes B)) hQ hq⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.VInv
