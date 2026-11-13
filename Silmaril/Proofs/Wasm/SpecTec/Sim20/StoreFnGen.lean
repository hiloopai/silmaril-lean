module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreDeepRules

/-!
# Firing a relation-free rule in `simEnv20T` from its body evaluated in `simEnv20`

Once the store's functions may hold stores, the state is typed in `simEnv20T` only, so round 3's
firings in `simEnv20` (which check the quantifier `z : state` there) no longer apply. What does
apply is everything else they prove: the conclusion and the premises *evaluate* in `simEnv20`
whatever the typing. `firesT_of_parts` puts a firing of `simEnv20T` together from

* the quantifiers, typed in `simEnv20T`;
* the conclusion and the premises, evaluated in `simEnv20`, moved by relation-freeness
  (`RelFree.evalExp_withRels`, `RelFree.premW_withRels_gen`) to `simEnv20S` and from there to
  `simEnv20T`, which share every definition (`StoreAgree.evalExp_of`, `StoreAgree.premW_of_plain`).

The rule must be relation-free and its premises plain without `otherwise` (both checked by
`decide` at each use). This is the route `StoreDeep.firesT_block` takes, made generic.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreFn

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim (TypedV PremW QuantsOk ValsOnly Fires DDerives otherwise stateT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evRule evExp evPrems evParams)

set_option maxRecDepth 100000

variable {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-- A premise that is plain and has no `otherwise`. -/
def premOkB (p : Prem) : Bool := StoreAgree.plainB p && RelFree.noElseB p

/-- The definitions bound by a scope of values are harmless. -/
theorem defsOk_of_valsOnly {ρ : VarEnv} (hρ : ValsOnly ρ) : RelFree.DefsOk RelFree.bad20 ρ :=
  fun p hp => by
    rw [hρ.2.1] at hp
    cases hp

/-- **A relation-free rule of `simEnv20T` fires** from quantifiers typed in `simEnv20T` and its
conclusion and premises evaluated in `simEnv20`. -/
theorem firesT_of_parts {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param} {e : Exp}
    {prems : List Prem} (hT : HasRuleAt (simEnv20T B) x "%~>%" k (.ruleD nm qs "%~>%" e prems))
    (hG : (evRule (.ruleD nm qs "%~>%" e prems)).all (RelFree.rfEvB RelFree.bad20) = true)
    (hpl : prems.all premOkB = true) (σ : List (IL.Id × Value)) {v : Value}
    {D : Sim.Interp} {els : Prop}
    (hq : QuantsOk (simEnv20T B) (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp (E20 B) (VarEnv.empty.bindVals σ) e v)
    (hp : ∀ pr ∈ prems, PremW (E20 B) D els (VarEnv.empty.bindVals σ) pr) :
    Fires (simEnv20T B) x k v := by
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hD := defsOk_of_valsOnly hρ
  have hG' : (RelFree.GoodEvs RelFree.bad20 (evParams qs) ∧
      RelFree.GoodEvs RelFree.bad20 (evExp e)) ∧ RelFree.GoodEvs RelFree.bad20 (evPrems prems) := by
    simpa only [evRule, RelFree.goodEvs_append] using RelFree.goodEvs_of_all hG
  refine Pure.fires_of_ruleAt hT σ hq (StoreDeep.evalT_of_20 hρ hG'.1.2 he) fun pr hpr => ?_
  have hok : StoreAgree.plainB pr = true ∧ RelFree.noElseB pr = true := by
    simpa [premOkB] using List.all_eq_true.1 hpl pr hpr
  have hS : PremW (StepFix.simEnv20S B) D els (VarEnv.empty.bindVals σ) pr := by
    rw [RelFree.simEnv20S_eq B]
    exact RelFree.premW_withRels_gen (RelFree.defsGood_simEnv20 B) (hp pr hpr) hD
      (RelFree.goodEvs_prems hG'.2 pr hpr) (.inl hok.2)
  exact StoreAgree.premW_of_plain (StoreAgree.envSame20T B) hS hok.1

/-- A typing of `simEnv20` of a relation-free type, moved to `simEnv20T`. -/
theorem typedT {t : Typ} {v : Value}
    (ht : (Sim.Round7.Script.evTyp t).all (RelFree.rfEvB RelFree.bad20) = true)
    (h : TypedV (E20 B) t v) : TypedV (simEnv20T B) t v :=
  StoreDeep.typedV_toT ht h

/-- A `Step_read` firing of `simEnv20T`, as a step of `simEnv20T`. -/
theorem sstepT_read {k : Nat} {z : Value} {is js : List Value}
    (hz : TypedV (simEnv20T B) stateT z) (his : TypedV (simEnv20T B) StepFix.adminsTy (.list is))
    (hjs : TypedV (simEnv20T B) StepFix.adminsTy (.list js))
    (h : Fires (simEnv20T B) "Step_read" k (.tuple [Sim.cfgV z is, .list js])) :
    SStepB (simEnv20T B) (Sim.cfgV z is) (Sim.cfgV z js) :=
  StoreDeep.sstepT_of_firesRead hz his hjs h

/-! ## `Step_read` and `Step` rules, from their place in `simEnv20` -/

/-- `simEnv20T`'s `Step_read` is `simEnv20`'s. -/
theorem hasRuleAtT_read {op : MixopS} {k : Nat} {r : Rule}
    (h : HasRuleAt (E20 B) "Step_read" op k r) : HasRuleAt (simEnv20T B) "Step_read" op k r := by
  obtain ⟨ps, t, rules, hrel, hps, hk⟩ := h
  obtain ⟨t', rules', h₁, h₂, -⟩ := RelFree.readRules20_spec B
  have e := Option.some.inj (h₁.symm.trans hrel)
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  exact ⟨[], t', rules', ((StoreAgree.envSame20T B).rels "Step_read").trans h₂, rfl, hk⟩

/-- Every `Step_read` rule is relation-free. -/
theorem readGood {op : MixopS} {k : Nat} {r : Rule} (h : HasRuleAt (E20 B) "Step_read" op k r) :
    (evRule r).all (RelFree.rfEvB RelFree.bad20) = true := by
  obtain ⟨ps, t, rules, hrel, -, hk⟩ := h
  obtain ⟨t', rules', h₁, -, hok⟩ := RelFree.readRules20_spec B
  have e := Option.some.inj (h₁.symm.trans hrel)
  simp only [Prod.mk.injEq] at e
  obtain ⟨-, -, -, rfl⟩ := e
  exact List.all_eq_true.1 hok r (List.mem_of_getElem? hk)

/-- `simEnv20T`'s `Step` rule `k + 1` is `simEnv20`'s rule `k`, for `k ≥ 4`; it is
relation-free and has no `otherwise`. -/
theorem hasRuleAtT_step {op : MixopS} {k : Nat} {r : Rule} (hk4 : 4 ≤ k)
    (h : HasRuleAt (E20 B) "Step" op k r) :
    HasRuleAt (simEnv20T B) "Step" op (k + 1) r ∧ RelFree.ruleOkB RelFree.bad20 r = true := by
  obtain ⟨ps, t, rules, hrel, hps, hk⟩ := h
  obtain ⟨t', rules', h₁, h₂, hok⟩ := RelFree.stepRules20_spec B
  have e := Option.some.inj (h₁.symm.trans hrel)
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  refine ⟨⟨[], t', _, ((StoreAgree.envSame20T B).rels "Step").trans h₂, rfl,
    (Whole.getElem?_fix_succ _ rfl rules' hk4).trans hk⟩, ?_⟩
  have hd : (rules'.drop 4)[k - 4]? = some r := by
    rw [List.getElem?_drop, show 4 + (k - 4) = k by omega]
    exact hk
  exact List.all_eq_true.1 hok r (List.mem_of_getElem? hd)

/-- **A `Step_read` rule fires in `simEnv20T`** from quantifiers typed there and its body
evaluated in `simEnv20`. -/
theorem firesT_read_of20 {k : Nat} {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem}
    (h : HasRuleAt (E20 B) "Step_read" "%~>%" k (.ruleD nm qs "%~>%" e prems))
    (hpl : prems.all premOkB = true) (σ : List (IL.Id × Value)) {v : Value}
    {D : Sim.Interp} {els : Prop}
    (hq : QuantsOk (simEnv20T B) (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp (E20 B) (VarEnv.empty.bindVals σ) e v)
    (hp : ∀ pr ∈ prems, PremW (E20 B) D els (VarEnv.empty.bindVals σ) pr) :
    Fires (simEnv20T B) "Step_read" k v :=
  firesT_of_parts (hasRuleAtT_read h) (readGood h) hpl σ hq he hp

/-- **A `Step` rule `k ≥ 4` of `simEnv20` fires as rule `k + 1` of `simEnv20T`** from quantifiers
typed there and its body evaluated in `simEnv20`. -/
theorem firesT_step_of20 {k : Nat} (hk4 : 4 ≤ k) {nm : IL.Id} {qs : List Param} {e : Exp}
    {prems : List Prem} (h : HasRuleAt (E20 B) "Step" "%~>%" k (.ruleD nm qs "%~>%" e prems))
    (hpl : prems.all StoreAgree.plainB = true) (σ : List (IL.Id × Value)) {v : Value}
    {D : Sim.Interp} {els : Prop}
    (hq : QuantsOk (simEnv20T B) (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp (E20 B) (VarEnv.empty.bindVals σ) e v)
    (hp : ∀ pr ∈ prems, PremW (E20 B) D els (VarEnv.empty.bindVals σ) pr) :
    Fires (simEnv20T B) "Step" (k + 1) v := by
  obtain ⟨hT, hok⟩ := hasRuleAtT_step hk4 h
  have hok' : (evRule (.ruleD nm qs "%~>%" e prems)).all (RelFree.rfEvB RelFree.bad20) = true ∧
      prems.all RelFree.noElseB = true := by
    simpa only [RelFree.ruleOkB, Bool.and_eq_true] using hok
  refine firesT_of_parts hT hok'.1 ?_ σ hq he hp
  simp only [premOkB, List.all_eq_true, Bool.and_eq_true] at hpl hok' ⊢
  exact fun p hp => ⟨hpl p hp, hok'.2 p hp⟩

/-- **A firing of `simEnv20T`'s `Step` is a step of `simEnv20T`.** -/
theorem sstepT_of_firesStep {k : Nat} {c c' : Value}
    (h : Fires (simEnv20T B) "Step" k (.tuple [c, c'])) : SStepB (simEnv20T B) c c' := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := StoreFix.hasRuleAt_ctxtInstrsFixT B
  exact (StoreFix.sstepB20T_iff B).2 ((Sim.dderives_iff_fires hrel).2 ⟨k, h⟩)

/-- **Quantifiers `z :: qs`, typed in `simEnv20T`**: the state there, the rest moved from a
typing in `simEnv20` of relation-free types. -/
theorem quantsOkT_z {ρ : VarEnv} {Z : Value} {qs : List Param} (hρ : ValsOnly ρ)
    (fz : ρ.findVal? "z" = some Z) (hz : TypedV (simEnv20T B) stateT Z)
    (hG : (evParams qs).all (RelFree.rfEvB RelFree.bad20) = true) (hq : QuantsOk (E20 B) ρ qs) :
    QuantsOk (simEnv20T B) ρ (.expP "z" stateT :: qs) := by
  refine QuantsOk.cons fz (hz ρ hρ) ?_
  have hT : RelFree.TypsOk RelFree.bad20 ρ := fun p hp => by
    rw [hρ.1] at hp
    cases hp
  have hS : QuantsOk (StepFix.simEnv20S B) ρ qs := by
    rw [RelFree.simEnv20S_eq B]
    exact RelFree.quantsOk_withRels (RelFree.defsGood_simEnv20 B) (RelFree.typsGood_simEnv20 B)
      (defsOk_of_valsOnly hρ) hT (RelFree.goodEvs_of_all hG) hq
  exact StoreAgree.quantsOk_of (StoreAgree.envSame20T B) (StoreAgree.typRepair20T B) hS

end Silmaril.Wasm.SpecTec.Sim20.StoreFn
