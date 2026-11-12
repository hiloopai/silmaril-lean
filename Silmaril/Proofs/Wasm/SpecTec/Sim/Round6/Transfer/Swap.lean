module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Thms

/-!
# Round 6: swapping the interpretation of one premise

`Step`'s rules 1–5 (`read`, `ctxt-instrs`, `ctxt-label`, `ctxt-handler`, `ctxt-frame`) each have
one relational premise first (`Step_read` or `Step`), followed only by premises that consult no
relation and have no `otherwise` (`TailFree`). Their conclusions have no empty-domain option
iteration, so `DDerivesB` reads them as `DDerives` does. Such a rule fires the same under both
readings as soon as the two readings agree **at the instances of its leading premise**
(`Inst`), not everywhere (`firesB_iff_swap`): this is what lets the transfer go by recursion on
the code, through the context rules, with the readings agreeing only away from cast redexes.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Transfer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Reading

/-- A relation-free premise without `otherwise` holds under any interpretation. -/
theorem premW_tail {env : Env} {D D' : Interp} {els els' : Prop} {ρ : VarEnv} {pr : Prem}
    (hf : premRels pr = [] ∧ noElsePr pr = true) (h : PremW env D els ρ pr) :
    PremW env D' els' ρ pr :=
  premW_imp_noElse (fun _ hy => absurd (hf.1 ▸ hy) List.not_mem_nil) hf.2 h

/-- The leading premise, at its instance. -/
theorem premW_head {env : Env} {D D' : Interp} {els els' : Prop} {ρ : VarEnv} {x : IL.Id}
    {op' : MixopS} {pe : Exp} (hD : ∀ w, EvalExp env ρ pe w → D x op' [] w → D' x op' [] w)
    (h : PremW env D els ρ (.rulePr x [] op' pe)) : PremW env D' els' ρ (.rulePr x [] op' pe) := by
  cases h with
  | rulePr ha hw hd =>
    obtain rfl := evalArgs_nil_iff.1 ha
    exact .rulePr ha hw (hD _ hw hd)

/-- **A rule body under a second interpretation**, when the two agree at the instances of the
leading premise. -/
theorem ruleBody_swap {env : Env} {D D' : Interp} {els els' : Prop} {op : MixopS} {nm : IL.Id}
    {qs : List Param} {e pe : Exp} {x : IL.Id} {op' : MixopS} {rest : List Prem} {v : Value}
    (hrest : TailFree rest)
    (hD : ∀ w, Inst env D els (.ruleD nm qs op e (.rulePr x [] op' pe :: rest)) v w →
      D x op' [] w → D' x op' [] w)
    (h : RuleBody env D els [] [] op (.ruleD nm qs op e (.rulePr x [] op' pe :: rest)) v) :
    RuleBody env D' els' [] [] op (.ruleD nm qs op e (.rulePr x [] op' pe :: rest)) v := by
  obtain ⟨hop, ρ₀, σ, hps, hq, he, hp⟩ := h
  have e₀ : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  rw [e₀] at hq he hp
  have hr : ∀ pr ∈ rest, PremW env D els (VarEnv.empty.bindVals σ) pr :=
    fun pr hpr => hp pr (.tail _ hpr)
  have h₀ : PremW env D' els' (VarEnv.empty.bindVals σ) (.rulePr x [] op' pe) :=
    premW_head (fun w hw => hD w ⟨σ, hq, he, hw, hr⟩) (hp _ (.head _))
  have hall : ∀ pr ∈ .rulePr x [] op' pe :: rest, PremW env D' els' (VarEnv.empty.bindVals σ) pr :=
    fun pr hpr => (List.mem_cons.1 hpr).elim (fun h => h ▸ h₀)
      (fun h => premW_tail (hrest pr h) (hr pr h))
  exact ⟨hop, VarEnv.empty, σ, rfl, hq, he, hall⟩

/-- `Inst` under `DDerivesB`'s premises is `Inst` under `DDerives`'s, and back: the remaining
premises consult no relation. -/
theorem inst_congr {env : Env} {D D' : Interp} {els els' : Prop} {nm : IL.Id} {qs : List Param}
    {op : MixopS} {e pe : Exp} {x : IL.Id} {op' : MixopS} {rest : List Prem} {v w : Value}
    (hrest : TailFree rest)
    (h : Inst env D els (.ruleD nm qs op e (.rulePr x [] op' pe :: rest)) v w) :
    Inst env D' els' (.ruleD nm qs op e (.rulePr x [] op' pe :: rest)) v w := by
  obtain ⟨σ, hq, he, hw, hr⟩ := h
  exact ⟨σ, hq, he, hw, fun pr hpr => premW_tail (hrest pr hpr) (hr pr hpr)⟩

/-- **A rule of `Step` with a leading relational premise and a plain conclusion fires the same
under both readings**, when the two readings agree at the instances of that premise. -/
theorem firesB_iff_swap {env : Env} {k : Nat} {nm : IL.Id} {qs : List Param} {e pe : Exp}
    {x : IL.Id} {op' : MixopS} {rest : List Prem}
    (hR : HasRuleAt env "Step" "%~>%" k (.ruleD nm qs "%~>%" e (.rulePr x [] op' pe :: rest)))
    (hn : hasOptNil e = false) (hrest : TailFree rest) {v : Value}
    (hD : ∀ w, Inst env (fun _ _ _ _ => True) True (.ruleD nm qs "%~>%" e (.rulePr x [] op' pe :: rest)) v w →
      (DDerivesB env (otherwiseB env) x op' [] w ↔ DDerives env (otherwise env) x op' [] w)) :
    FiresB env "Step" k v ↔ Fires env "Step" k v := by
  constructor
  · rintro ⟨t, rules, r, hrel, hr, hb⟩
    obtain rfl : r = _ := Option.some.inj (hr.symm.trans (ruleAt_get hR hrel))
    have hb' := (ruleBodyB_iff_of_not hn).1 hb
    exact ⟨t, rules, _, hrel, hr,
      ruleBody_swap hrest (fun w hi => (hD w (inst_congr hrest hi)).1) hb'⟩
  · rintro ⟨t, rules, r, hrel, hr, hb⟩
    obtain rfl : r = _ := Option.some.inj (hr.symm.trans (ruleAt_get hR hrel))
    exact ⟨t, rules, _, hrel, hr, (ruleBodyB_iff_of_not hn).2
      (ruleBody_swap hrest (fun w hi => (hD w (inst_congr hrest hi)).2) hb)⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.Transfer
