module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxElse.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round8.NxDer.Thms

/-!
# Round 8, `otherwise` across erasure: recording where `otherwise` is used (unrefined)

`dderivesB_fire`: a derivation of a `grE` relation read with `O` is one read with `elseF env O`,
which records, wherever an `otherwise` premise is read, that its relation is in `grE` and that its
rule fired (`Fired`). The proof is round 7's `Determ.dderivesB_mapO`, with the facts of the rule
added at the rule case and the relation premises kept in `grE` by `EraseAll.xFacts`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxElse

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (grE gdE xPrem)
open Round6.Reading (DDerivesB DPremB)

variable {B : Builtins}

mutual
/-- **A derivation of a `grE` relation records where it reads `otherwise`.** -/
theorem dderivesB_fire {O : ElseI} :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, grE x = true →
      DDerivesB (utf8Env B) O x op args v → DDerivesB (utf8Env B) (elseF (utf8Env B) O) x op args v
  | _, _, _, _, hx, .rule (σ := σ) (ρ₀ := ρ₀) (e' := e') hrel hrule halt hps hq he hp => by
    have hXF := EraseAll.xFacts hx hrel hrule
    refine .rule hrel hrule halt hps hq he fun pr hpr => ?_
    exact dpremB_fire (hXF.prems pr hpr)
      (fun hin hO => ⟨hO, hx, _, _, _, _, _, _, _, _, e', ρ₀, σ, hrel, hrule,
        List.any_eq_true.2 ⟨pr, hpr, hin⟩, halt, hps, hq, he⟩) (hp pr hpr)
termination_by structural _ _ _ _ _ hd => hd

/-- `dderivesB_fire` for premises: `els` is needed only under an `otherwise`. -/
theorem dpremB_fire {O : ElseI} {els els' : Prop} :
    ∀ {ρ : VarEnv} {pr : Prem}, xPrem grE gdE pr = true → (elseIn pr = true → els → els') →
      DPremB (utf8Env B) O els ρ pr → DPremB (utf8Env B) (elseF (utf8Env B) O) els' ρ pr
  | _, _, _, _, .ifPr h => .ifPr h
  | _, _, _, hels, .elsePr h => .elsePr (hels rfl h)
  | _, _, _, _, .letPr h₂ h₁ => .letPr h₂ h₁
  | _, _, hx, _, .rulePr ha he hd => by
    simp only [xPrem, Bool.and_eq_true] at hx
    exact .rulePr ha he (dderivesB_fire hx.1.1 hd)
  | _, _, _, _, .iterOptNone hd hne hall => .iterOptNone hd hne hall
  | _, _, hx, hels, .iterOptSome hd hne hs hp => by
    simp only [xPrem, Bool.and_eq_true] at hx
    exact .iterOptSome hd hne hs (dpremB_fire hx.1.1 (fun h => hels h) hp)
  | _, _, hx, hels, .iterList hit hd hne hl hk hp => by
    simp only [xPrem, Bool.and_eq_true] at hx
    exact .iterList hit hd hne hl hk fun r hr => dpremB_fire hx.1.1 (fun h => hels h) (hp r hr)
  | _, _, hx, hels, .iterListN hd he hk hl hlen hp => by
    simp only [xPrem, Bool.and_eq_true] at hx
    exact .iterListN hd he hk hl hlen fun r hr => dpremB_fire hx.1.1 (fun h => hels h) (hp r hr)
termination_by structural _ _ _ _ hd => hd
end

end Silmaril.Wasm.SpecTec.Sim.Round8.NxElse
