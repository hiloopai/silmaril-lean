module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Rules

/-!
# Family V: evaluating iterations

Two shapes of `IterE` the vector rules use: a one-domain list iteration whose body is evaluated per
element (`vtestop`'s `($inez_(…, i)!%.0)*`), and a domain-free `^M` iteration (`vsplat`'s
`$lpacknum_(Lnn, c_1)^M`), which repeats its body.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Vec

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- Finitely many evaluations have a common fuel. -/
theorem forall₂_fuel {env : Env} {ρ : VarEnv} {b : Exp} {x : IL.Id} :
    ∀ {vs ws : List Value}, List.Forall₂ (fun v w => EvalExp env (ρ.bindVals [(x, v)]) b w) vs ws →
      ∃ d, List.Forall₂ (fun v w => evalExp d env (ρ.bindVals [(x, v)]) b = .ok w) vs ws
  | [], [], .nil => ⟨0, .nil⟩
  | _ :: _, _ :: _, .cons ⟨m, hm⟩ hs => by
      obtain ⟨d, hd⟩ := forall₂_fuel hs
      exact ⟨max m d, .cons (evalExp_ok_of_le (by omega) hm)
        (List.Forall₂.imp (fun _ _ h => evalExp_ok_of_le (by omega) h) hd)⟩

/-- `b*` over one domain `x <- y`: the list of the body's values, round by round. -/
theorem evalExp_iterList1 {env : Env} {ρ : VarEnv} {b : Exp} {x y : IL.Id}
    {vs ws : List Value} (h : ρ.findVal? y = some (.list vs))
    (hb : List.Forall₂ (fun v w => EvalExp env (ρ.bindVals [(x, v)]) b w) vs ws) :
    EvalExp env ρ (.iterE b (.mk .list [.mk x (.varE y)])) (.list ws) := by
  obtain ⟨d, hd⟩ := forall₂_fuel hb
  refine evalExp_iterE_iff.mpr ⟨d + 3, ?_⟩
  have hdoms : evalDoms (d + 2) env ρ [.mk x (.varE y)] = .ok [(x, Value.list vs)] := by
    simp [evalDoms, domVar, domSrc, evalExp, h]
  rw [evalIterE, hdoms]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, Value.asList?,
    List.isEmpty_cons]
  refine ⟨[(x, Value.list vs)], rfl, trivial, vs.length, rfl, ?_⟩
  rw [evalIterList]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, List.mapM_cons,
    List.mapM_nil]
  refine ⟨[(x, vs)], by simp [Value.asList?], by simp, ws, ?_, rfl⟩
  rw [Equiv.Execution.iterRows_singleton, evalRounds]
  clear hdoms h hb
  induction hd with
  | nil => rfl
  | cons hvw _ ih =>
      simp only [List.map_cons, List.mapM_cons, Res.bind_eq_ok]
      exact ⟨_, hvw, _, ih, rfl⟩

/-- The rows of a domain-free iteration bind nothing. -/
theorem iterRows_nil (k : Nat) : iterRows [] none k = List.replicate k [] := by
  have h : iterRow [] none = fun _ => [] := funext fun _ => rfl
  rw [iterRows, h, List.map_const', List.length_range]

/-- `b^n` with no domain: `n` copies of the body's value. -/
theorem evalExp_iterListN_nodom {env : Env} {ρ : VarEnv} {b eₙ : Exp} {k : Nat} {v : Value}
    (hn : EvalExp env ρ eₙ (.num (.natN k))) (hb : EvalExp env ρ b v) :
    EvalExp env ρ (.iterE b (.mk (.listN eₙ none) [])) (.list (List.replicate k v)) := by
  obtain ⟨m₁, h₁⟩ := hn
  obtain ⟨m₂, h₂⟩ := hb
  refine evalExp_iterE_iff.mpr ⟨m₁ + m₂ + 3, ?_⟩
  have e₁ : evalExp (m₁ + m₂ + 2) env ρ eₙ = .ok (.num (.natN k)) :=
    evalExp_ok_of_le (by omega) h₁
  have e₂ : evalExp (m₁ + m₂) env ρ b = .ok v := evalExp_ok_of_le (by omega) h₂
  rw [evalIterE]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok]
  refine ⟨[], by simp only [evalDoms, List.mapM_nil]; rfl, _, e₁, k, rfl, ?_⟩
  rw [evalIterList]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, List.mapM_nil]
  refine ⟨[], rfl, by simp, List.replicate k v, ?_, rfl⟩
  rw [evalRounds, iterRows_nil]
  clear h₁ e₁
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, List.mapM_cons, Res.bind_eq_ok, VarEnv.bindVals_nil]
      exact ⟨v, e₂, _, ih, rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Vec
