module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdPureStep.Decode

/-!
# Inverting a call of a one-clause definition

`State.evalExp_call1` evaluates a call of a definition with one clause and no premises forward.
`evalExp_call1_inv` is its converse: whatever value the call has is the value of the clause's
body at the matched scope, provided `B` does not interpret the name (`callDef` consults `B`
when the body definitely fails). This is what the backward lemmas use to read the store
updaters (`$with_local`, …) and accessors back.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdPureStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- **A call of a one-clause definition, inverted.** -/
theorem evalExp_call1_inv {env : Env} {ρ ρ₀ : VarEnv} {x : IL.Id} {pats args : List Arg}
    {ws : List ArgV} {body : Exp} {v : Value} (hd : State.HasClause1 env x pats body)
    (hρ : ρ.findDef? x = none) (hb : env.builtins.call x ws = none)
    (ha : EvalArgs env ρ args ws) (hm : MatchArgs env VarEnv.empty pats ws ρ₀)
    (h : EvalExp env ρ (.callE x args) v) : EvalExp env ρ₀ body v := by
  obtain ⟨ps, t, q, hf⟩ := hd
  obtain ⟨n₀, hn⟩ := evalExp_callE_iff.1 h
  obtain ⟨n₁, ha⟩ := ha
  obtain ⟨n₂, hm⟩ := hm
  have hc : callDef (n₀ + n₁ + n₂ + 3) env ρ x args = .ok v := callDef_ok_of_le (by omega) hn
  have ea : evalArgs (n₀ + n₁ + n₂ + 2) env ρ args = .ok ws := evalArgs_ok_of_le (by omega) ha
  have em : matchArgs (n₀ + n₁ + n₂ + 1) env VarEnv.empty pats ws = .ok ρ₀ :=
    matchArgs_ok_of_le (by omega) hm
  have et : tryClauses (n₀ + n₁ + n₂ + 2) env [.defD q pats body []] ws =
      evalExp (n₀ + n₁ + n₂ + 1) env ρ₀ body := by
    simp only [tryClauses, em, Bind.bind, Except.bind, premsHold_nil_eq, Res.elimUndef_ok]
  simp only [callDef, ea, Bind.bind, Except.bind, hρ, Option.getD_none, Res.ofOption, hf, et] at hc
  revert hc
  rcases hr : evalExp (n₀ + n₁ + n₂ + 1) env ρ₀ body with e | u
  · cases e with
    | outOfFuel => simp [Res.elimUndef]
    | undef => simp [Res.elimUndef, hb]
  · intro hc
    simp only [Res.elimUndef_ok] at hc
    exact ⟨_, hr.trans hc⟩


/-! ## Paths, inverted -/

theorem pathGet_root_inv {env : Env} {ρ : VarEnv} {v u : Value} (h : PathGet env ρ v .rootP u) :
    u = v := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => simp [pathGet] at h
  | succ n => simp only [pathGet] at h; exact (Except.ok.inj h).symm

theorem pathGet_dot_inv {env : Env} {ρ : VarEnv} {v w : Value} {p : Path} {a : AtomS}
    (h : PathGet env ρ v (.dotP p a) w) : ∃ u, PathGet env ρ v p u ∧ u.field? a = some w := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => simp [pathGet] at h
  | succ n =>
      simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨u, hu, hw⟩ := h
      exact ⟨u, ⟨n, hu⟩, hw⟩

theorem pathGet_idx_inv {env : Env} {ρ : VarEnv} {v w : Value} {p : Path} {e : Exp}
    (h : PathGet env ρ v (.idxP p e) w) :
    ∃ u iv i, PathGet env ρ v p u ∧ EvalExp env ρ e iv ∧ iv.asNat? = some i ∧ u.idx? i = some w := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => simp [pathGet] at h
  | succ n =>
      simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨u, hu, iv, hiv, i, hi, hw⟩ := h
      exact ⟨u, iv, i, ⟨n, hu⟩, ⟨n, hiv⟩, hi, hw⟩

theorem pathSet_root_inv {env : Env} {ρ : VarEnv} {v w r : Value}
    (h : PathSet env ρ v .rootP w r) : r = w := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => simp [pathSet] at h
  | succ n => simp only [pathSet] at h; exact (Except.ok.inj h).symm

theorem pathSet_dot_inv {env : Env} {ρ : VarEnv} {v w r : Value} {p : Path} {a : AtomS}
    (h : PathSet env ρ v (.dotP p a) w r) :
    ∃ u u', PathGet env ρ v p u ∧ u.setField a w = some u' ∧ PathSet env ρ v p u' r := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => simp [pathSet] at h
  | succ n =>
      simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨u, hu, u', hu', hr⟩ := h
      exact ⟨u, u', ⟨n, hu⟩, hu', ⟨n, hr⟩⟩

theorem pathSet_idx_inv {env : Env} {ρ : VarEnv} {v w r : Value} {p : Path} {e : Exp}
    (h : PathSet env ρ v (.idxP p e) w r) :
    ∃ u iv i u', PathGet env ρ v p u ∧ EvalExp env ρ e iv ∧ iv.asNat? = some i ∧
      u.setIdx i w = some u' ∧ PathSet env ρ v p u' r := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => simp [pathSet] at h
  | succ n =>
      simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨u, hu, iv, hiv, i, hi, u', hu', hr⟩ := h
      exact ⟨u, iv, i, u', ⟨n, hu⟩, ⟨n, hiv⟩, hi, hu', ⟨n, hr⟩⟩

end Silmaril.Wasm.SpecTec.Sim.BwdPureStep
