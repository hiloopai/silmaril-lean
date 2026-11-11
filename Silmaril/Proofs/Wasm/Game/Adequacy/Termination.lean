module

public import Silmaril.Proofs.Wasm.Game.Env.Basic
public import Silmaril.Proofs.Wasm.Game.Machine.Basic

/-!
# Termination excludes divergence

An abstract termination argument (`nsteps_normal_not_infinite`), determinism
of strategy-definable hosts at callouts, and `not_diverges_of_run`: under an
induced host, a configuration with a finite run to a result has no infinite
run (deterministic profile, `Det.DStep.shrink`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

/-! ### Abstract termination argument -/

/-- **Termination excludes divergence, abstractly.** If peaks of `R` are joinable in at most
one step on each side (`Det.Join`) and the two sides of a non-trivial peak are strictly smaller
than its top under `μ`, then a configuration with a counted path to a normal form has no
infinite trace. Lexicographic induction on (path length, `μ`): the first step of an infinite
trace either follows the path (the length drops) or leaves it, in which case the distance to
the normal form does not grow (`NSteps.of_step_join`) and `μ` drops. -/
theorem nsteps_normal_not_infinite {α : Type _} {R : α → α → Prop} (μ : α → Nat)
    (hj : ∀ {x a b : α}, R x a → R x b → Det.Join R a b)
    (hs : ∀ {x a b : α}, R x a → R x b → a = b ∨ μ a < μ x)
    {y : α} (hy : ∀ z, ¬ R y z) :
    ∀ (k : Nat) (x : α), NSteps R k x y → ¬ InfiniteTrace R x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  suffices h : ∀ (n : Nat) (x : α), μ x = n → NSteps R k x y → ¬ InfiniteTrace R x from
    fun x => h _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro x hn hpath hinf
  obtain ⟨x₁, hx₁, hinf₁⟩ := hinf.unfold
  obtain ⟨m, hm, hpath₁⟩ := NSteps.of_step_join hj hy hpath hx₁
  cases hpath with
  | refl => exact hy _ hx₁
  | @head _ a _ k' hxa hrest =>
    rcases hs hx₁ hxa with heq | hlt
    · exact ihk k' (Nat.lt_succ_self k') _ (heq ▸ hrest) hinf₁
    · rcases Nat.lt_or_ge m (k' + 1) with hlt' | hge
      · exact ihk m hlt' x₁ hpath₁ hinf₁
      · have hmk : m = k' + 1 := le_antisymm hm hge
        exact ihn (μ x₁) (by omega) x₁ rfl (hmk ▸ hpath₁) hinf₁

/-! ### Determinism of strategy-definable hosts -/

/-- The host relation `hostOf ts K` has at most one outcome per call. -/
theorem hostOf_out_unique {ts : List FnType} {K : Silmaril.Wasm.Game.Env (ifaceSig ts)} {h : Nat}
    {s : Store Nat} {args : List Val} {out₁ out₂ : HostOutcome Nat}
    (h₁ : hostOf ts K h s args out₁) (h₂ : hostOf ts K h s args out₂) : out₁ = out₂ := by
  obtain ⟨e₁, he₁, ⟨w₁, hw₁, rfl⟩ | ⟨hn₁, rfl⟩⟩ := h₁ <;>
    obtain ⟨e₂, he₂, ⟨w₂, hw₂, rfl⟩ | ⟨hn₂, rfl⟩⟩ := h₂ <;>
    simp only [he₁, Option.some.injEq] at he₂ <;> subst he₂
  · rw [Env.Answers.unique hw₁ hw₂]
  · exact (hn₂ _ hw₁).elim
  · exact (hn₁ _ hw₂).elim
  · rfl

/-- At a callout, Core steps against a host with unique outcomes are deterministic. -/
theorem Step.eq_of_callout {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics Nat}
    (hu : ∀ h s args out₁ out₂, host h s args out₁ → host h s args out₂ → out₁ = out₂)
    {c c₁ c₂ : Config Nat} {x : Ctx × Nat × Nat × List Val}
    (hd : decompose? c.store c.code = some x)
    (h₁ : Step P host c c₁) (h₂ : Step P host c c₂) : c₁ = c₂ := by
  rcases Step.split_host h₁ with h₁ | ⟨E₁, a₁, hh₁, args₁, hd₁, ⟨s₁, r₁, hr₁, rfl⟩ | ⟨hv₁, rfl⟩⟩
  · rw [decompose?_none_of_noRedex (Step.noRedex h₁)] at hd
    cases hd
  all_goals
    rcases Step.split_host h₂ with h₂ | ⟨E₂, a₂, hh₂, args₂, hd₂, ⟨s₂, r₂, hr₂, rfl⟩ | ⟨hv₂, rfl⟩⟩
    · rw [decompose?_none_of_noRedex (Step.noRedex h₂)] at hd
      cases hd
  all_goals
    simp only [hd₁, Option.some.injEq, Prod.mk.injEq] at hd₂
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hd₂
  · cases hu _ _ _ _ _ hr₁ hr₂
    rfl
  · cases hu _ _ _ _ _ hr₁ hv₂
  · cases hu _ _ _ _ _ hv₁ hr₂
  · rfl

/-- A finished configuration has no step. -/
theorem Step.not_result {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics Nat}
    {c c' : Config Nat}
    {r : Result} (hc : c.code = r.toAdmin) : ¬ Step P host c c' := by
  intro h
  apply Step.not_quiet h
  rw [hc]
  cases r with
  | values vs => exact quiet_vals vs
  | throw a => exact quiet_throwing a
  | trap => exact quiet_trap

/-- Host-free runs that reach a normal form have no infinite continuation from their start
(route: `Det.DStep.shrink`). -/
theorem reach_normal_not_infinite {o : GrowOracle} {x y : Store Nat × Thread}
    (run : Reach (profile o) x y) (normal : ∀ z, ¬ InternalP (profile o) y z) :
    ¬ InfiniteTrace (InternalP (profile o)) x := by
  unfold Reach at run
  rw [internalP_profile] at run normal ⊢
  obtain ⟨k, hk⟩ := NSteps.of_rtg run
  exact nsteps_normal_not_infinite tsize (fun ha hb => Internal.deterministic ha hb)
    (fun ha hb => Internal.shrink ha hb) normal k x hk

/-- Termination excludes divergence under a strategy-definable host (route:
`Det.DStep.shrink` for host-free steps, determinism of `hostOf` at callouts). -/
theorem not_diverges_of_run {o : GrowOracle} {ts : List FnType}
    {K : Silmaril.Wasm.Game.Env (ifaceSig ts)} {c c' : Config Nat} {r : Result}
    (run : Steps (profile o) (hostOf ts K) c c') (final : c'.code = r.toAdmin) :
    ¬ Diverges (profile o) (hostOf ts K) c := by
  have hu : ∀ h s args out₁ out₂, hostOf ts K h s args out₁ → hostOf ts K h s args out₂ →
      out₁ = out₂ := fun _ _ _ _ _ h₁ h₂ => hostOf_out_unique h₁ h₂
  have hj : ∀ {x a b : Config Nat}, Step (profile o) (hostOf ts K) x a →
      Step (profile o) (hostOf ts K) x b → Det.Join (Step (profile o) (hostOf ts K)) a b := by
    intro x a b ha hb
    cases hd : decompose? x.store x.code with
    | none => exact Step.deterministic_profile hd ha hb
    | some y =>
      rw [Step.eq_of_callout hu hd ha hb]
      exact Det.Join.rfl'
  have hs : ∀ {x a b : Config Nat}, Step (profile o) (hostOf ts K) x a →
      Step (profile o) (hostOf ts K) x b → a = b ∨ sizeOf a.code < sizeOf x.code := by
    intro x a b ha hb
    cases hd : decompose? x.store x.code with
    | some y => exact .inl (Step.eq_of_callout hu hd ha hb)
    | none =>
      show a = b ∨ sizeOf a.code < sizeOf x.code
      have nh : ∀ {c' : Config Nat}, Step (profile o) (hostOf ts K) x c' →
          Det.DStep o x c' := by
        intro c' h
        rcases Step.split_host h with h | ⟨E, a, hh, args, hd', -⟩
        · exact h
        · cases hd.symm.trans hd'
      have ha' : Det.DStep o x a := nh ha
      have hb' : Det.DStep o x b := nh hb
      rcases x with ⟨s, f, code⟩
      rcases Det.DStep.shrink _ s f code a b rfl ha' hb' with h | ⟨-, -, hl, -⟩
      · exact .inl h
      · exact .inr hl
  obtain ⟨k, hk⟩ := NSteps.of_rtg run
  exact nsteps_normal_not_infinite (fun c : Config Nat => sizeOf c.code) hj hs
    (fun z hz => Step.not_result final hz) k c hk

end Silmaril.Proofs.Wasm.Game
