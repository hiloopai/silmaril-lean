module

public import Silmaril.Wasm.SingleThreaded.Determinism.HeadCtl

@[expose] public section

/-! # Host-free reduction in the deterministic profile is joinable

Core reduction is *not* a function even in the deterministic profile: SpecTec's
`Step_pure/trap-instrs` (`val* TRAP instr* ~> TRAP`) and
`Step_read/throw_ref-instrs` overlap with `Step/ctxt-instrs` applied to a
shorter bubble, e.g. `v₁ v₂ TRAP` steps both to `TRAP` and to `v₁ TRAP`. What
holds is the diamond property: two successors are joinable in at most one step
each (`Join`). Everything else (head steps) is deterministic.
-/

namespace Silmaril.Wasm.SingleThreaded.Det

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type}

/-- A bubbled result reaches the bare bubble in at most one step. -/
theorem bubble_to {o : GrowKind → Nat → Nat → Nat → Bool} {s : Store H} {f : Frame}
    {p : List Val} {X r : List Admin} (hX : IsBubble X) :
    Relation.ReflGen (DStep o) ⟨s, f, vals p ++ X ++ r⟩ ⟨s, f, X⟩ := by
  by_cases h : p ≠ [] ∨ r ≠ []
  · refine .single ?_
    rcases hX with rfl | ⟨a, rfl⟩
    · exact .trapInstrs h
    · exact .throwRefInstrs (a := a) h
  · simp only [ne_eq, not_or, not_not] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using (Relation.ReflGen.refl : Relation.ReflGen (DStep o) _ _)

theorem headDec_bubble_false {P : Profile} {s : Store H} {f : Frame} {code : List Admin}
    {c₁ c₂ : Config H} (hd : HeadDec P s f code c₁) (hb : Bubble s f code c₂) : False := by
  obtain ⟨vs, args, e, rest, c₀, hf, -, hh, -⟩ := fnv_headDec hd
  obtain ⟨p, q, u, r, -, ⟨hf', -⟩ | ⟨a, hf', -⟩⟩ := fnv_bubble hb
  · rw [hf] at hf'
    simp only [Prod.mk.injEq, List.cons.injEq] at hf'
    exact hh.good.ne_trap hf'.2.1
  · rw [hf] at hf'
    simp only [Prod.mk.injEq, List.cons.injEq] at hf'
    obtain ⟨h1, rfl, -⟩ := hf'
    have := hh.good.throwRef rfl
    subst this
    have := congrArg List.getLast? h1
    simp at this

theorem bubble_join {o : GrowKind → Nat → Nat → Nat → Bool} {s : Store H} {f : Frame}
    {code : List Admin} {c₁ c₂ : Config H} (hb₁ : Bubble s f code c₁) (hb₂ : Bubble s f code c₂) :
    Join (DStep o) c₁ c₂ := by
  obtain ⟨p₁, q₁, u₁, r₁, -, ⟨hf₁, -, rfl⟩ | ⟨a₁, hf₁, -, rfl⟩⟩ := fnv_bubble hb₁ <;>
    obtain ⟨p₂, q₂, u₂, r₂, -, ⟨hf₂, -, rfl⟩ | ⟨a₂, hf₂, -, rfl⟩⟩ := fnv_bubble hb₂
  · exact ⟨_, bubble_to (.inl rfl), bubble_to (.inl rfl)⟩
  · rw [hf₁] at hf₂; simp at hf₂
  · rw [hf₁] at hf₂; simp at hf₂
  · rw [hf₁] at hf₂
    simp only [Prod.mk.injEq, List.cons.injEq] at hf₂
    have h := (append_singleton_inj.mp hf₂.1).2
    simp only [Val.ref.injEq, Ref.exn.injEq] at h
    subst h
    exact ⟨_, bubble_to (.inr ⟨a₁, rfl⟩), bubble_to (.inr ⟨a₁, rfl⟩)⟩

theorem sizeOf_lt_code {vs args : List Val} {e : Admin} {rest : List Admin} :
    sizeOf e < sizeOf (vals vs ++ (vals args ++ e :: rest)) :=
  List.sizeOf_lt_of_mem (by simp)

theorem head_join {o : GrowKind → Nat → Nat → Nat → Bool} {s : Store H} {f : Frame}
    {vs₁ vs₂ args₁ args₂ : List Val} {e : Admin} {rest : List Admin} {c₀₁ c₀₂ : Config H}
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf e → DStep o ⟨s, f, body⟩ c₁ → DStep o ⟨s, f, body⟩ c₂ →
      Join (DStep o) c₁ c₂)
    (hva : vs₁ ++ args₁ = vs₂ ++ args₂)
    (hh₁ : Head (Profile.deterministic o) s f args₁ e c₀₁)
    (hh₂ : Head (Profile.deterministic o) s f args₂ e c₀₂) (p : List Val)
    (hp : args₁ = p ++ args₂) :
    Join (DStep o) ⟨c₀₁.store, c₀₁.frame, vals vs₁ ++ c₀₁.code ++ rest⟩
      ⟨c₀₂.store, c₀₂.frame, vals vs₂ ++ c₀₂.code ++ rest⟩ := by
  have key : p = [] ∧ Join (DStep o) c₀₁ c₀₂ := by
    by_cases hk : famOf e = .control
    · exact Head.det_ctl hk ih hh₁ hh₂ hp
    · obtain ⟨hp, rfl⟩ := Head.det_fam hk hh₁ hh₂ hp
      exact ⟨hp, Join.rfl'⟩
  obtain ⟨rfl, hj⟩ := key
  simp only [List.nil_append] at hp
  subst hp
  have : vs₁ = vs₂ := List.append_cancel_right hva
  subst this
  exact Join.map (fun c => ⟨c.store, c.frame, vals vs₁ ++ c.code ++ rest⟩)
    (lift_instrs vs₁ rest) hj

/-- **Diamond property** of host-free reduction in the deterministic profile. -/
theorem DStep.join {o : GrowKind → Nat → Nat → Nat → Bool} :
    ∀ (n : Nat) (s : Store H) (f : Frame) (code : List Admin) (c₁ c₂ : Config H),
      sizeOf code = n → DStep o ⟨s, f, code⟩ c₁ → DStep o ⟨s, f, code⟩ c₂ →
      Join (DStep o) c₁ c₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s f code c₁ c₂ hn h₁ h₂
  rcases Step.decomp h₁ with hd₁ | hb₁ <;> rcases Step.decomp h₂ with hd₂ | hb₂
  · obtain ⟨vs₁, args₁, e₁, rest₁, c₀₁, hf₁, hc₁, hh₁, rfl⟩ := fnv_headDec hd₁
    obtain ⟨vs₂, args₂, e₂, rest₂, c₀₂, hf₂, -, hh₂, rfl⟩ := fnv_headDec hd₂
    simp only at hf₁ hf₂ hc₁ hh₁ hh₂
    rw [hf₁] at hf₂
    simp only [Prod.mk.injEq, List.cons.injEq] at hf₂
    obtain ⟨hva, rfl, rfl⟩ := hf₂
    have ih' : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
        sizeOf body < sizeOf e₁ → DStep o ⟨s, f, body⟩ c₁ → DStep o ⟨s, f, body⟩ c₂ →
        Join (DStep o) c₁ c₂ := by
      intro s f body c₁ c₂ hlt
      refine ih _ ?_ s f body c₁ c₂ rfl
      subst hn hc₁
      exact lt_trans hlt sizeOf_lt_code
    rcases append_eq_append_suffix hva with ⟨p, hp⟩ | ⟨p, hp⟩
    · exact head_join ih' hva hh₁ hh₂ p hp
    · exact (head_join ih' hva.symm hh₂ hh₁ p hp).symm
  · exact (headDec_bubble_false hd₁ hb₂).elim
  · exact (headDec_bubble_false hd₂ hb₁).elim
  · exact bubble_join hb₁ hb₂

theorem DStep.join' {o : GrowKind → Nat → Nat → Nat → Bool} {c c₁ c₂ : Config H}
    (h₁ : DStep o c c₁) (h₂ : DStep o c c₂) : Join (DStep o) c₁ c₂ := by
  rcases c with ⟨s, f, code⟩
  exact DStep.join _ s f code c₁ c₂ rfl h₁ h₂

end Silmaril.Wasm.SingleThreaded.Det
