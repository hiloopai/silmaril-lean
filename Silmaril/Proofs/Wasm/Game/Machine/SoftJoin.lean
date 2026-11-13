module

public import Silmaril.Proofs.Wasm.Game.Machine.SoftCtl

/-!
# Determinism of host-free Core steps up to profile choices: the main lemma

`soft_join`: two host-free steps from the same configuration under an arbitrary profile have
equal results, or both are `Soft` (a profile choice or a bubble under the context rules).

Source: the induction follows silmaril-lean's `Det.DStep.join` and `Det.head_join`
(`Silmaril/Wasm/SingleThreaded/Determinism/Join.lean`, pinned revision); the family cases are
new (the deterministic families use silmaril-lean's profile-free `ParametricStep.det`,
`VariableStep.det`, `RefStep.det`, `AggregateStep.det`; the choice families give `Soft`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.Choice

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-- A choice head under a value prefix and a suffix is `Soft`. -/
theorem soft_of_head_choice {P : Profile} {s : Store H} {f : Frame} {vs args : List Val}
    {e : Admin} {rest : List Admin} {c₀ : Config H} (hh : Head P s f args e c₀)
    (hk : ChoiceFam (famOf e)) :
    Soft P ⟨s, f, vals vs ++ (vals args ++ e :: rest)⟩
      ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ := by
  have hne : famOf e ≠ .control := by intro h; rw [h] at hk; exact hk
  have hf : FamRel P (famOf e) s f (vals args ++ [e]) ⟨c₀.store, c₀.frame, c₀.code⟩ := by
    rcases c₀ with ⟨_, _, _⟩
    exact hh.fam_inv hne
  have hl := Soft.instrs (vs := vs) (rest := rest) (Soft.choice hk hf)
  have hcode : vals vs ++ (vals args ++ e :: rest) = vals vs ++ (vals args ++ [e]) ++ rest := by
    simp
  rw [hcode]
  exact hl

/-- Two deterministic family heads at the same instruction consume the same arguments and
have the same result. -/
theorem det_fam_free {P : Profile} {s : Store H} {f : Frame} {args₁ args₂ p : List Val}
    {e : Admin} {c₁ c₂ : Config H} (hc : famOf e ≠ .control) (hk : ¬ ChoiceFam (famOf e))
    (h₁ : Head P s f args₁ e c₁) (h₂ : Head P s f args₂ e c₂) (hp : args₁ = p ++ args₂) :
    p = [] ∧ c₁ = c₂ := by
  have f₁ := h₁.fam_inv hc
  have f₂ := h₂.fam_inv hc
  have hl : vals args₁ ++ [e] = vals p ++ (vals args₂ ++ [e]) := by subst hp; simp
  revert f₁ f₂ hc hk
  generalize famOf e = k
  intro hc hk f₁ f₂
  cases k with
  | parametric =>
    obtain ⟨is₁, r₁, rfl⟩ := f₁; obtain ⟨is₂, r₂, rfl⟩ := f₂
    obtain ⟨hp', rfl⟩ := ParametricStep.det r₁ r₂ hl; exact ⟨hp', rfl⟩
  | «variable» => exact VariableStep.det f₁ f₂ hl
  | reference => exact RefStep.det f₁ f₂ hl
  | aggregate => exact AggregateStep.det f₁ f₂ hl
  | control => exact absurd rfl hc
  | _ => exact absurd trivial hk

/-- `SoftJoin` under a value prefix and a suffix. -/
theorem SoftJoin.instrs {P : Profile} {s : Store H} {f : Frame} {vs args : List Val} {e : Admin}
    {rest : List Admin} {c₁ c₂ : Config H} (h : SoftJoin P ⟨s, f, vals args ++ [e]⟩ c₁ c₂) :
    SoftJoin P ⟨s, f, vals vs ++ (vals args ++ e :: rest)⟩
      ⟨c₁.store, c₁.frame, vals vs ++ c₁.code ++ rest⟩
      ⟨c₂.store, c₂.frame, vals vs ++ c₂.code ++ rest⟩ := by
  have hm : SoftJoin P ⟨s, f, vals vs ++ (vals args ++ [e]) ++ rest⟩
      ⟨c₁.store, c₁.frame, vals vs ++ c₁.code ++ rest⟩
      ⟨c₂.store, c₂.frame, vals vs ++ c₂.code ++ rest⟩ :=
    h.map (fun c => ⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩)
      (fun x hx => by rcases x with ⟨_, _, _⟩; exact .instrs hx)
  have hcode : vals vs ++ (vals args ++ e :: rest) = vals vs ++ (vals args ++ [e]) ++ rest := by
    simp
  rw [hcode]
  exact hm

/-- Two head steps at the same first non-value with the same arguments. -/
theorem head_soft_same {P : Profile} {s : Store H} {f : Frame} {args₁ args₂ p : List Val}
    {e : Admin} {c₀₁ c₀₂ : Config H}
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf e → Step P noHost ⟨s, f, body⟩ c₁ → Step P noHost ⟨s, f, body⟩ c₂ →
      SoftJoin P ⟨s, f, body⟩ c₁ c₂)
    (hk : ¬ ChoiceFam (famOf e)) (hh₁ : Head P s f args₁ e c₀₁) (hh₂ : Head P s f args₂ e c₀₂)
    (hp : args₁ = p ++ args₂) : p = [] ∧ SoftJoin P ⟨s, f, vals args₂ ++ [e]⟩ c₀₁ c₀₂ := by
  by_cases hc : famOf e = .control
  · obtain ⟨hp', hj⟩ := Head.det_ctl_soft hc ih hh₁ hh₂ hp
    exact ⟨hp', SoftJoin.of_join hj⟩
  · obtain ⟨hp', heq⟩ := det_fam_free hc hk hh₁ hh₂ hp
    exact ⟨hp', .inl heq⟩

/-- Two head steps at the same first non-value. -/
theorem head_soft {P : Profile} {s : Store H} {f : Frame} {vs₁ vs₂ args₁ args₂ : List Val}
    {e : Admin} {rest : List Admin} {c₀₁ c₀₂ : Config H}
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf e → Step P noHost ⟨s, f, body⟩ c₁ → Step P noHost ⟨s, f, body⟩ c₂ →
      SoftJoin P ⟨s, f, body⟩ c₁ c₂)
    (hva : vs₁ ++ args₁ = vs₂ ++ args₂)
    (hh₁ : Head P s f args₁ e c₀₁) (hh₂ : Head P s f args₂ e c₀₂) (p : List Val)
    (hp : args₁ = p ++ args₂) :
    SoftJoin P ⟨s, f, vals vs₁ ++ (vals args₁ ++ e :: rest)⟩
      ⟨c₀₁.store, c₀₁.frame, vals vs₁ ++ c₀₁.code ++ rest⟩
      ⟨c₀₂.store, c₀₂.frame, vals vs₂ ++ c₀₂.code ++ rest⟩ := by
  have hcode : vals vs₁ ++ (vals args₁ ++ e :: rest) = vals vs₂ ++ (vals args₂ ++ e :: rest) := by
    rw [← List.append_assoc, ← List.append_assoc, ← vals_append, ← vals_append, hva]
  by_cases hk : ChoiceFam (famOf e)
  · have h₂ : Soft P ⟨s, f, vals vs₁ ++ (vals args₁ ++ e :: rest)⟩
        ⟨c₀₂.store, c₀₂.frame, vals vs₂ ++ c₀₂.code ++ rest⟩ := by
      rw [hcode]
      exact soft_of_head_choice hh₂ hk
    exact .inr ⟨soft_of_head_choice hh₁ hk, h₂⟩
  · obtain ⟨hp', hj⟩ := head_soft_same ih hk hh₁ hh₂ hp
    have hargs : args₁ = args₂ := by simpa [hp'] using hp
    have hvs : vs₁ = vs₂ := List.append_cancel_right (hargs ▸ hva)
    have hj' : SoftJoin P ⟨s, f, vals args₁ ++ [e]⟩ c₀₁ c₀₂ := by rw [hargs]; exact hj
    rw [← hvs]
    exact SoftJoin.instrs hj'

/-- Two head decompositions of steps of the same code. -/
theorem headDec_soft {P : Profile} {s : Store H} {f : Frame} {code : List Admin}
    {c₁ c₂ : Config H}
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf code → Step P noHost ⟨s, f, body⟩ c₁ →
      Step P noHost ⟨s, f, body⟩ c₂ → SoftJoin P ⟨s, f, body⟩ c₁ c₂)
    (hd₁ : HeadDec P s f code c₁) (hd₂ : HeadDec P s f code c₂) :
    SoftJoin P ⟨s, f, code⟩ c₁ c₂ := by
  obtain ⟨vs₁, args₁, e₁, rest₁, c₀₁, hf₁, hc₁, hh₁, hd₁'⟩ := fnv_headDec hd₁
  obtain ⟨vs₂, args₂, e₂, rest₂, c₀₂, hf₂, -, hh₂, hd₂'⟩ := fnv_headDec hd₂
  have hf : vs₁ ++ args₁ = vs₂ ++ args₂ ∧ e₁ = e₂ ∧ rest₁ = rest₂ := by
    simpa only [Prod.mk.injEq, List.cons.injEq] using hf₁.symm.trans hf₂
  obtain ⟨hva, he, hr⟩ := hf
  have hh₂' : Head P s f args₂ e₁ c₀₂ := he ▸ hh₂
  have ih' : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf e₁ → Step P noHost ⟨s, f, body⟩ c₁ → Step P noHost ⟨s, f, body⟩ c₂ →
      SoftJoin P ⟨s, f, body⟩ c₁ c₂ := fun s f body c₁ c₂ hlt =>
    ih s f body c₁ c₂ (lt_of_lt_of_eq (lt_trans hlt sizeOf_lt_code) (congrArg sizeOf hc₁.symm))
  rw [hd₁', hd₂', hc₁, ← hr]
  rcases append_eq_append_suffix hva with ⟨p, hp⟩ | ⟨p, hp⟩
  · exact head_soft ih' hva hh₁ hh₂' p hp
  · show SoftJoin P _ _ _
    have hcode : vals vs₁ ++ (vals args₁ ++ e₁ :: rest₁) =
        vals vs₂ ++ (vals args₂ ++ e₁ :: rest₁) := by
      rw [← List.append_assoc, ← List.append_assoc, ← vals_append, ← vals_append, hva]
    have hj : SoftJoin P ⟨s, f, vals vs₁ ++ (vals args₁ ++ e₁ :: rest₁)⟩
        ⟨c₀₂.store, c₀₂.frame, vals vs₂ ++ c₀₂.code ++ rest₁⟩
        ⟨c₀₁.store, c₀₁.frame, vals vs₁ ++ c₀₁.code ++ rest₁⟩ := by
      rw [hcode]
      exact head_soft ih' hva.symm hh₂' hh₁ p hp
    rcases hj with h | ⟨ha, hb⟩
    · exact .inl h.symm
    · exact .inr ⟨hb, ha⟩

/-- **Determinism up to choices**, by induction on the size of the code. -/
theorem soft_join_aux {P : Profile} :
    ∀ (n : Nat) (s : Store H) (f : Frame) (code : List Admin) (c₁ c₂ : Config H),
      sizeOf code = n → Step P noHost ⟨s, f, code⟩ c₁ → Step P noHost ⟨s, f, code⟩ c₂ →
      SoftJoin P ⟨s, f, code⟩ c₁ c₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s f code c₁ c₂ hn h₁ h₂
  have ih' : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf code → Step P noHost ⟨s, f, body⟩ c₁ →
      Step P noHost ⟨s, f, body⟩ c₂ → SoftJoin P ⟨s, f, body⟩ c₁ c₂ :=
    fun s f body c₁ c₂ hlt => ih _ (hn ▸ hlt) s f body c₁ c₂ rfl
  rcases Step.decomp h₁ with hd₁ | hb₁ <;> rcases Step.decomp h₂ with hd₂ | hb₂
  · exact headDec_soft ih' hd₁ hd₂
  · exact (headDec_bubble_false hd₁ hb₂).elim
  · exact (headDec_bubble_false hd₂ hb₁).elim
  · exact .inr ⟨.bubble hb₁, .bubble hb₂⟩

/-- **Determinism up to choices.** Two host-free steps from the same configuration under an
arbitrary profile have equal results, or both are `Soft`. -/
theorem soft_join {P : Profile} {c c₁ c₂ : Config H} (h₁ : Step P noHost c c₁)
    (h₂ : Step P noHost c c₂) : SoftJoin P c c₁ c₂ := by
  rcases c with ⟨s, f, code⟩
  exact soft_join_aux _ s f code c₁ c₂ rfl h₁ h₂

/-- The form used for backward simulations: a step that is not the given one is `Soft`. -/
theorem eq_or_soft {P : Profile} {c c₁ c₂ : Config H} (h₁ : Step P noHost c c₁)
    (h₂ : Step P noHost c c₂) : c₂ = c₁ ∨ Soft P c c₂ := by
  rcases soft_join h₁ h₂ with h | ⟨-, h⟩
  · exact .inl h.symm
  · exact .inr h

end Silmaril.Proofs.Wasm.Game.Choice
