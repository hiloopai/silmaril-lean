module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Machine

/-!
# Finite machine and evaluation agreement

A semantic continuation describes the remaining finite computation. Pulling
this interpretation back along a single machine step proves that machine runs
cannot introduce finite results absent from the original evaluation judgment.
Neither direction assumes instruction determinism or well-typed terms.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics.Machine

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}

/-- The finite meaning of a saved continuation, using the original evaluation relations. -/
inductive KontEval (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α) :
    Kont α ν Φ → Value α → σ → Value α → σ → Prop where
  | halt (v : Value α) (s : σ) : KontEval instr free .halt v s v s
  | op {f : Φ} {k : Kont α ν Φ} {a b v : Value α} {s s₁ s₂ : σ}
      (step : instr f a s b s₁) (next : KontEval instr free k b s₁ v s₂) :
      KontEval instr free (.op f k) a s v s₂
  | let₁ {n} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)} {k : Kont α ν Φ}
      {a b v : Value α} {s s₁ s₂ : σ}
      (bodyEval : Eval instr free (extend bound a) body s b s₁)
      (next : KontEval instr free k b s₁ v s₂) :
      KontEval instr free (.let₁ bound body k) a s v s₂
  | pairLeft {n} {bound : BoundEnv α n} {right : Tm ν Φ n} {k : Kont α ν Φ}
      {a b v : Value α} {s s₁ s₂ : σ}
      (rightEval : Eval instr free bound right s b s₁)
      (next : KontEval instr free k (.pair a b) s₁ v s₂) :
      KontEval instr free (.pairLeft bound right k) a s v s₂
  | pairRight {k : Kont α ν Φ} {a b v : Value α} {s s' : σ}
      (next : KontEval instr free k (.pair a b) s v s') :
      KontEval instr free (.pairRight a k) b s v s'
  | let₂ {n} {bound : BoundEnv α n} {body : Tm ν Φ (n + 2)} {k : Kont α ν Φ}
      {a b c v : Value α} {s s₁ s₂ : σ}
      (bodyEval : Eval instr free (extend (extend bound a) b) body s c s₁)
      (next : KontEval instr free k c s₁ v s₂) :
      KontEval instr free (.let₂ bound body k) (.pair a b) s v s₂
  | inl {k : Kont α ν Φ} {a v : Value α} {s s' : σ}
      (next : KontEval instr free k (.inl a) s v s') :
      KontEval instr free (.inl k) a s v s'
  | inr {k : Kont α ν Φ} {a v : Value α} {s s' : σ}
      (next : KontEval instr free k (.inr a) s v s') :
      KontEval instr free (.inr k) a s v s'
  | caseLeft {n} {bound : BoundEnv α n} {left right : Tm ν Φ (n + 1)} {k : Kont α ν Φ}
      {a b v : Value α} {s s₁ s₂ : σ}
      (branch : Eval instr free (extend bound a) left s b s₁)
      (next : KontEval instr free k b s₁ v s₂) :
      KontEval instr free (.case bound left right k) (.inl a) s v s₂
  | caseRight {n} {bound : BoundEnv α n} {left right : Tm ν Φ (n + 1)} {k : Kont α ν Φ}
      {a b v : Value α} {s s₁ s₂ : σ}
      (branch : Eval instr free (extend bound a) right s b s₁)
      (next : KontEval instr free k b s₁ v s₂) :
      KontEval instr free (.case bound left right k) (.inr a) s v s₂
  | iterInit {n} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)} {k : Kont α ν Φ}
      {a b v : Value α} {s s₁ s₂ : σ}
      (loopEval : Loop instr free bound body a s b s₁)
      (next : KontEval instr free k b s₁ v s₂) :
      KontEval instr free (.iterInit bound body k) a s v s₂
  | exit {n} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)} {k : Kont α ν Φ}
      {a v : Value α} {s s' : σ}
      (next : KontEval instr free k a s v s') :
      KontEval instr free (.iterBody bound body k) (.inl a) s v s'
  | «continue» {n} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)} {k : Kont α ν Φ}
      {a b v : Value α} {s s₁ s₂ : σ}
      (loopEval : Loop instr free bound body a s b s₁)
      (next : KontEval instr free k b s₁ v s₂) :
      KontEval instr free (.iterBody bound body k) (.inr a) s v s₂

/-- Interpretation of an entire machine configuration as a finite computation. -/
def Finishes (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α)
    (c : Config α ν Φ σ) (value : Value α) (final : σ) : Prop :=
  match c with
  | .eval bound t k s => ∃ v s', Eval instr free bound t s v s' ∧ KontEval instr free k v s' value final
  | .ret v k s => KontEval instr free k v s value final
  | .loop bound body current k s =>
      ∃ v s', Loop instr free bound body current s v s' ∧ KontEval instr free k v s' value final

variable {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}

/-- Every machine step preserves the finite meaning when read backwards. -/
theorem Step.finishes {a b : Config α ν Φ σ} (h : Step instr free a b)
    {value : Value α} {final : σ} (hb : Finishes instr free b value final) :
    Finishes instr free a value final := by
  cases h with
  | fv => exact ⟨_, _, .fv, hb⟩
  | bv => exact ⟨_, _, .bv, hb⟩
  | unit => exact ⟨_, _, .unit, hb⟩
  | op =>
      obtain ⟨_, _, arg, hk⟩ := hb
      cases hk with
      | op step next => exact ⟨_, _, .op arg step, next⟩
  | apply _ step => exact .op step hb
  | let₁ =>
      obtain ⟨_, _, arg, hk⟩ := hb
      cases hk with
      | let₁ body next => exact ⟨_, _, .let₁ arg body, next⟩
  | bind₁ =>
      obtain ⟨_, _, body, next⟩ := hb
      exact .let₁ body next
  | pair =>
      obtain ⟨_, _, left, hk⟩ := hb
      cases hk with
      | pairLeft right next => exact ⟨_, _, .pair left right, next⟩
  | pairLeft =>
      obtain ⟨_, _, right, hk⟩ := hb
      cases hk with
      | pairRight next => exact .pairLeft right next
  | pairRight => exact .pairRight hb
  | let₂ =>
      obtain ⟨_, _, arg, hk⟩ := hb
      cases hk with
      | let₂ body next => exact ⟨_, _, .let₂ arg body, next⟩
  | bind₂ =>
      obtain ⟨_, _, body, next⟩ := hb
      exact .let₂ body next
  | inl =>
      obtain ⟨_, _, arg, hk⟩ := hb
      cases hk with
      | inl next => exact ⟨_, _, .inl arg, next⟩
  | injectLeft => exact .inl hb
  | inr =>
      obtain ⟨_, _, arg, hk⟩ := hb
      cases hk with
      | inr next => exact ⟨_, _, .inr arg, next⟩
  | injectRight => exact .inr hb
  | case =>
      obtain ⟨_, _, arg, hk⟩ := hb
      cases hk with
      | caseLeft branch next => exact ⟨_, _, .case_inl arg branch, next⟩
      | caseRight branch next => exact ⟨_, _, .case_inr arg branch, next⟩
  | caseLeft =>
      obtain ⟨_, _, branch, next⟩ := hb
      exact .caseLeft branch next
  | caseRight =>
      obtain ⟨_, _, branch, next⟩ := hb
      exact .caseRight branch next
  | abort =>
      obtain ⟨_, _, _, hk⟩ := hb
      cases hk
  | iter =>
      obtain ⟨_, _, init, hk⟩ := hb
      cases hk with
      | iterInit loop next => exact ⟨_, _, .iter init loop, next⟩
  | initialized =>
      obtain ⟨_, _, loop, next⟩ := hb
      exact .iterInit loop next
  | loop =>
      obtain ⟨_, _, body, hk⟩ := hb
      cases hk with
      | exit next => exact ⟨_, _, .done body, next⟩
      | «continue» loop next => exact ⟨_, _, .step body loop, next⟩
  | exit => exact .exit hb
  | «continue» =>
      obtain ⟨_, _, loop, next⟩ := hb
      exact .continue loop next

theorem Steps.finishes {a b : Config α ν Φ σ} (h : Steps instr free a b)
    {value : Value α} {final : σ} (hb : Finishes instr free b value final) :
    Finishes instr free a value final := by
  induction h with
  | refl => exact hb
  | cons step tail ih => exact step.finishes (ih hb)

/-- Finite machine runs agree exactly with the original term semantics. -/
theorem eval_iff_steps {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n}
    {s s' : σ} {value : Value α} :
    Eval instr free bound t s value s' ↔
      Steps instr free (.eval bound t .halt s) (.ret value .halt s') := by
  constructor
  · intro h; exact eval_steps h .halt
  · intro h
    obtain ⟨_, _, he, hk⟩ := h.finishes (KontEval.halt value s')
    cases hk
    exact he

/-- The same agreement holds for a loop after its initializer. -/
theorem loop_iff_steps {n : Nat} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)}
    {current value : Value α} {s s' : σ} :
    Loop instr free bound body current s value s' ↔
      Steps instr free (.loop bound body current .halt s) (.ret value .halt s') := by
  constructor
  · intro h; exact loop_steps h .halt
  · intro h
    obtain ⟨_, _, he, hk⟩ := h.finishes (KontEval.halt value s')
    cases hk
    exact he

end Silmaril.Isotope.LetIter.Semantics.Machine
