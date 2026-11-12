module

public import Silmaril.SSA.Isotope.LambdaSSA.Defs
public import Silmaril.Raw.SSA.Isotope.LetSeq.LocallyNameless.Syntax

/-!
# State-threading operational semantics for let-seq

This independent judgment evaluates subterms from left to right, with the newest
bound variable at index zero. Primitive instructions are atomic transitions;
their relation may be nondeterministic or have no result. Evaluation is separate
from typing and purity. Product elimination binds the right component at index zero.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetSeq.Semantics

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}

abbrev FreeEnv (ν : Type v) (α : Type u) := ν → Value α
abbrev BoundEnv (α : Type u) (n : Nat) := Fin n → Value α

/-- Extend an environment with its newest value at index zero. -/
def extend {n : Nat} (bound : BoundEnv α n) (value : Value α) : BoundEnv α (n + 1) :=
  Fin.cases value bound

@[simp] theorem extend_zero {n : Nat} (bound : BoundEnv α n) (value : Value α) :
    extend bound value 0 = value := rfl

@[simp] theorem extend_succ {n : Nat} (bound : BoundEnv α n) (value : Value α) (i : Fin n) :
    extend bound value i.succ = bound i := rfl

/-- Each primitive input and machine state has at most one output and final state. -/
def InstrDeterministic (instr : Φ → Value α → σ → Value α → σ → Prop) : Prop :=
  ∀ f a s b s' c s'', instr f a s b s' → instr f a s c s'' → b = c ∧ s' = s''

/-- Finite, left-to-right evaluation of a term. -/
inductive Eval (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α) :
    {n : Nat} → BoundEnv α n → Tm ν Φ n → σ → Value α → σ → Prop where
  | fv {n : Nat} {bound : BoundEnv α n} {x : ν} {s : σ} :
      Eval instr free bound (.fv x) s (free x) s
  | bv {n : Nat} {bound : BoundEnv α n} {i : Fin n} {s : σ} :
      Eval instr free bound (.bv i) s (bound i) s
  | op {n : Nat} {bound : BoundEnv α n} {f : Φ} {a : Tm ν Φ n}
      {s s₁ s₂ : σ} {va value : Value α}
      (arg : Eval instr free bound a s va s₁) (step : instr f va s₁ value s₂) :
      Eval instr free bound (.op f a) s value s₂
  | let₁ {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
      {s s₁ s₂ : σ} {va value : Value α}
      (arg : Eval instr free bound a s va s₁)
      (body : Eval instr free (extend bound va) b s₁ value s₂) :
      Eval instr free bound (.let₁ a b) s value s₂
  | unit {n : Nat} {bound : BoundEnv α n} {s : σ} :
      Eval instr free bound .unit s .unit s
  | pair {n : Nat} {bound : BoundEnv α n} {a b : Tm ν Φ n}
      {s s₁ s₂ : σ} {va vb : Value α}
      (left : Eval instr free bound a s va s₁) (right : Eval instr free bound b s₁ vb s₂) :
      Eval instr free bound (.pair a b) s (.pair va vb) s₂
  | let₂ {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 2)}
      {s s₁ s₂ : σ} {va vb value : Value α}
      (arg : Eval instr free bound a s (.pair va vb) s₁)
      (body : Eval instr free (extend (extend bound va) vb) b s₁ value s₂) :
      Eval instr free bound (.let₂ a b) s value s₂

variable {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}

theorem Eval.deterministic (hd : InstrDeterministic instr) {n : Nat}
    {bound : BoundEnv α n} {t : Tm ν Φ n} {s s₁ : σ} {v₁ : Value α}
    (h : Eval instr free bound t s v₁ s₁) :
    ∀ {v₂ s₂}, Eval instr free bound t s v₂ s₂ → v₁ = v₂ ∧ s₁ = s₂ := by
  induction h with
  | fv => intro _ _ h'; cases h'; exact ⟨rfl, rfl⟩
  | bv => intro _ _ h'; cases h'; exact ⟨rfl, rfl⟩
  | unit => intro _ _ h'; cases h'; exact ⟨rfl, rfl⟩
  | op arg step ih =>
      intro _ _ h'
      cases h' with
      | op arg' step' =>
          obtain ⟨rfl, rfl⟩ := ih arg'
          exact hd _ _ _ _ _ _ _ step step'
  | let₁ arg body ihArg ihBody =>
      intro _ _ h'
      cases h' with
      | let₁ arg' body' =>
          obtain ⟨rfl, rfl⟩ := ihArg arg'
          exact ihBody body'
  | pair left right ihLeft ihRight =>
      intro _ _ h'
      cases h' with
      | pair left' right' =>
          obtain ⟨rfl, rfl⟩ := ihLeft left'
          obtain ⟨rfl, rfl⟩ := ihRight right'
          exact ⟨rfl, rfl⟩
  | let₂ arg body ihArg ihBody =>
      intro _ _ h'
      cases h' with
      | let₂ arg' body' =>
          obtain ⟨hv, rfl⟩ := ihArg arg'
          obtain ⟨rfl, rfl⟩ := Value.pair.inj hv
          exact ihBody body'

/-- Existence of a finite result, without assuming primitive transitions are total. -/
def Terminates {n : Nat} (instr : Φ → Value α → σ → Value α → σ → Prop)
    (free : FreeEnv ν α) (bound : BoundEnv α n) (t : Tm ν Φ n) (s : σ) : Prop :=
  ∃ value s', Eval instr free bound t s value s'

/-- Absence of a finite result does not by itself assert an infinite computation. -/
def NoResult {n : Nat} (instr : Φ → Value α → σ → Value α → σ → Prop)
    (free : FreeEnv ν α) (bound : BoundEnv α n) (t : Tm ν Φ n) (s : σ) : Prop :=
  ¬ Terminates instr free bound t s

/-- Matching environments continue to match under one common newest binder. -/
theorem extend_rename {n m : Nat} {bound : BoundEnv α n} {target : BoundEnv α m}
    {ρ : Fin n → Fin m} (agree : ∀ i, target (ρ i) = bound i) (value : Value α) :
    ∀ i, extend target value (Tm.up ρ i) = extend bound value i :=
  Fin.cases rfl (fun i => agree i)

/-- Bound renaming preserves both the result and the threaded machine state
when the target environment supplies the same value at every renamed index. -/
theorem Eval.rename {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n}
    {s s' : σ} {value : Value α} (h : Eval instr free bound t s value s') :
    ∀ {m : Nat} (ρ : Fin n → Fin m) (target : BoundEnv α m),
      (∀ i, target (ρ i) = bound i) → Eval instr free target (t.rename ρ) s value s' := by
  induction h with
  | fv => intro _ _ _ _; exact .fv
  | bv => intro _ _ _ agree; exact agree _ ▸ .bv
  | unit => intro _ _ _ _; exact .unit
  | op arg step ih =>
      intro _ ρ target agree
      exact .op (ih ρ target agree) step
  | let₁ arg body ihArg ihBody =>
      intro _ ρ target agree
      exact .let₁ (ihArg ρ target agree) (ihBody (Tm.up ρ) _ (extend_rename agree _))
  | pair left right ihLeft ihRight =>
      intro _ ρ target agree
      exact .pair (ihLeft ρ target agree) (ihRight ρ target agree)
  | let₂ arg body ihArg ihBody =>
      intro _ ρ target agree
      exact .let₂ (ihArg ρ target agree)
        (ihBody (Tm.up (Tm.up ρ)) _ (extend_rename (extend_rename agree _) _))

/-- Renaming also reflects execution when the environments agree at each image. -/
theorem Eval.of_rename {n m : Nat} {bound : BoundEnv α n} {target : BoundEnv α m}
    {ρ : Fin n → Fin m} {t : Tm ν Φ n} {s s' : σ} {value : Value α}
    (agree : ∀ i, target (ρ i) = bound i)
    (h : Eval instr free target (t.rename ρ) s value s') :
    Eval instr free bound t s value s' := by
  induction t generalizing m s s' value with
  | fv x => cases h; exact .fv
  | bv i => cases h; exact agree i ▸ .bv
  | op f a ih =>
      cases h with | op arg step => exact .op (ih agree arg) step
  | let₁ a b iha ihb =>
      cases h with
      | let₁ arg body => exact .let₁ (iha agree arg) (ihb (extend_rename agree _) body)
  | unit => cases h; exact .unit
  | pair a b iha ihb =>
      cases h with | pair left right => exact .pair (iha agree left) (ihb agree right)
  | let₂ a b iha ihb =>
      cases h with
      | let₂ arg body =>
          exact .let₂ (iha agree arg) (ihb (extend_rename (extend_rename agree _) _) body)

theorem Eval.rename_iff {n m : Nat} {bound : BoundEnv α n} {target : BoundEnv α m}
    {ρ : Fin n → Fin m} {t : Tm ν Φ n} {s s' : σ} {value : Value α}
    (agree : ∀ i, target (ρ i) = bound i) :
    Eval instr free target (t.rename ρ) s value s' ↔
      Eval instr free bound t s value s' :=
  ⟨of_rename agree, fun h => h.rename ρ target agree⟩

end Silmaril.Isotope.LetSeq.Semantics
