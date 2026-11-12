module

public import Silmaril.Raw.SSA.Isotope.LetSeq.LocallyNameless.Typing
public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Typing
public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Typing

/-!
# One-hole contexts for raw and exactly typed let syntax

The primitive contexts put a hole in each argument of each constructor, including
binder bodies. Compatibility with these contexts implies compatibility with
arbitrarily nested contexts by repeated application. Typed holes retain their
bound context and result type; a hole cannot change either silently.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Theory

/-- The sort of a typed term: scope, bound-variable types, and result type. -/
structure TypingIndex (τ : Type u) where
  depth : Nat
  bound : BoundCtx τ depth
  result : τ

end Silmaril.Isotope.Theory

namespace Silmaril.Isotope.LetSeq.LocallyNameless

open Silmaril.Isotope.Theory

variable {ν : Type w} {Φ : Type v}

/-- Every constructor argument is a permitted raw hole. -/
inductive RawContext : {n m : Nat} → (Tm ν Φ n → Tm ν Φ m) → Prop where
  | op {n : Nat} (f : Φ) : RawContext (fun a : Tm ν Φ n => .op f a)
  | let₁_left {n : Nat} (b : Tm ν Φ (n + 1)) : RawContext (fun a : Tm ν Φ n => .let₁ a b)
  | let₁_right {n : Nat} (a : Tm ν Φ n) : RawContext (fun b : Tm ν Φ (n + 1) => .let₁ a b)
  | pair_left {n : Nat} (b : Tm ν Φ n) : RawContext (fun a : Tm ν Φ n => .pair a b)
  | pair_right {n : Nat} (a : Tm ν Φ n) : RawContext (fun b : Tm ν Φ n => .pair a b)
  | let₂_left {n : Nat} (b : Tm ν Φ (n + 2)) : RawContext (fun a : Tm ν Φ n => .let₂ a b)
  | let₂_right {n : Nat} (a : Tm ν Φ n) : RawContext (fun b : Tm ν Φ (n + 2) => .let₂ a b)

variable {τ : Type u} [HasProduct τ] [HasUnit τ] [DecidableEq ν] [HasTy Φ τ]

/-- A raw term with exact (proposition-valued) typing evidence. -/
def TypedTerm (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) (i : TypingIndex τ) :=
  {a : Tm ν Φ i.depth // HasType Φ Γ i.bound a i.result}

/-- Every constructor argument is also a permitted typed hole at its exact sort. -/
inductive TypedContext (Γ : Ctx ν τ) : {i j : TypingIndex τ} →
    (TypedTerm Φ Γ i → TypedTerm Φ Γ j) → Prop where
  | op {n : Nat} {β : BoundCtx τ n} {f : Φ}  :
      TypedContext Γ (i := ⟨_, β, instrSrc f⟩) (j := ⟨_, β, instrTrg f⟩)
        (fun x => ⟨.op f x.val, .op x.property⟩)
  | let₁_left {n : Nat} {β : BoundCtx τ n} {A B : τ} (b : TypedTerm Φ Γ (⟨_, (.snoc β A), B⟩)) :
      TypedContext Γ (i := ⟨_, β, A⟩) (j := ⟨_, β, B⟩)
        (fun x => ⟨.let₁ x.val b.val, .let₁ x.property b.property⟩)
  | let₁_right {n : Nat} {β : BoundCtx τ n} {A B : τ} (a : TypedTerm Φ Γ (⟨_, β, A⟩)) :
      TypedContext Γ (i := ⟨_, (.snoc β A), B⟩) (j := ⟨_, β, B⟩)
        (fun x => ⟨.let₁ a.val x.val, .let₁ a.property x.property⟩)
  | pair_left {n : Nat} {β : BoundCtx τ n} {A B : τ} (b : TypedTerm Φ Γ (⟨_, β, B⟩)) :
      TypedContext Γ (i := ⟨_, β, A⟩) (j := ⟨_, β, product A B⟩)
        (fun x => ⟨.pair x.val b.val, .pair x.property b.property⟩)
  | pair_right {n : Nat} {β : BoundCtx τ n} {A B : τ} (a : TypedTerm Φ Γ (⟨_, β, A⟩)) :
      TypedContext Γ (i := ⟨_, β, B⟩) (j := ⟨_, β, product A B⟩)
        (fun x => ⟨.pair a.val x.val, .pair a.property x.property⟩)
  | let₂_left {n : Nat} {β : BoundCtx τ n} {A B C : τ} (b : TypedTerm Φ Γ (⟨_, (.snoc (.snoc β A) B), C⟩)) :
      TypedContext Γ (i := ⟨_, β, product A B⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.let₂ x.val b.val, .let₂ x.property b.property⟩)
  | let₂_right {n : Nat} {β : BoundCtx τ n} {A B C : τ} (a : TypedTerm Φ Γ (⟨_, β, product A B⟩)) :
      TypedContext Γ (i := ⟨_, (.snoc (.snoc β A) B), C⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.let₂ a.val x.val, .let₂ a.property x.property⟩)

end Silmaril.Isotope.LetSeq.LocallyNameless

namespace Silmaril.Isotope.LetCase.LocallyNameless

open Silmaril.Isotope.Theory

variable {ν : Type w} {Φ : Type v}

/-- Every constructor argument is a permitted raw hole. -/
inductive RawContext : {n m : Nat} → (Tm ν Φ n → Tm ν Φ m) → Prop where
  | op {n : Nat} (f : Φ) : RawContext (fun a : Tm ν Φ n => .op f a)
  | let₁_left {n : Nat} (b : Tm ν Φ (n + 1)) : RawContext (fun a : Tm ν Φ n => .let₁ a b)
  | let₁_right {n : Nat} (a : Tm ν Φ n) : RawContext (fun b : Tm ν Φ (n + 1) => .let₁ a b)
  | pair_left {n : Nat} (b : Tm ν Φ n) : RawContext (fun a : Tm ν Φ n => .pair a b)
  | pair_right {n : Nat} (a : Tm ν Φ n) : RawContext (fun b : Tm ν Φ n => .pair a b)
  | let₂_left {n : Nat} (b : Tm ν Φ (n + 2)) : RawContext (fun a : Tm ν Φ n => .let₂ a b)
  | let₂_right {n : Nat} (a : Tm ν Φ n) : RawContext (fun b : Tm ν Φ (n + 2) => .let₂ a b)
  | inl {n : Nat}  : RawContext (fun a : Tm ν Φ n => .inl a)
  | inr {n : Nat}  : RawContext (fun a : Tm ν Φ n => .inr a)
  | case_scrutinee {n : Nat} (l r : Tm ν Φ (n + 1)) : RawContext (fun e : Tm ν Φ n => .case e l r)
  | case_left {n : Nat} (e : Tm ν Φ n) (r : Tm ν Φ (n + 1)) : RawContext (fun l : Tm ν Φ (n + 1) => .case e l r)
  | case_right {n : Nat} (e : Tm ν Φ n) (l : Tm ν Φ (n + 1)) : RawContext (fun r : Tm ν Φ (n + 1) => .case e l r)
  | abort {n : Nat}  : RawContext (fun a : Tm ν Φ n => .abort a)

variable {τ : Type u} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]

/-- A raw term with exact (proposition-valued) typing evidence. -/
def TypedTerm (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) (i : TypingIndex τ) :=
  {a : Tm ν Φ i.depth // HasType Φ Γ i.bound a i.result}

/-- Every constructor argument is also a permitted typed hole at its exact sort. -/
inductive TypedContext (Γ : Ctx ν τ) : {i j : TypingIndex τ} →
    (TypedTerm Φ Γ i → TypedTerm Φ Γ j) → Prop where
  | op {n : Nat} {β : BoundCtx τ n} {f : Φ}  :
      TypedContext Γ (i := ⟨_, β, instrSrc f⟩) (j := ⟨_, β, instrTrg f⟩)
        (fun x => ⟨.op f x.val, .op x.property⟩)
  | let₁_left {n : Nat} {β : BoundCtx τ n} {A B : τ} (b : TypedTerm Φ Γ (⟨_, (.snoc β A), B⟩)) :
      TypedContext Γ (i := ⟨_, β, A⟩) (j := ⟨_, β, B⟩)
        (fun x => ⟨.let₁ x.val b.val, .let₁ x.property b.property⟩)
  | let₁_right {n : Nat} {β : BoundCtx τ n} {A B : τ} (a : TypedTerm Φ Γ (⟨_, β, A⟩)) :
      TypedContext Γ (i := ⟨_, (.snoc β A), B⟩) (j := ⟨_, β, B⟩)
        (fun x => ⟨.let₁ a.val x.val, .let₁ a.property x.property⟩)
  | pair_left {n : Nat} {β : BoundCtx τ n} {A B : τ} (b : TypedTerm Φ Γ (⟨_, β, B⟩)) :
      TypedContext Γ (i := ⟨_, β, A⟩) (j := ⟨_, β, product A B⟩)
        (fun x => ⟨.pair x.val b.val, .pair x.property b.property⟩)
  | pair_right {n : Nat} {β : BoundCtx τ n} {A B : τ} (a : TypedTerm Φ Γ (⟨_, β, A⟩)) :
      TypedContext Γ (i := ⟨_, β, B⟩) (j := ⟨_, β, product A B⟩)
        (fun x => ⟨.pair a.val x.val, .pair a.property x.property⟩)
  | let₂_left {n : Nat} {β : BoundCtx τ n} {A B C : τ} (b : TypedTerm Φ Γ (⟨_, (.snoc (.snoc β A) B), C⟩)) :
      TypedContext Γ (i := ⟨_, β, product A B⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.let₂ x.val b.val, .let₂ x.property b.property⟩)
  | let₂_right {n : Nat} {β : BoundCtx τ n} {A B C : τ} (a : TypedTerm Φ Γ (⟨_, β, product A B⟩)) :
      TypedContext Γ (i := ⟨_, (.snoc (.snoc β A) B), C⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.let₂ a.val x.val, .let₂ a.property x.property⟩)
  | inl {n : Nat} {β : BoundCtx τ n} {A B : τ}  :
      TypedContext Γ (i := ⟨_, β, A⟩) (j := ⟨_, β, coprod A B⟩)
        (fun x => ⟨.inl x.val, .inl x.property⟩)
  | inr {n : Nat} {β : BoundCtx τ n} {A B : τ}  :
      TypedContext Γ (i := ⟨_, β, B⟩) (j := ⟨_, β, coprod A B⟩)
        (fun x => ⟨.inr x.val, .inr x.property⟩)
  | case_scrutinee {n : Nat} {β : BoundCtx τ n} {A B C : τ} (l : TypedTerm Φ Γ (⟨_, (.snoc β A), C⟩)) (r : TypedTerm Φ Γ (⟨_, (.snoc β B), C⟩)) :
      TypedContext Γ (i := ⟨_, β, coprod A B⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.case x.val l.val r.val, .case x.property l.property r.property⟩)
  | case_left {n : Nat} {β : BoundCtx τ n} {A B C : τ} (e : TypedTerm Φ Γ (⟨_, β, coprod A B⟩)) (r : TypedTerm Φ Γ (⟨_, (.snoc β B), C⟩)) :
      TypedContext Γ (i := ⟨_, (.snoc β A), C⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.case e.val x.val r.val, .case e.property x.property r.property⟩)
  | case_right {n : Nat} {β : BoundCtx τ n} {A B C : τ} (e : TypedTerm Φ Γ (⟨_, β, coprod A B⟩)) (l : TypedTerm Φ Γ (⟨_, (.snoc β A), C⟩)) :
      TypedContext Γ (i := ⟨_, (.snoc β B), C⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.case e.val l.val x.val, .case e.property l.property x.property⟩)
  | abort {n : Nat} {β : BoundCtx τ n} {C : τ}  :
      TypedContext Γ (i := ⟨_, β, Silmaril.empty⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.abort x.val, .abort x.property⟩)

end Silmaril.Isotope.LetCase.LocallyNameless

namespace Silmaril.Isotope.LetIter.LocallyNameless

open Silmaril.Isotope.Theory

variable {ν : Type w} {Φ : Type v}

/-- Every constructor argument is a permitted raw hole. -/
inductive RawContext : {n m : Nat} → (Tm ν Φ n → Tm ν Φ m) → Prop where
  | op {n : Nat} (f : Φ) : RawContext (fun a : Tm ν Φ n => .op f a)
  | let₁_left {n : Nat} (b : Tm ν Φ (n + 1)) : RawContext (fun a : Tm ν Φ n => .let₁ a b)
  | let₁_right {n : Nat} (a : Tm ν Φ n) : RawContext (fun b : Tm ν Φ (n + 1) => .let₁ a b)
  | pair_left {n : Nat} (b : Tm ν Φ n) : RawContext (fun a : Tm ν Φ n => .pair a b)
  | pair_right {n : Nat} (a : Tm ν Φ n) : RawContext (fun b : Tm ν Φ n => .pair a b)
  | let₂_left {n : Nat} (b : Tm ν Φ (n + 2)) : RawContext (fun a : Tm ν Φ n => .let₂ a b)
  | let₂_right {n : Nat} (a : Tm ν Φ n) : RawContext (fun b : Tm ν Φ (n + 2) => .let₂ a b)
  | inl {n : Nat}  : RawContext (fun a : Tm ν Φ n => .inl a)
  | inr {n : Nat}  : RawContext (fun a : Tm ν Φ n => .inr a)
  | case_scrutinee {n : Nat} (l r : Tm ν Φ (n + 1)) : RawContext (fun e : Tm ν Φ n => .case e l r)
  | case_left {n : Nat} (e : Tm ν Φ n) (r : Tm ν Φ (n + 1)) : RawContext (fun l : Tm ν Φ (n + 1) => .case e l r)
  | case_right {n : Nat} (e : Tm ν Φ n) (l : Tm ν Φ (n + 1)) : RawContext (fun r : Tm ν Φ (n + 1) => .case e l r)
  | abort {n : Nat}  : RawContext (fun a : Tm ν Φ n => .abort a)
  | iter_left {n : Nat} (b : Tm ν Φ (n + 1)) : RawContext (fun a : Tm ν Φ n => .iter a b)
  | iter_right {n : Nat} (a : Tm ν Φ n) : RawContext (fun b : Tm ν Φ (n + 1) => .iter a b)

variable {τ : Type u} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]

/-- A raw term with exact (proposition-valued) typing evidence. -/
def TypedTerm (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) (i : TypingIndex τ) :=
  {a : Tm ν Φ i.depth // HasType Φ Γ i.bound a i.result}

/-- Every constructor argument is also a permitted typed hole at its exact sort. -/
inductive TypedContext (Γ : Ctx ν τ) : {i j : TypingIndex τ} →
    (TypedTerm Φ Γ i → TypedTerm Φ Γ j) → Prop where
  | op {n : Nat} {β : BoundCtx τ n} {f : Φ}  :
      TypedContext Γ (i := ⟨_, β, instrSrc f⟩) (j := ⟨_, β, instrTrg f⟩)
        (fun x => ⟨.op f x.val, .op x.property⟩)
  | let₁_left {n : Nat} {β : BoundCtx τ n} {A B : τ} (b : TypedTerm Φ Γ (⟨_, (.snoc β A), B⟩)) :
      TypedContext Γ (i := ⟨_, β, A⟩) (j := ⟨_, β, B⟩)
        (fun x => ⟨.let₁ x.val b.val, .let₁ x.property b.property⟩)
  | let₁_right {n : Nat} {β : BoundCtx τ n} {A B : τ} (a : TypedTerm Φ Γ (⟨_, β, A⟩)) :
      TypedContext Γ (i := ⟨_, (.snoc β A), B⟩) (j := ⟨_, β, B⟩)
        (fun x => ⟨.let₁ a.val x.val, .let₁ a.property x.property⟩)
  | pair_left {n : Nat} {β : BoundCtx τ n} {A B : τ} (b : TypedTerm Φ Γ (⟨_, β, B⟩)) :
      TypedContext Γ (i := ⟨_, β, A⟩) (j := ⟨_, β, product A B⟩)
        (fun x => ⟨.pair x.val b.val, .pair x.property b.property⟩)
  | pair_right {n : Nat} {β : BoundCtx τ n} {A B : τ} (a : TypedTerm Φ Γ (⟨_, β, A⟩)) :
      TypedContext Γ (i := ⟨_, β, B⟩) (j := ⟨_, β, product A B⟩)
        (fun x => ⟨.pair a.val x.val, .pair a.property x.property⟩)
  | let₂_left {n : Nat} {β : BoundCtx τ n} {A B C : τ} (b : TypedTerm Φ Γ (⟨_, (.snoc (.snoc β A) B), C⟩)) :
      TypedContext Γ (i := ⟨_, β, product A B⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.let₂ x.val b.val, .let₂ x.property b.property⟩)
  | let₂_right {n : Nat} {β : BoundCtx τ n} {A B C : τ} (a : TypedTerm Φ Γ (⟨_, β, product A B⟩)) :
      TypedContext Γ (i := ⟨_, (.snoc (.snoc β A) B), C⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.let₂ a.val x.val, .let₂ a.property x.property⟩)
  | inl {n : Nat} {β : BoundCtx τ n} {A B : τ}  :
      TypedContext Γ (i := ⟨_, β, A⟩) (j := ⟨_, β, coprod A B⟩)
        (fun x => ⟨.inl x.val, .inl x.property⟩)
  | inr {n : Nat} {β : BoundCtx τ n} {A B : τ}  :
      TypedContext Γ (i := ⟨_, β, B⟩) (j := ⟨_, β, coprod A B⟩)
        (fun x => ⟨.inr x.val, .inr x.property⟩)
  | case_scrutinee {n : Nat} {β : BoundCtx τ n} {A B C : τ} (l : TypedTerm Φ Γ (⟨_, (.snoc β A), C⟩)) (r : TypedTerm Φ Γ (⟨_, (.snoc β B), C⟩)) :
      TypedContext Γ (i := ⟨_, β, coprod A B⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.case x.val l.val r.val, .case x.property l.property r.property⟩)
  | case_left {n : Nat} {β : BoundCtx τ n} {A B C : τ} (e : TypedTerm Φ Γ (⟨_, β, coprod A B⟩)) (r : TypedTerm Φ Γ (⟨_, (.snoc β B), C⟩)) :
      TypedContext Γ (i := ⟨_, (.snoc β A), C⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.case e.val x.val r.val, .case e.property x.property r.property⟩)
  | case_right {n : Nat} {β : BoundCtx τ n} {A B C : τ} (e : TypedTerm Φ Γ (⟨_, β, coprod A B⟩)) (l : TypedTerm Φ Γ (⟨_, (.snoc β A), C⟩)) :
      TypedContext Γ (i := ⟨_, (.snoc β B), C⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.case e.val l.val x.val, .case e.property l.property x.property⟩)
  | abort {n : Nat} {β : BoundCtx τ n} {C : τ}  :
      TypedContext Γ (i := ⟨_, β, Silmaril.empty⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.abort x.val, .abort x.property⟩)
  | iter_left {n : Nat} {β : BoundCtx τ n} {A B : τ} (b : TypedTerm Φ Γ (⟨_, (.snoc β A), coprod B A⟩)) :
      TypedContext Γ (i := ⟨_, β, A⟩) (j := ⟨_, β, B⟩)
        (fun x => ⟨.iter x.val b.val, .iter x.property b.property⟩)
  | iter_right {n : Nat} {β : BoundCtx τ n} {A B : τ} (a : TypedTerm Φ Γ (⟨_, β, A⟩)) :
      TypedContext Γ (i := ⟨_, (.snoc β A), coprod B A⟩) (j := ⟨_, β, B⟩)
        (fun x => ⟨.iter a.val x.val, .iter a.property x.property⟩)

end Silmaril.Isotope.LetIter.LocallyNameless

