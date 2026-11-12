module

public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Typing

/-!
# Data-valued exact typing

These coercion-free derivations present the proposition-valued typing judgment
as data. Their existence is equivalent to exact typing. Interpretation can
recurse on the data without selecting an arbitrary subtype derivation.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]

/-- Exact typing evidence, with no coercion constructor. -/
inductive Derivation (Φ : Type v) [HasTy Φ τ] (Γ : Isotope.Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm ν Φ n → τ → Type (max u v w) where
  | fv {n : Nat} {β : BoundCtx τ n} {x : ν} {A : τ}
      (h : Γ.lookup x = some A) : Derivation Φ Γ β (.fv x) A
  | bv {n : Nat} {β : BoundCtx τ n} {ι : Fin n} :
      Derivation Φ Γ β (.bv ι) (β.get ι)
  | op {n : Nat} {β : BoundCtx τ n} {f : Φ} {a : Tm ν Φ n}
      (ha : Derivation Φ Γ β a (instrSrc f)) : Derivation Φ Γ β (.op f a) (instrTrg f)
  | let₁ {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
      (ha : Derivation Φ Γ β a A) (hb : Derivation Φ Γ (.snoc β A) b B) :
      Derivation Φ Γ β (.let₁ a b) B
  | unit {n : Nat} {β : BoundCtx τ n} : Derivation Φ Γ β .unit Silmaril.unit
  | pair {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A B : τ}
      (ha : Derivation Φ Γ β a A) (hb : Derivation Φ Γ β b B) :
      Derivation Φ Γ β (.pair a b) (Silmaril.product A B)
  | let₂ {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {c : Tm ν Φ (n + 2)} {A B C : τ}
      (ha : Derivation Φ Γ β a (Silmaril.product A B))
      (hc : Derivation Φ Γ (.snoc (.snoc β A) B) c C) : Derivation Φ Γ β (.let₂ a c) C
  | inl {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A B : τ}
      (ha : Derivation Φ Γ β a A) : Derivation Φ Γ β (.inl a) (Silmaril.coprod A B)
  | inr {n : Nat} {β : BoundCtx τ n} {b : Tm ν Φ n} {A B : τ}
      (hb : Derivation Φ Γ β b B) : Derivation Φ Γ β (.inr b) (Silmaril.coprod A B)
  | case {n : Nat} {β : BoundCtx τ n} {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B C : τ}
      (he : Derivation Φ Γ β e (Silmaril.coprod A B))
      (hl : Derivation Φ Γ (.snoc β A) l C)
      (hr : Derivation Φ Γ (.snoc β B) r C) : Derivation Φ Γ β (.case e l r) C
  | abort {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {C : τ}
      (ha : Derivation Φ Γ β a Silmaril.empty) : Derivation Φ Γ β (.abort a) C
  | iter {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
      (ha : Derivation Φ Γ β a A)
      (hb : Derivation Φ Γ (.snoc β A) b (Silmaril.coprod B A)) :
      Derivation Φ Γ β (.iter a b) B


namespace Derivation

variable {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ} {n : Nat}
  {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}

/-- Forget the data while retaining its exact typing judgment. -/
theorem toHasType (d : Derivation Φ Γ β t A) : HasType Φ Γ β t A := by
  induction d with
  | fv h => exact .fv h
  | bv => exact .bv
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih
  | iter _ _ iha ihb => exact .iter iha ihb

/-- Every exact typing proof admits coercion-free derivation data. -/
theorem ofHasType (h : HasType Φ Γ β t A) : Nonempty (Derivation Φ Γ β t A) := by
  induction h with
  | fv h => exact ⟨.fv h⟩
  | bv => exact ⟨.bv⟩
  | op _ ih => exact ih.map Derivation.op
  | let₁ _ _ iha ihb => rcases iha with ⟨ha⟩; rcases ihb with ⟨hb⟩; exact ⟨.let₁ ha hb⟩
  | unit => exact ⟨.unit⟩
  | pair _ _ iha ihb => rcases iha with ⟨ha⟩; rcases ihb with ⟨hb⟩; exact ⟨.pair ha hb⟩
  | let₂ _ _ iha ihb => rcases iha with ⟨ha⟩; rcases ihb with ⟨hb⟩; exact ⟨.let₂ ha hb⟩
  | inl _ ih => exact ih.map Derivation.inl
  | inr _ ih => exact ih.map Derivation.inr
  | case _ _ _ ihe ihl ihr => rcases ihe with ⟨he⟩; rcases ihl with ⟨hl⟩; rcases ihr with ⟨hr⟩; exact ⟨.case he hl hr⟩
  | abort _ ih => exact ih.map Derivation.abort
  | iter _ _ iha ihb => rcases iha with ⟨ha⟩; rcases ihb with ⟨hb⟩; exact ⟨.iter ha hb⟩

@[simp] theorem nonempty_iff : Nonempty (Derivation Φ Γ β t A) ↔ HasType Φ Γ β t A :=
  ⟨fun ⟨d⟩ => d.toHasType, ofHasType⟩

end Derivation
end Silmaril.Isotope.LetIter.LocallyNameless
