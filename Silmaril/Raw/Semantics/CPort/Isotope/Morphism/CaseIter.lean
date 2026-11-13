module

public import Silmaril.Semantics.CPort.Isotope.LetCase.LocallyNameless.Typing.Defs
public import Silmaril.Semantics.CPort.Isotope.LetCase.LocallyNameless.Purity.Defs
public import Silmaril.Semantics.CPort.Isotope.LetIter.LocallyNameless.Typing.Defs
/-! Constructor-preserving inclusion from LetCase into LetIter. -/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.Morphism.CaseIter

open LetCase.LocallyNameless

variable {ν : Type u} {Φ : Type v} {n m : Nat}

/-- Include the smaller calculus without changing names or binder indices. -/
def embed {n : Nat} : Tm ν Φ n → LetIter.LocallyNameless.Tm ν Φ n
  | .fv x => .fv x
  | .bv i => .bv i
  | .op f a => .op f (embed a)
  | .let₁ a b => .let₁ (embed a) (embed b)
  | .unit => .unit
  | .pair a b => .pair (embed a) (embed b)
  | .let₂ a b => .let₂ (embed a) (embed b)
  | .inl a => .inl (embed a)
  | .inr a => .inr (embed a)
  | .case e l r => .case (embed e) (embed l) (embed r)
  | .abort a => .abort (embed a)

/-- Recognize terms using only constructors of the smaller calculus. -/
def project {n : Nat} : LetIter.LocallyNameless.Tm ν Φ n → Option (Tm ν Φ n)
  | .fv x => some (.fv x)
  | .bv i => some (.bv i)
  | .op f a => return .op f (← project a)
  | .let₁ a b => return .let₁ (← project a) (← project b)
  | .unit => some .unit
  | .pair a b => return .pair (← project a) (← project b)
  | .let₂ a b => return .let₂ (← project a) (← project b)
  | .inl a => return .inl (← project a)
  | .inr a => return .inr (← project a)
  | .case e l r => return .case (← project e) (← project l) (← project r)
  | .abort a => return .abort (← project a)
  | .iter _ _ => none

@[simp] theorem project_embed (t : Tm ν Φ n) : project (embed t) = some t := by
  induction t <;> simp [embed, project, *]

theorem embed_injective : Function.Injective (embed : Tm ν Φ n → _) := by
  intro a b h
  exact Option.some.inj (by simpa only [project_embed] using congrArg project h)

@[simp] theorem embed_rename (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    embed (Tm.rename ρ t) = LetIter.LocallyNameless.Tm.rename ρ (embed t) := by
  induction t generalizing m <;> simp [Tm.rename, embed, LetIter.LocallyNameless.Tm.rename, *]
  all_goals first | rfl | exact ⟨rfl, rfl⟩

@[simp] theorem embed_lift (t : Tm ν Φ n) :
    embed t.lift = LetIter.LocallyNameless.Tm.lift (embed t) := embed_rename _ _

@[simp] theorem embed_underBinder (t : Tm ν Φ (n + 1)) :
    embed t.underBinder = LetIter.LocallyNameless.Tm.underBinder (embed t) := embed_rename _ _

@[simp] theorem embed_underTwoBinders (t : Tm ν Φ (n + 2)) :
    embed t.underTwoBinders = LetIter.LocallyNameless.Tm.underTwoBinders (embed t) := embed_rename _ _

theorem embed_upSub (σ : Fin n → Tm ν Φ m) :
    (fun i => embed (Tm.upSub σ i)) = LetIter.LocallyNameless.Tm.upSub (fun i => embed (σ i)) := by
  funext i
  exact Fin.cases rfl (fun j => embed_lift (σ j)) i

@[simp] theorem embed_bsubst (σ : Fin n → Tm ν Φ m) (t : Tm ν Φ n) :
    embed (Tm.bsubst σ t) = LetIter.LocallyNameless.Tm.bsubst (fun i => embed (σ i)) (embed t) := by
  induction t generalizing m <;> simp [Tm.bsubst, embed, LetIter.LocallyNameless.Tm.bsubst, embed_upSub, *]

@[simp] theorem embed_instantiate (b : Tm ν Φ (n + 1)) (a : Tm ν Φ n) :
    embed (Tm.instantiate b a) = LetIter.LocallyNameless.Tm.instantiate (embed b) (embed a) := by
  rw [Tm.instantiate, embed_bsubst, LetIter.LocallyNameless.Tm.instantiate]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem embed_fsubst [DecidableEq ν] (x : ν) (s t : Tm ν Φ n) :
    embed (Tm.fsubst x s t) = LetIter.LocallyNameless.Tm.fsubst x (embed s) (embed t) := by
  induction t with
  | fv y => by_cases h : x = y <;> simp [Tm.fsubst, embed, h]
  | bv i => rfl
  | unit => rfl
  | op _ _ ih => simp [Tm.fsubst, embed, LetIter.LocallyNameless.Tm.fsubst, ih]
  | let₁ _ _ iha ihb => simp [Tm.fsubst, embed, LetIter.LocallyNameless.Tm.fsubst, iha, ihb]
  | pair _ _ iha ihb => simp [Tm.fsubst, embed, LetIter.LocallyNameless.Tm.fsubst, iha, ihb]
  | let₂ _ _ iha ihb => simp [Tm.fsubst, embed, LetIter.LocallyNameless.Tm.fsubst, iha, ihb]
  | inl _ ih | inr _ ih | abort _ ih => simp [Tm.fsubst, embed, LetIter.LocallyNameless.Tm.fsubst, ih]
  | case _ _ _ ihe ihl ihr => simp [Tm.fsubst, embed, LetIter.LocallyNameless.Tm.fsubst, ihe, ihl, ihr]

/-- Inclusion preserves exact typing over the same contexts and type operations. -/
theorem embed_hasType {τ : Type w} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]
    {Γ : Ctx ν τ} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) : LetIter.LocallyNameless.HasType Φ Γ β (embed t) A := by
  induction h with
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

/-- Inclusion preserves the independently chosen primitive purity predicate. -/
theorem embed_pure {ε : Type r} [HasEff Φ ε] {pureEff : ε} {t : Tm ν Φ n}
    (h : Pure pureEff t) : LetIter.LocallyNameless.Pure pureEff (embed t) := by
  induction h with
  | fv => exact .fv
  | bv => exact .bv
  | op hf _ ih => exact .op hf ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih

end Silmaril.Isotope.Morphism.CaseIter
