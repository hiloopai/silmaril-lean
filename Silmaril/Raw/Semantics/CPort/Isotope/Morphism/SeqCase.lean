module

public import Silmaril.Semantics.CPort.Isotope.LetSeq.LocallyNameless.Typing.Defs
public import Silmaril.Semantics.CPort.Isotope.LetSeq.LocallyNameless.Purity.Defs
public import Silmaril.Semantics.CPort.Isotope.LetCase.LocallyNameless.Typing.Defs
public import Silmaril.Semantics.CPort.Isotope.LetCase.LocallyNameless.Purity.Defs
/-! Constructor-preserving inclusion from LetSeq into LetCase. -/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.Morphism.SeqCase

open LetSeq.LocallyNameless

variable {ν : Type u} {Φ : Type v} {n m : Nat}

/-- Include the smaller calculus without changing names or binder indices. -/
def embed {n : Nat} : Tm ν Φ n → LetCase.LocallyNameless.Tm ν Φ n
  | .fv x => .fv x
  | .bv i => .bv i
  | .op f a => .op f (embed a)
  | .let₁ a b => .let₁ (embed a) (embed b)
  | .unit => .unit
  | .pair a b => .pair (embed a) (embed b)
  | .let₂ a b => .let₂ (embed a) (embed b)

/-- Recognize terms using only constructors of the smaller calculus. -/
def project {n : Nat} : LetCase.LocallyNameless.Tm ν Φ n → Option (Tm ν Φ n)
  | .fv x => some (.fv x)
  | .bv i => some (.bv i)
  | .op f a => return .op f (← project a)
  | .let₁ a b => return .let₁ (← project a) (← project b)
  | .unit => some .unit
  | .pair a b => return .pair (← project a) (← project b)
  | .let₂ a b => return .let₂ (← project a) (← project b)
  | .inl _ => none
  | .inr _ => none
  | .case _ _ _ => none
  | .abort _ => none

@[simp] theorem project_embed (t : Tm ν Φ n) : project (embed t) = some t := by
  induction t <;> simp [embed, project, *]

theorem embed_injective : Function.Injective (embed : Tm ν Φ n → _) := by
  intro a b h
  exact Option.some.inj (by simpa only [project_embed] using congrArg project h)

@[simp] theorem embed_rename (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    embed (Tm.rename ρ t) = LetCase.LocallyNameless.Tm.rename ρ (embed t) := by
  induction t generalizing m <;> simp [Tm.rename, embed, LetCase.LocallyNameless.Tm.rename, *]
  all_goals rfl

@[simp] theorem embed_lift (t : Tm ν Φ n) :
    embed t.lift = LetCase.LocallyNameless.Tm.lift (embed t) := embed_rename _ _

@[simp] theorem embed_underBinder (t : Tm ν Φ (n + 1)) :
    embed t.underBinder = LetCase.LocallyNameless.Tm.underBinder (embed t) := embed_rename _ _

@[simp] theorem embed_underTwoBinders (t : Tm ν Φ (n + 2)) :
    embed t.underTwoBinders = LetCase.LocallyNameless.Tm.underTwoBinders (embed t) := embed_rename _ _

theorem embed_upSub (σ : Fin n → Tm ν Φ m) :
    (fun i => embed (Tm.upSub σ i)) = LetCase.LocallyNameless.Tm.upSub (fun i => embed (σ i)) := by
  funext i
  exact Fin.cases rfl (fun j => embed_lift (σ j)) i

@[simp] theorem embed_bsubst (σ : Fin n → Tm ν Φ m) (t : Tm ν Φ n) :
    embed (Tm.bsubst σ t) = LetCase.LocallyNameless.Tm.bsubst (fun i => embed (σ i)) (embed t) := by
  induction t generalizing m <;> simp [Tm.bsubst, embed, LetCase.LocallyNameless.Tm.bsubst, embed_upSub, *]

@[simp] theorem embed_instantiate (b : Tm ν Φ (n + 1)) (a : Tm ν Φ n) :
    embed (Tm.instantiate b a) = LetCase.LocallyNameless.Tm.instantiate (embed b) (embed a) := by
  rw [Tm.instantiate, embed_bsubst, LetCase.LocallyNameless.Tm.instantiate]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem embed_fsubst [DecidableEq ν] (x : ν) (s t : Tm ν Φ n) :
    embed (Tm.fsubst x s t) = LetCase.LocallyNameless.Tm.fsubst x (embed s) (embed t) := by
  induction t with
  | fv y => by_cases h : x = y <;> simp [Tm.fsubst, embed, h]
  | bv i => rfl
  | unit => rfl
  | op _ _ ih => simp [Tm.fsubst, embed, LetCase.LocallyNameless.Tm.fsubst, ih]
  | let₁ _ _ iha ihb => simp [Tm.fsubst, embed, LetCase.LocallyNameless.Tm.fsubst, iha, ihb]
  | pair _ _ iha ihb => simp [Tm.fsubst, embed, LetCase.LocallyNameless.Tm.fsubst, iha, ihb]
  | let₂ _ _ iha ihb => simp [Tm.fsubst, embed, LetCase.LocallyNameless.Tm.fsubst, iha, ihb]

/-- Inclusion preserves exact typing over the same contexts and type operations. -/
theorem embed_hasType {τ : Type w} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]
    {Γ : Ctx ν τ} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) : LetCase.LocallyNameless.HasType Φ Γ β (embed t) A := by
  induction h with
  | fv h => exact .fv h
  | bv => exact .bv
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb

/-- Inclusion preserves the independently chosen primitive purity predicate. -/
theorem embed_pure {ε : Type r} [HasEff Φ ε] {pureEff : ε} {t : Tm ν Φ n}
    (h : Pure pureEff t) : LetCase.LocallyNameless.Pure pureEff (embed t) := by
  induction h with
  | fv => exact .fv
  | bv => exact .bv
  | op hf _ ih => exact .op hf ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb

end Silmaril.Isotope.Morphism.SeqCase
