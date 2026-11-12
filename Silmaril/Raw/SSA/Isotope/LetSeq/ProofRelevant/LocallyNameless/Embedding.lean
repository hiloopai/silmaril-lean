module

public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.RefinementCategories
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.RefinementCategories
public import Silmaril.Raw.SSA.Isotope.Morphism.SeqCase

@[expose] public section

/-! # Witness-preserving inclusion of the native LetSeq fragment -/

namespace Silmaril.Isotope.LetSeq.ProofRelevant.LocallyNameless

open Silmaril.Isotope.LetSeq.LocallyNameless (Tm TypedRenaming)

universe u v w r
variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type v} [HasTy Φ τ]
variable {Γ : Ctx ν τ}

/-- Include native fragment typing without changing any subtype witness. -/
def HasType.embed : {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} →
    HasType Φ Γ β t A →
      LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ β (Morphism.SeqCase.embed t) A
  | _, _, _, _, .fv h => .fv h
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op h => .op h.embed
  | _, _, _, _, .let₁ h k => LetCase.ProofRelevant.LocallyNameless.HasType.let₁ h.embed k.embed
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair h k => LetCase.ProofRelevant.LocallyNameless.HasType.pair h.embed k.embed
  | _, _, _, _, .let₂ h k => LetCase.ProofRelevant.LocallyNameless.HasType.let₂ h.embed k.embed
  | _, _, _, _, .sub h d => .sub h.embed d

/-- The induced translation of exact typed terms, retaining coercion paths. -/
def TypedTerm.embed {i : Isotope.Theory.TypingIndex τ} (a : TypedTerm Φ Γ i) :
    LetCase.ProofRelevant.LocallyNameless.TypedTerm Φ Γ i :=
  ⟨Morphism.SeqCase.embed a.1, a.2.embed⟩

private theorem dependent_congr₁ {α : Type*} {β γ : α → Type*}
    (f : ∀ a, β a → γ a) {a a' : α} {b : β a} {b' : β a'}
    (ha : a = a') (hb : HEq b b') : HEq (f a b) (f a' b') := by
  cases ha; cases hb; rfl

private theorem dependent_congr₂ {α₁ α₂ : Type*} {β₁ : α₁ → Type*}
    {β₂ : α₂ → Type*} {γ : α₁ → α₂ → Type*}
    (f : ∀ a₁ a₂, β₁ a₁ → β₂ a₂ → γ a₁ a₂)
    {a₁ a₁' : α₁} {a₂ a₂' : α₂} {b₁ : β₁ a₁} {b₁' : β₁ a₁'}
    {b₂ : β₂ a₂} {b₂' : β₂ a₂'} (h₁ : a₁ = a₁') (h₂ : a₂ = a₂')
    (k₁ : HEq b₁ b₁') (k₂ : HEq b₂ b₂') :
    HEq (f a₁ a₂ b₁ b₂) (f a₁' a₂' b₁' b₂') := by
  cases h₁; cases h₂; cases k₁; cases k₂; rfl

private theorem dependent_congr₃ {α₁ α₂ α₃ : Type*} {β₁ : α₁ → Type*}
    {β₂ : α₂ → Type*} {β₃ : α₃ → Type*} {γ : α₁ → α₂ → α₃ → Type*}
    (f : ∀ a₁ a₂ a₃, β₁ a₁ → β₂ a₂ → β₃ a₃ → γ a₁ a₂ a₃)
    {a₁ a₁' : α₁} {a₂ a₂' : α₂} {a₃ a₃' : α₃}
    {b₁ : β₁ a₁} {b₁' : β₁ a₁'} {b₂ : β₂ a₂} {b₂' : β₂ a₂'}
    {b₃ : β₃ a₃} {b₃' : β₃ a₃'} (h₁ : a₁ = a₁') (h₂ : a₂ = a₂') (h₃ : a₃ = a₃')
    (k₁ : HEq b₁ b₁') (k₂ : HEq b₂ b₂') (k₃ : HEq b₃ b₃') :
    HEq (f a₁ a₂ a₃ b₁ b₂ b₃) (f a₁' a₂' a₃' b₁' b₂' b₃') := by
  cases h₁; cases h₂; cases h₃; cases k₁; cases k₂; cases k₃; rfl

private theorem HasType.embed_cast {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n}
    {A B : τ} (e : A = B) (h : HasType Φ Γ β t A) :
    (e ▸ h).embed = e ▸ h.embed := by cases e; rfl

/-- Renaming commutes with inclusion at the level of exact typing data. -/
theorem HasType.embed_rename {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) (ρ : TypedRenaming β β') :
    HEq (h.rename ρ).embed (LetCase.ProofRelevant.LocallyNameless.HasType.rename ρ h.embed) := by
  induction h generalizing m with
  | fv h => rfl
  | @bv n β i =>
    change HEq ((ρ.typed i ▸ (HasType.bv (ι := ρ.toFun i))).embed)
      (ρ.typed i ▸ (LetCase.ProofRelevant.LocallyNameless.HasType.bv (ι := ρ.toFun i)))
    exact heq_of_eq (HasType.embed_cast (ρ.typed i) _)
  | op h ih =>
    exact dependent_congr₁ (fun a h => LetCase.ProofRelevant.LocallyNameless.HasType.op (a := a) h)
      (Morphism.SeqCase.embed_rename _ _) (ih ρ)
  | @let₁ n β a A b B h k ih ik =>
    exact dependent_congr₂ (fun a b (h : LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ β' a A)
        (k : LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ (β'.snoc A) b B) => LetCase.ProofRelevant.LocallyNameless.HasType.let₁ h k)
      (Morphism.SeqCase.embed_rename _ _) (Morphism.SeqCase.embed_rename _ _)
      (ih ρ) (ik (BoundCtx.Renaming.up ρ _))
  | unit => rfl
  | @pair n β a A b B h k ih ik =>
    exact dependent_congr₂ (fun a b (h : LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ β' a A)
        (k : LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ β' b B) => LetCase.ProofRelevant.LocallyNameless.HasType.pair h k)
      (Morphism.SeqCase.embed_rename _ _) (Morphism.SeqCase.embed_rename _ _)
      (ih ρ) (ik ρ)
  | @let₂ n β a A B c C h k ih ik =>
    exact dependent_congr₂ (fun a c (h : LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ β' a (product A B))
        (k : LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ ((β'.snoc A).snoc B) c C) => LetCase.ProofRelevant.LocallyNameless.HasType.let₂ h k)
      (Morphism.SeqCase.embed_rename _ _) (Morphism.SeqCase.embed_rename _ _)
      (ih ρ) (ik ((BoundCtx.Renaming.up ρ _).up _))
  | sub h d ih =>
    exact dependent_congr₁ (fun a h => LetCase.ProofRelevant.LocallyNameless.HasType.sub (a := a) h d)
      (Morphism.SeqCase.embed_rename _ _) (ih ρ)


/-- Inclusion commutes with insertion of a bound variable, retaining typing evidence. -/
theorem HasType.embed_lift {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n}
    {A B : τ} (h : HasType Φ Γ β t A) :
    HEq (h.lift (B := B)).embed (h.embed.lift (B := B)) :=
  h.embed_rename (BoundCtx.Renaming.succ β B)

omit [DecidableEq ν] in
private theorem subst_embed_eq {n m : Nat} (t : Tm ν Φ n)
    {σ : Fin n → Tm ν Φ m} {σ' : Fin n → LetCase.LocallyNameless.Tm ν Φ m}
    (hσ : ∀ i, Morphism.SeqCase.embed (σ i) = σ' i) :
    Morphism.SeqCase.embed (t.bsubst σ) =
      (Morphism.SeqCase.embed t).bsubst σ' := by
  rw [Morphism.SeqCase.embed_bsubst]
  exact congrArg (fun s => LetCase.LocallyNameless.Tm.bsubst s (Morphism.SeqCase.embed t)) (funext hσ)

omit [DecidableEq ν] in
private theorem subst_embed_up_eq {n m : Nat}
    {σ : Fin n → Tm ν Φ m} {σ' : Fin n → LetCase.LocallyNameless.Tm ν Φ m}
    (hσ : ∀ i, Morphism.SeqCase.embed (σ i) = σ' i) :
    ∀ i, Morphism.SeqCase.embed (Tm.upSub σ i) = LetCase.LocallyNameless.Tm.upSub σ' i := by
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  exact (Morphism.SeqCase.embed_lift (σ j)).trans (congrArg _ (hσ j))

private theorem subst_embed_up_heq {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} {σ' : Fin n → LetCase.LocallyNameless.Tm ν Φ m}
    {s : TypedSubst (Γ := Γ) β β' σ}
    {s' : LetCase.ProofRelevant.LocallyNameless.TypedSubst (Γ := Γ) β β' σ'}
    (hσ : ∀ i, Morphism.SeqCase.embed (σ i) = σ' i)
    (hs : ∀ i, HEq (s i).embed (s' i)) (A : τ) :
    ∀ i, HEq (s.up A i).embed (s'.up A i) := by
  intro i
  refine Fin.cases HEq.rfl (fun j => ?_) i
  exact ((s j).embed_lift).trans
    (dependent_congr₁ (fun t (h : LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ β' t (β.get j)) =>
      h.lift (B := A)) (hσ j) (hs j))

/-- Simultaneous substitution commutes with inclusion on exact derivations.
The pointwise formulation also applies under any number of binders. -/
theorem HasType.embed_bsubst {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A)
    {σ : Fin n → Tm ν Φ m} {σ' : Fin n → LetCase.LocallyNameless.Tm ν Φ m}
    (s : TypedSubst (Γ := Γ) β β' σ)
    (s' : LetCase.ProofRelevant.LocallyNameless.TypedSubst (Γ := Γ) β β' σ')
    (hσ : ∀ i, Morphism.SeqCase.embed (σ i) = σ' i)
    (hs : ∀ i, HEq (s i).embed (s' i)) :
    HEq (h.bsubst s).embed (LetCase.ProofRelevant.LocallyNameless.HasType.bsubst s' h.embed) := by
  induction h generalizing m with
  | fv h => rfl
  | @bv n β i => exact hs i
  | op h ih =>
    exact dependent_congr₁ (fun a h => LetCase.ProofRelevant.LocallyNameless.HasType.op (a := a) h)
      (subst_embed_eq _ hσ) (ih s s' hσ hs)
  | @let₁ n β a A b B h k ih ik =>
    exact dependent_congr₂ (fun a b (h : LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ β' a A)
        (k : LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ (β'.snoc A) b B) => LetCase.ProofRelevant.LocallyNameless.HasType.let₁ h k)
      (subst_embed_eq _ hσ) (subst_embed_eq _ (subst_embed_up_eq hσ))
      (ih s s' hσ hs) (ik (s.up _) (s'.up _) (subst_embed_up_eq hσ) (subst_embed_up_heq hσ hs _))
  | unit => rfl
  | @pair n β a A b B h k ih ik =>
    exact dependent_congr₂ (fun a b (h : LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ β' a A)
        (k : LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ β' b B) => LetCase.ProofRelevant.LocallyNameless.HasType.pair h k)
      (subst_embed_eq _ hσ) (subst_embed_eq _ hσ)
      (ih s s' hσ hs) (ik s s' hσ hs)
  | @let₂ n β a A B c C h k ih ik =>
    exact dependent_congr₂ (fun a c (h : LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ β' a (product A B))
        (k : LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ ((β'.snoc A).snoc B) c C) => LetCase.ProofRelevant.LocallyNameless.HasType.let₂ h k)
      (subst_embed_eq _ hσ) (subst_embed_eq _ (subst_embed_up_eq (subst_embed_up_eq hσ)))
      (ih s s' hσ hs) (ik ((s.up _).up _) ((s'.up _).up _) (subst_embed_up_eq (subst_embed_up_eq hσ))
        (subst_embed_up_heq (subst_embed_up_eq hσ) (subst_embed_up_heq hσ hs _) _))
  | sub h d ih =>
    exact dependent_congr₁ (fun a h => LetCase.ProofRelevant.LocallyNameless.HasType.sub (a := a) h d)
      (subst_embed_eq _ hσ) (ih s s' hσ hs)


/-- Opening a binder commutes with inclusion without identifying typing witnesses. -/
theorem HasType.embed_instantiate {n : Nat} {β : BoundCtx τ n} {A B : τ}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (hb : HasType Φ Γ (β.snoc A) b B) (ha : HasType Φ Γ β a A) :
    HEq (hb.instantiate ha).embed (hb.embed.instantiate ha.embed) := by
  exact hb.embed_bsubst (β' := β)
    (σ := Fin.cases a fun i => .bv i)
    (σ' := Fin.cases (Morphism.SeqCase.embed a) fun i => .bv i)
    (Fin.cases ha fun _ => .bv)
    (Fin.cases ha.embed fun _ => .bv)
    (fun i => Fin.cases rfl (fun _ => rfl) i)
    (fun i => Fin.cases HEq.rfl (fun _ => HEq.rfl) i)

end Silmaril.Isotope.LetSeq.ProofRelevant.LocallyNameless
