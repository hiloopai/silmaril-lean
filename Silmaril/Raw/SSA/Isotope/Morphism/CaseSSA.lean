module

public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Structural
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Scope
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Purity
public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Purity

/-!
# Scoped let-case and positional SSA expressions

With no named free variables, let-case's finite indices represent precisely
SSA expressions scoped by any ambient length `n`, including nonzero lengths.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Morphism.CaseSSA

open LetCase.LocallyNameless

variable {Φ : Type u} {n m : Nat}

/-- Forget finite-index bounds, preserving every expression constructor. -/
def erase {n : Nat} : Tm Empty Φ n → LambdaSSA.Tm Φ
  | .fv x => nomatch x
  | .bv i => .var i.val
  | .op f a => .op f (erase a)
  | .let₁ a b => .let₁ (erase a) (erase b)
  | .unit => .unit
  | .pair a b => .pair (erase a) (erase b)
  | .let₂ a b => .let₂ (erase a) (erase b)
  | .inl a => .inl (erase a)
  | .inr a => .inr (erase a)
  | .case e l r => .case (erase e) (erase l) (erase r)
  | .abort a => .abort (erase a)

/-- Reconstruct finite indices from an expression and its scope proof. -/
def ofScoped {n : Nat} (t : LambdaSSA.Tm Φ) (h : t.Scoped n) : Tm Empty Φ n :=
  match t with
  | .var i => .bv ⟨i, h⟩
  | .op f a => .op f (ofScoped a h)
  | .let₁ a b => .let₁ (ofScoped a h.1) (ofScoped b h.2)
  | .unit => .unit
  | .pair a b => .pair (ofScoped a h.1) (ofScoped b h.2)
  | .let₂ a b => .let₂ (ofScoped a h.1) (ofScoped b h.2)
  | .inl a => .inl (ofScoped a h)
  | .inr a => .inr (ofScoped a h)
  | .case e l r => .case (ofScoped e h.1) (ofScoped l h.2.1) (ofScoped r h.2.2)
  | .abort a => .abort (ofScoped a h)

@[simp] theorem scoped_erase (t : Tm Empty Φ n) : (erase t).Scoped n := by
  induction t with
  | fv x => exact x.elim
  | bv i => exact i.isLt
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => exact ih
  | let₁ _ _ iha ihb | pair _ _ iha ihb | let₂ _ _ iha ihb => exact ⟨iha, ihb⟩
  | unit => trivial
  | case _ _ _ ihe ihl ihr => exact ⟨ihe, ihl, ihr⟩

@[simp] theorem erase_ofScoped (t : LambdaSSA.Tm Φ) (h : t.Scoped n) :
    erase (ofScoped t h) = t := by
  induction t generalizing n with
  | var i => rfl
  | op f a ih => exact congrArg (LambdaSSA.Tm.op f) (ih h)
  | let₁ a b iha ihb => exact congrArg₂ LambdaSSA.Tm.let₁ (iha h.1) (ihb h.2)
  | pair a b iha ihb => exact congrArg₂ LambdaSSA.Tm.pair (iha h.1) (ihb h.2)
  | unit => rfl
  | let₂ a b iha ihb => exact congrArg₂ LambdaSSA.Tm.let₂ (iha h.1) (ihb h.2)
  | inl a ih => exact congrArg LambdaSSA.Tm.inl (ih h)
  | inr a ih => exact congrArg LambdaSSA.Tm.inr (ih h)
  | case e l r ihe ihl ihr => simp [ofScoped, erase, ihe h.1, ihl h.2.1, ihr h.2.2]
  | abort a ih => exact congrArg LambdaSSA.Tm.abort (ih h)

@[simp] theorem ofScoped_erase (t : Tm Empty Φ n) :
    ofScoped (erase t) (scoped_erase t) = t := by
  induction t with
  | fv x => exact x.elim
  | bv i => rfl
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => simp [erase, ofScoped, ih]
  | let₁ _ _ iha ihb | pair _ _ iha ihb | let₂ _ _ iha ihb =>
      simp [erase, ofScoped, iha, ihb]
  | unit => rfl
  | case _ _ _ ihe ihl ihr => simp [erase, ofScoped, ihe, ihl, ihr]

theorem erase_injective : Function.Injective (erase : Tm Empty Φ n → _) := by
  intro a b h
  have h' : (⟨erase a, scoped_erase a⟩ : {t : LambdaSSA.Tm Φ // t.Scoped n}) =
      ⟨erase b, scoped_erase b⟩ := Subtype.ext h
  have h'' := congrArg (fun t : {t : LambdaSSA.Tm Φ // t.Scoped n} => ofScoped t.val t.property) h'
  simpa only [ofScoped_erase] using h''

/-- Full equivalence with positional expressions scoped by the ambient length. -/
def scopedEquiv (Φ : Type u) (n : Nat) :
    Tm Empty Φ n ≃ {t : LambdaSSA.Tm Φ // t.Scoped n} where
  toFun t := ⟨erase t, scoped_erase t⟩
  invFun t := ofScoped t.val t.property
  left_inv := ofScoped_erase
  right_inv t := Subtype.ext (erase_ofScoped t.val t.property)

/-- Decode exactly when every positional variable is in scope. -/
def decode? (n : Nat) (t : LambdaSSA.Tm Φ) : Option (Tm Empty Φ n) :=
  if h : t.Scoped n then some (ofScoped t h) else none

@[simp] theorem decode?_erase (t : Tm Empty Φ n) : decode? n (erase t) = some t := by
  simp [decode?]

theorem decode?_eq_some_iff {t : LambdaSSA.Tm Φ} {a : Tm Empty Φ n} :
    decode? n t = some a ↔ erase a = t := by
  constructor
  · intro h
    unfold decode? at h
    split at h
    · have he := Option.some.inj h
      subst a
      exact erase_ofScoped _ _
    · contradiction
  · intro h
    subst t
    exact decode?_erase a

/-- Erasure preserves exact typing using the newest-first list of bound types. -/
theorem erase_hasType {τ : Type v} [TypeFormers τ] [HasTy Φ τ]
    {Γ : Ctx Empty τ} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
    (h : HasType Φ Γ β t A) : LambdaSSA.Tm.HasType β.toList (erase t) A := by
  induction h with
  | @fv x => exact x.elim
  | bv => exact .var (BoundCtx.getElem?_toList _ _)
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih

/-- Exact SSA typing reflects through erasure; no injectivity laws for type
operations or uniqueness of derivations are assumed. -/
theorem hasType_of_erase {τ : Type v} [TypeFormers τ] [HasTy Φ τ]
    {Γ : Ctx Empty τ} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
    (h : LambdaSSA.Tm.HasType β.toList (erase t) A) : HasType Φ Γ β t A := by
  induction t generalizing A with
  | fv x => exact x.elim
  | bv i =>
      cases h with
      | var hi =>
          have he : β.get i = A := Option.some.inj ((BoundCtx.getElem?_toList β i).symm.trans hi)
          exact he ▸ .bv
  | op _ _ ih => cases h with | op ha => exact .op (ih ha)
  | let₁ _ _ iha ihb => cases h with | let₁ ha hb => exact .let₁ (iha ha) (ihb hb)
  | unit => cases h with | unit => exact .unit
  | pair _ _ iha ihb => cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | let₂ _ _ iha ihb => cases h with | let₂ ha hb => exact .let₂ (iha ha) (ihb hb)
  | inl _ ih => cases h with | inl ha => exact .inl (ih ha)
  | inr _ ih => cases h with | inr ha => exact .inr (ih ha)
  | case _ _ _ ihe ihl ihr =>
      cases h with | case he hl hr => exact .case (ihe he) (ihl hl) (ihr hr)
  | abort _ ih => cases h with | abort ha => exact .abort (ih ha)

/-- Both presentations assign exactly the same types over corresponding contexts. -/
theorem erase_hasType_iff {τ : Type v} [TypeFormers τ] [HasTy Φ τ]
    {Γ : Ctx Empty τ} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ} :
    LambdaSSA.Tm.HasType β.toList (erase t) A ↔ HasType Φ Γ β t A :=
  ⟨hasType_of_erase, erase_hasType⟩

theorem ofScoped_hasType_iff {τ : Type v} [TypeFormers τ] [HasTy Φ τ]
    {Γ : Ctx Empty τ} {β : BoundCtx τ n} {t : LambdaSSA.Tm Φ} {A : τ} (h : t.Scoped n) :
    HasType Φ Γ β (ofScoped t h) A ↔ LambdaSSA.Tm.HasType β.toList t A := by
  rw [← erase_hasType_iff, erase_ofScoped]

/-- Related finite and natural index maps remain related under one binder. -/
theorem up_ren_related {ρ : Fin n → Fin m} {r : Nat → Nat}
    (h : ∀ i, (ρ i).val = r i.val) :
    ∀ i, (Tm.up ρ i).val = Silmaril.DeBruijn.lift r i.val :=
  Fin.cases rfl (fun i => congrArg Nat.succ (h i))

/-- Erasure commutes with renamings agreeing on all in-scope indices. -/
theorem erase_rename (ρ : Fin n → Fin m) (r : Nat → Nat)
    (hρ : ∀ i, (ρ i).val = r i.val) (t : Tm Empty Φ n) :
    erase (Tm.rename ρ t) = LambdaSSA.Tm.rename r (erase t) := by
  induction t generalizing m r with
  | fv x => exact x.elim
  | bv i => exact congrArg LambdaSSA.Tm.var (hρ i)
  | op f a ih => exact congrArg (LambdaSSA.Tm.op f) (ih _ _ hρ)
  | let₁ a b iha ihb =>
      exact congrArg₂ LambdaSSA.Tm.let₁ (iha _ _ hρ) (ihb _ _ (up_ren_related hρ))
  | unit => rfl
  | pair a b iha ihb => exact congrArg₂ LambdaSSA.Tm.pair (iha _ _ hρ) (ihb _ _ hρ)
  | let₂ a b iha ihb =>
      exact congrArg₂ LambdaSSA.Tm.let₂ (iha _ _ hρ)
        (ihb _ _ (up_ren_related (up_ren_related hρ)))
  | inl a ih => exact congrArg LambdaSSA.Tm.inl (ih _ _ hρ)
  | inr a ih => exact congrArg LambdaSSA.Tm.inr (ih _ _ hρ)
  | case e l r ihe ihl ihr =>
      simp only [Tm.rename, erase, LambdaSSA.Tm.rename]
      rw [ihe _ _ hρ, ihl _ _ (up_ren_related hρ), ihr _ _ (up_ren_related hρ)]
  | abort a ih => exact congrArg LambdaSSA.Tm.abort (ih _ _ hρ)

@[simp] theorem erase_lift (t : Tm Empty Φ n) :
    erase t.lift = LambdaSSA.Tm.rename Nat.succ (erase t) :=
  erase_rename Fin.succ Nat.succ (fun _ => rfl) t

/-- Related substitutions remain related under one binder. -/
theorem up_subst_related {σ : Fin n → Tm Empty Φ m} {θ : Nat → LambdaSSA.Tm Φ}
    (h : ∀ i, erase (σ i) = θ i.val) :
    ∀ i, erase (Tm.upSub σ i) = LambdaSSA.Tm.liftSubst θ i.val := by
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  change erase (σ j).lift = LambdaSSA.Tm.rename Nat.succ (θ j.val)
  rw [erase_lift, h j]

/-- Erasure commutes with substitutions agreeing on all in-scope images. -/
theorem erase_bsubst (σ : Fin n → Tm Empty Φ m) (θ : Nat → LambdaSSA.Tm Φ)
    (hσ : ∀ i, erase (σ i) = θ i.val) (t : Tm Empty Φ n) :
    erase (Tm.bsubst σ t) = LambdaSSA.Tm.subst θ (erase t) := by
  induction t generalizing m θ with
  | fv x => exact x.elim
  | bv i => exact hσ i
  | op f a ih => exact congrArg (LambdaSSA.Tm.op f) (ih _ _ hσ)
  | let₁ a b iha ihb =>
      exact congrArg₂ LambdaSSA.Tm.let₁ (iha _ _ hσ) (ihb _ _ (up_subst_related hσ))
  | unit => rfl
  | pair a b iha ihb => exact congrArg₂ LambdaSSA.Tm.pair (iha _ _ hσ) (ihb _ _ hσ)
  | let₂ a b iha ihb =>
      exact congrArg₂ LambdaSSA.Tm.let₂ (iha _ _ hσ)
        (ihb _ _ (up_subst_related (up_subst_related hσ)))
  | inl a ih => exact congrArg LambdaSSA.Tm.inl (ih _ _ hσ)
  | inr a ih => exact congrArg LambdaSSA.Tm.inr (ih _ _ hσ)
  | case e l r ihe ihl ihr =>
      simp only [Tm.bsubst, erase, LambdaSSA.Tm.subst]
      rw [ihe _ _ hσ, ihl _ _ (up_subst_related hσ), ihr _ _ (up_subst_related hσ)]
  | abort a ih => exact congrArg LambdaSSA.Tm.abort (ih _ _ hσ)

/-- Opening the newest binder agrees with positional substitution at index zero. -/
theorem erase_instantiate (b : Tm Empty Φ (n + 1)) (a : Tm Empty Φ n) :
    erase (Tm.instantiate b a) =
      LambdaSSA.Tm.subst (Nat.casesOn · (erase a) LambdaSSA.Tm.var) (erase b) :=
  erase_bsubst _ _ (Fin.cases rfl (fun _ => rfl)) b

theorem decode?_rename (ρ : Fin n → Fin m) (r : Nat → Nat)
    (hρ : ∀ i, (ρ i).val = r i.val) (t : Tm Empty Φ n) :
    decode? m (LambdaSSA.Tm.rename r (erase t)) = some (Tm.rename ρ t) := by
  rw [← erase_rename ρ r hρ, decode?_erase]

theorem decode?_subst (σ : Fin n → Tm Empty Φ m) (θ : Nat → LambdaSSA.Tm Φ)
    (hσ : ∀ i, erase (σ i) = θ i.val) (t : Tm Empty Φ n) :
    decode? m (LambdaSSA.Tm.subst θ (erase t)) = some (Tm.bsubst σ t) := by
  rw [← erase_bsubst σ θ hσ, decode?_erase]

section Resolve

variable {ν : Type w}

/-- Resolve named free variables to positional slots. The map shifts beneath
binders; different names may resolve to the same slot. -/
def resolve {n : Nat} (ρ : ν → Nat) : Tm ν Φ n → LambdaSSA.Tm Φ
  | .fv x => .var (ρ x)
  | .bv i => .var i.val
  | .op f a => .op f (resolve ρ a)
  | .let₁ a b => .let₁ (resolve ρ a) (resolve (fun x => ρ x + 1) b)
  | .unit => .unit
  | .pair a b => .pair (resolve ρ a) (resolve ρ b)
  | .let₂ a b => .let₂ (resolve ρ a) (resolve (fun x => ρ x + 2) b)
  | .inl a => .inl (resolve ρ a)
  | .inr a => .inr (resolve ρ a)
  | .case e l r => .case (resolve ρ e)
      (resolve (fun x => ρ x + 1) l) (resolve (fun x => ρ x + 1) r)
  | .abort a => .abort (resolve ρ a)

@[simp] theorem resolve_empty (ρ : Empty → Nat) (t : Tm Empty Φ n) :
    resolve ρ t = erase t := by
  induction t generalizing ρ with
  | fv x => exact x.elim
  | bv i => rfl
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => simp [resolve, erase, ih]
  | let₁ _ _ iha ihb | pair _ _ iha ihb | let₂ _ _ iha ihb =>
      simp [resolve, erase, iha, ihb]
  | unit => rfl
  | case _ _ _ ihe ihl ihr => simp [resolve, erase, ihe, ihl, ihr]

/-- Visible free names resolve to positions with exactly their declared types. -/
def Resolves {τ : Type v} [DecidableEq ν] (Γ : Ctx ν τ) (β : BoundCtx τ n)
    (ρ : ν → Nat) : Prop :=
  ∀ ⦃x A⦄, Γ.lookup x = some A → SSA.At β.toList (ρ x) A

theorem Resolves.up {τ : Type v} [DecidableEq ν] {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {ρ : ν → Nat} (hρ : Resolves Γ β ρ) (B : τ) :
    Resolves Γ (.snoc β B) (fun x => ρ x + 1) := by
  intro x A hx
  simpa [BoundCtx.toList, SSA.At] using hρ hx

/-- Name resolution preserves exact typing whenever the resolver preserves
visible lookup types. Unused free names impose no constraint. -/
theorem resolve_hasType {τ : Type v} [TypeFormers τ] [HasTy Φ τ] [DecidableEq ν]
    {Γ : Ctx ν τ} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ} {ρ : ν → Nat}
    (hρ : Resolves Γ β ρ) (h : HasType Φ Γ β t A) :
    LambdaSSA.Tm.HasType β.toList (resolve ρ t) A := by
  induction h generalizing ρ with
  | fv hx => exact .var (hρ hx)
  | bv => exact .var (BoundCtx.getElem?_toList _ _)
  | op _ ih => exact .op (ih hρ)
  | let₁ _ _ iha ihb => exact .let₁ (iha hρ) (ihb (hρ.up _))
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha hρ) (ihb hρ)
  | let₂ _ _ iha ihb => exact .let₂ (iha hρ) (ihb ((hρ.up _).up _))
  | inl _ ih => exact .inl (ih hρ)
  | inr _ ih => exact .inr (ih hρ)
  | case _ _ _ ihe ihl ihr => exact .case (ihe hρ) (ihl (hρ.up _)) (ihr (hρ.up _))
  | abort _ ih => exact .abort (ih hρ)

end Resolve

/-- Resolution preserves syntactic purity independently of typing or valid slots. -/
theorem resolve_pure {ν : Type w} {ε : Type v} [HasEff Φ ε] {pureEff : ε}
    {t : Tm ν Φ n} (h : Pure pureEff t) (ρ : ν → Nat) :
    LambdaSSA.Tm.Pure pureEff (resolve ρ t) := by
  induction h generalizing ρ with
  | fv => exact .var
  | bv => exact .var
  | op hf _ ih => exact .op hf (ih ρ)
  | let₁ _ _ iha ihb => exact .let₁ (iha ρ) (ihb _)
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha ρ) (ihb ρ)
  | let₂ _ _ iha ihb => exact .let₂ (iha ρ) (ihb _)
  | inl _ ih => exact .inl (ih ρ)
  | inr _ ih => exact .inr (ih ρ)
  | case _ _ _ ihe ihl ihr => exact .case (ihe ρ) (ihl _) (ihr _)
  | abort _ ih => exact .abort (ih ρ)

theorem erase_pure {ε : Type v} [HasEff Φ ε] {pureEff : ε} {t : Tm Empty Φ n}
    (h : Pure pureEff t) : LambdaSSA.Tm.Pure pureEff (erase t) := by
  simpa only [resolve_empty] using resolve_pure h Empty.elim

theorem pure_of_erase {ε : Type v} [HasEff Φ ε] {pureEff : ε} {t : Tm Empty Φ n}
    (h : LambdaSSA.Tm.Pure pureEff (erase t)) : Pure pureEff t := by
  induction t with
  | fv x => exact x.elim
  | bv => exact .bv
  | op _ _ ih => cases h with | op hf ha => exact .op hf (ih ha)
  | let₁ _ _ iha ihb => cases h with | let₁ ha hb => exact .let₁ (iha ha) (ihb hb)
  | unit => exact .unit
  | pair _ _ iha ihb => cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | let₂ _ _ iha ihb => cases h with | let₂ ha hb => exact .let₂ (iha ha) (ihb hb)
  | inl _ ih => cases h with | inl ha => exact .inl (ih ha)
  | inr _ ih => cases h with | inr ha => exact .inr (ih ha)
  | case _ _ _ ihe ihl ihr =>
      cases h with | case he hl hr => exact .case (ihe he) (ihl hl) (ihr hr)
  | abort _ ih => cases h with | abort ha => exact .abort (ih ha)

theorem erase_pure_iff {ε : Type v} [HasEff Φ ε] {pureEff : ε} {t : Tm Empty Φ n} :
    LambdaSSA.Tm.Pure pureEff (erase t) ↔ Pure pureEff t :=
  ⟨pure_of_erase, erase_pure⟩

theorem ofScoped_pure_iff {ε : Type v} [HasEff Φ ε] {pureEff : ε}
    {t : LambdaSSA.Tm Φ} (h : t.Scoped n) :
    Pure pureEff (ofScoped t h) ↔ LambdaSSA.Tm.Pure pureEff t := by
  rw [← erase_pure_iff, erase_ofScoped]

end Silmaril.Isotope.Morphism.CaseSSA
