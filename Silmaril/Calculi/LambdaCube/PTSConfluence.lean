module

public import Silmaril.Calculi.LambdaCube.PTS
public import Mathlib.Logic.Relation

@[expose] public section

set_option autoImplicit true

/-! # Church–Rosser for the cube's untyped conversion

Tait–Martin-Löf parallel reduction on `Pseudo` with Takahashi's complete
development (`Pseudo.dev`): `Par.dev` gives the triangle property, hence the
diamond, and Mathlib's `Relation.church_rosser` turns it into confluence.
`Conv.join` shows that `Pseudo.Conv` is joinability by parallel reduction, so
distinct redex-free pseudo-terms are not convertible (`Conv.eq_of_noRedex`).

Also a generation lemma for the newest variable (`HasType.var_zero_conv`).
-/

namespace Silmaril.Calculi.LambdaCube

namespace Pseudo

variable {S : Type}

/-! ## Renaming and substitution algebra -/

theorem rename_rename (t : Pseudo S) : ∀ r r' : ℕ → ℕ,
    rename r (rename r' t) = rename (r ∘ r') t := by
  have hl : ∀ r r' : ℕ → ℕ, DeBruijn.lift r ∘ DeBruijn.lift r' = DeBruijn.lift (r ∘ r') := by
    intro r r'; funext n; cases n <;> rfl
  induction t with
  | sort s => intro r r'; rfl
  | var n => intro r r'; rfl
  | app f a ihf iha => intro r r'; simp only [rename, ihf, iha]
  | lam A b ihA ihb => intro r r'; simp only [rename, ihA, ihb, hl]
  | pi A B ihA ihB => intro r r'; simp only [rename, ihA, ihB, hl]

theorem rename_subst (t : Pseudo S) : ∀ (r : ℕ → ℕ) (σ : ℕ → Pseudo S),
    rename r (subst σ t) = subst (rename r ∘ σ) t := by
  have hl : ∀ (r : ℕ → ℕ) (σ : ℕ → Pseudo S),
      rename (DeBruijn.lift r) ∘ liftSub σ = liftSub (rename r ∘ σ) := by
    intro r σ; funext n
    cases n with
    | zero => rfl
    | succ n =>
      simp only [Function.comp_apply, liftSub, rename_rename]
      rfl
  induction t with
  | sort s => intro r σ; rfl
  | var n => intro r σ; rfl
  | app f a ihf iha => intro r σ; simp only [subst, rename, ihf, iha]
  | lam A b ihA ihb => intro r σ; simp only [subst, rename, ihA, ihb, hl]
  | pi A B ihA ihB => intro r σ; simp only [subst, rename, ihA, ihB, hl]

theorem subst_rename (t : Pseudo S) : ∀ (σ : ℕ → Pseudo S) (r : ℕ → ℕ),
    subst σ (rename r t) = subst (σ ∘ r) t := by
  have hl : ∀ (σ : ℕ → Pseudo S) (r : ℕ → ℕ),
      liftSub σ ∘ DeBruijn.lift r = liftSub (σ ∘ r) := by
    intro σ r; funext n; cases n <;> rfl
  induction t with
  | sort s => intro σ r; rfl
  | var n => intro σ r; rfl
  | app f a ihf iha => intro σ r; simp only [subst, rename, ihf, iha]
  | lam A b ihA ihb => intro σ r; simp only [subst, rename, ihA, ihb, hl]
  | pi A B ihA ihB => intro σ r; simp only [subst, rename, ihA, ihB, hl]

theorem subst_subst (t : Pseudo S) : ∀ (τ σ : ℕ → Pseudo S),
    subst τ (subst σ t) = subst (subst τ ∘ σ) t := by
  have hl : ∀ (τ σ : ℕ → Pseudo S),
      subst (liftSub τ) ∘ liftSub σ = liftSub (subst τ ∘ σ) := by
    intro τ σ; funext n
    cases n with
    | zero => rfl
    | succ n =>
      simp only [Function.comp_apply, liftSub, subst_rename, rename_subst]
      rfl
  induction t with
  | sort s => intro τ σ; rfl
  | var n => intro τ σ; rfl
  | app f a ihf iha => intro τ σ; simp only [subst, ihf, iha]
  | lam A b ihA ihb => intro τ σ; simp only [subst, ihA, ihb, hl]
  | pi A B ihA ihB => intro τ σ; simp only [subst, ihA, ihB, hl]

theorem subst_var (t : Pseudo S) : ∀ σ : ℕ → Pseudo S, (∀ n, σ n = .var n) → subst σ t = t := by
  have hl : ∀ σ : ℕ → Pseudo S, (∀ n, σ n = .var n) → ∀ n, liftSub σ n = .var n := by
    intro σ h n
    cases n with
    | zero => rfl
    | succ n => simp only [liftSub, h]; rfl
  induction t with
  | sort s => intro σ _; rfl
  | var n => intro σ h; exact h n
  | app f a ihf iha => intro σ h; simp only [subst, ihf σ h, iha σ h]
  | lam A b ihA ihb => intro σ h; simp only [subst, ihA σ h, ihb _ (hl σ h)]
  | pi A B ihA ihB => intro σ h; simp only [subst, ihA σ h, ihB _ (hl σ h)]

theorem rename_substOne (b a : Pseudo S) (r : ℕ → ℕ) :
    rename r (substOne b a) = substOne (rename (DeBruijn.lift r) b) (rename r a) := by
  simp only [substOne, rename_subst, subst_rename]
  congr 1
  funext n
  cases n <;> rfl

theorem subst_substOne (b a : Pseudo S) (σ : ℕ → Pseudo S) :
    subst σ (substOne b a) = substOne (subst (liftSub σ) b) (subst σ a) := by
  simp only [substOne, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp_apply, liftSub, subst_rename, subst]
    exact (subst_var _ _ (fun _ => rfl)).symm

/-! ## Parallel reduction -/

/-- Tait–Martin-Löf parallel β-reduction. -/
inductive Par : Pseudo S → Pseudo S → Prop where
  | sort (s) : Par (.sort s) (.sort s)
  | var (n) : Par (.var n) (.var n)
  | app : Par f f' → Par a a' → Par (.app f a) (.app f' a')
  | lam : Par A A' → Par b b' → Par (.lam A b) (.lam A' b')
  | pi : Par A A' → Par B B' → Par (.pi A B) (.pi A' B')
  | beta (A) : Par b b' → Par a a' → Par (.app (.lam A b) a) (substOne b' a')

theorem Par.refl : ∀ t : Pseudo S, Par t t
  | .sort s => .sort s
  | .var n => .var n
  | .app f a => .app (Par.refl f) (Par.refl a)
  | .lam A b => .lam (Par.refl A) (Par.refl b)
  | .pi A B => .pi (Par.refl A) (Par.refl B)

theorem Par.rename (h : Par t t') : ∀ r : ℕ → ℕ, Par (t.rename r) (t'.rename r) := by
  induction h with
  | sort s => intro r; exact .sort s
  | var n => intro r; exact .var _
  | app _ _ ih₁ ih₂ => intro r; exact .app (ih₁ r) (ih₂ r)
  | lam _ _ ih₁ ih₂ => intro r; exact .lam (ih₁ r) (ih₂ _)
  | pi _ _ ih₁ ih₂ => intro r; exact .pi (ih₁ r) (ih₂ _)
  | beta A _ _ ih₁ ih₂ =>
    intro r
    rw [rename_substOne]
    exact .beta _ (ih₁ _) (ih₂ r)

theorem Par.subst (h : Par t t') : ∀ σ σ' : ℕ → Pseudo S, (∀ n, Par (σ n) (σ' n)) →
    Par (t.subst σ) (t'.subst σ') := by
  have hl : ∀ σ σ' : ℕ → Pseudo S, (∀ n, Par (σ n) (σ' n)) →
      ∀ n, Par (liftSub σ n) (liftSub σ' n) := by
    intro σ σ' h n
    cases n with
    | zero => exact .var 0
    | succ n => exact (h n).rename _
  induction h with
  | sort s => intro σ σ' _; exact .sort s
  | var n => intro σ σ' h; exact h n
  | app _ _ ih₁ ih₂ => intro σ σ' h; exact .app (ih₁ σ σ' h) (ih₂ σ σ' h)
  | lam _ _ ih₁ ih₂ => intro σ σ' h; exact .lam (ih₁ σ σ' h) (ih₂ _ _ (hl σ σ' h))
  | pi _ _ ih₁ ih₂ => intro σ σ' h; exact .pi (ih₁ σ σ' h) (ih₂ _ _ (hl σ σ' h))
  | beta A _ _ ih₁ ih₂ =>
    intro σ σ' h
    rw [subst_substOne]
    exact .beta _ (ih₁ _ _ (hl σ σ' h)) (ih₂ σ σ' h)

theorem Par.substOne (hb : Par b b') (ha : Par a a') : Par (substOne b a) (substOne b' a') :=
  hb.subst _ _ (fun n => by cases n with
    | zero => exact ha
    | succ n => exact .var n)

/-- Takahashi's complete development. -/
def dev : Pseudo S → Pseudo S
  | .sort s => .sort s
  | .var n => .var n
  | .app (.lam _ b) a => substOne (dev b) (dev a)
  | .app f a => .app (dev f) (dev a)
  | .lam A b => .lam (dev A) (dev b)
  | .pi A B => .pi (dev A) (dev B)

/-- The triangle property. -/
theorem Par.dev (h : Par t u) : Par u (Pseudo.dev t) := by
  induction h with
  | sort s => exact .sort s
  | var n => exact .var n
  | @app f f' a a' hf _ ihf iha =>
    cases f with
    | lam A b =>
      cases hf with
      | lam _ hb =>
        change Par _ (.lam (Pseudo.dev A) (Pseudo.dev b)) at ihf
        show Par _ (Pseudo.substOne (Pseudo.dev b) (Pseudo.dev a))
        cases ihf with
        | lam _ hb' => exact .beta _ hb' iha
    | sort s => exact .app ihf iha
    | var n => exact .app ihf iha
    | app g c => exact .app ihf iha
    | pi A B => exact .app ihf iha
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | pi _ _ ih₁ ih₂ => exact .pi ih₁ ih₂
  | beta A _ _ ih₁ ih₂ => exact ih₁.substOne ih₂

theorem Par.diamond (h₁ : Par t u₁) (h₂ : Par t u₂) :
    ∃ v, Relation.ReflGen Par u₁ v ∧ Relation.ReflTransGen Par u₂ v :=
  ⟨Pseudo.dev t, .single h₁.dev, .single h₂.dev⟩

/-- Joinability by parallel reduction sequences. -/
abbrev Joinable : Pseudo S → Pseudo S → Prop := Relation.Join (Relation.ReflTransGen Par)

theorem joinable_equivalence : Equivalence (Joinable (S := S)) :=
  Relation.equivalence_join_reflTransGen (fun _ _ _ h₁ h₂ => Par.diamond h₁ h₂)

theorem reflTransGen_par_map (g : Pseudo S → Pseudo S)
    (hg : ∀ x y, Par x y → Par (g x) (g y)) (h : Relation.ReflTransGen Par x y) :
    Relation.ReflTransGen Par (g x) (g y) := by
  induction h with
  | refl => exact .refl
  | tail _ hp ih => exact ih.tail (hg _ _ hp)

theorem reflTransGen_par_app (hf : Relation.ReflTransGen Par f f')
    (ha : Relation.ReflTransGen Par a a') :
    Relation.ReflTransGen (Par (S := S)) (.app f a) (.app f' a') :=
  (reflTransGen_par_map (fun x => Pseudo.app x a)
      (fun _ _ h => Par.app h (Par.refl a)) hf).trans
    (reflTransGen_par_map (fun x => Pseudo.app f' x)
      (fun _ _ h => Par.app (Par.refl f') h) ha)

theorem reflTransGen_par_lam (hf : Relation.ReflTransGen Par f f')
    (ha : Relation.ReflTransGen Par a a') :
    Relation.ReflTransGen (Par (S := S)) (.lam f a) (.lam f' a') :=
  (reflTransGen_par_map (fun x => Pseudo.lam x a)
      (fun _ _ h => Par.lam h (Par.refl a)) hf).trans
    (reflTransGen_par_map (fun x => Pseudo.lam f' x)
      (fun _ _ h => Par.lam (Par.refl f') h) ha)

theorem reflTransGen_par_pi (hf : Relation.ReflTransGen Par f f')
    (ha : Relation.ReflTransGen Par a a') :
    Relation.ReflTransGen (Par (S := S)) (.pi f a) (.pi f' a') :=
  (reflTransGen_par_map (fun x => Pseudo.pi x a)
      (fun _ _ h => Par.pi h (Par.refl a)) hf).trans
    (reflTransGen_par_map (fun x => Pseudo.pi f' x)
      (fun _ _ h => Par.pi (Par.refl f') h) ha)

/-- Church–Rosser: convertible pseudo-terms have a common parallel reduct. -/
theorem Conv.join (h : Conv t u) : Joinable t u := by
  induction h with
  | refl t => exact joinable_equivalence.refl t
  | symm _ ih => exact joinable_equivalence.symm ih
  | trans _ _ ih₁ ih₂ => exact joinable_equivalence.trans ih₁ ih₂
  | beta A b a =>
    exact ⟨substOne b a, .single (.beta A (Par.refl b) (Par.refl a)), .refl⟩
  | app _ _ ih₁ ih₂ =>
    obtain ⟨v₁, h₁, h₁'⟩ := ih₁
    obtain ⟨v₂, h₂, h₂'⟩ := ih₂
    exact ⟨.app v₁ v₂, reflTransGen_par_app h₁ h₂, reflTransGen_par_app h₁' h₂'⟩
  | lam _ _ ih₁ ih₂ =>
    obtain ⟨v₁, h₁, h₁'⟩ := ih₁
    obtain ⟨v₂, h₂, h₂'⟩ := ih₂
    exact ⟨.lam v₁ v₂, reflTransGen_par_lam h₁ h₂, reflTransGen_par_lam h₁' h₂'⟩
  | pi _ _ ih₁ ih₂ =>
    obtain ⟨v₁, h₁, h₁'⟩ := ih₁
    obtain ⟨v₂, h₂, h₂'⟩ := ih₂
    exact ⟨.pi v₁ v₂, reflTransGen_par_pi h₁ h₂, reflTransGen_par_pi h₁' h₂'⟩

theorem rename_succ_ne_var_zero (t : Pseudo S) : t.rename Nat.succ ≠ .var 0 := by
  cases t <;> simp [rename]

/-! ## Redex-free pseudo-terms -/

/-- No β-redex occurs. -/
def NoRedex : Pseudo S → Prop
  | .sort _ => True
  | .var _ => True
  | .app f a => (∀ A b, f ≠ .lam A b) ∧ NoRedex f ∧ NoRedex a
  | .lam A b => NoRedex A ∧ NoRedex b
  | .pi A B => NoRedex A ∧ NoRedex B

theorem Par.eq_of_noRedex (h : Par t u) : NoRedex t → u = t := by
  induction h with
  | sort s => intro _; rfl
  | var n => intro _; rfl
  | app _ _ ih₁ ih₂ => intro ht; obtain ⟨_, h₁, h₂⟩ := ht; rw [ih₁ h₁, ih₂ h₂]
  | lam _ _ ih₁ ih₂ => intro ht; obtain ⟨h₁, h₂⟩ := ht; rw [ih₁ h₁, ih₂ h₂]
  | pi _ _ ih₁ ih₂ => intro ht; obtain ⟨h₁, h₂⟩ := ht; rw [ih₁ h₁, ih₂ h₂]
  | beta A _ _ _ _ => intro ht; exact absurd rfl (ht.1 A _)

theorem reflTransGen_par_eq_of_noRedex (h : Relation.ReflTransGen (Par (S := S)) t u)
    (ht : NoRedex t) : u = t := by
  induction h with
  | refl => rfl
  | tail _ hp ih => subst ih; exact hp.eq_of_noRedex ht

/-- Distinct redex-free pseudo-terms are not convertible. -/
theorem Conv.eq_of_noRedex (h : Conv t u) (ht : NoRedex t) (hu : NoRedex u) : t = u := by
  obtain ⟨v, h₁, h₂⟩ := h.join
  rw [← reflTransGen_par_eq_of_noRedex h₁ ht, reflTransGen_par_eq_of_noRedex h₂ hu]

end Pseudo

open Pseudo

/-- Generation for the newest variable: its types are convertible to the
shifted newest context entry. -/
theorem HasType.var_zero_conv {P : Specification} {Γ : List (Pseudo P.Sorts)}
    {t B : Pseudo P.Sorts} (h : HasType P Γ t B) :
    t = .var 0 → ∀ A Γ', Γ = A :: Γ' → Conv (A.rename Nat.succ) B := by
  induction h with
  | start _ => intro h; cases h
  | var _ => intro _ A Γ' hΓ; cases hΓ; exact .refl _
  | weak _ _ _ _ => intro h; exact absurd h (rename_succ_ne_var_zero _)
  | pi _ _ _ => intro h; cases h
  | lam _ _ => intro h; cases h
  | app _ _ => intro h; cases h
  | conv _ hc _ ih _ => intro h A Γ' hΓ; exact (ih h A Γ' hΓ).trans hc

end Silmaril.Calculi.LambdaCube
