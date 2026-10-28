module

public import Silmaril.Calculi.LambdaCube.PER.Cube

@[expose] public section

set_option autoImplicit true

/-! # Church–Rosser for βη-conversion of Fω constructors

Steps 1–4 of the proof outlined in `PER/OmegaConvReflect.lean`: untyped one-step
βη-reduction `Con.Step`, subject reduction into `ConEq`, Church–Rosser
(`ConEq.join`), and the resulting injectivity and disjointness of `→` and `∀`
under `ConEq`.

Source: Selinger [selinger-2008-lecture-notes-lambda-calculus], Theorem 4.2
(p. 27) and its proof in §4.4 (pp. 31–35).
-/

namespace Silmaril.Calculi.LambdaCube.PERModel.SystemFOmega

/-! ## βη-reduction of constructors -/


/-- One-step untyped βη-reduction of constructors (compatible closure). -/
inductive Con.Step : Con → Con → Prop where
  | beta : Con.Step (.app (.lam k A) B) (A.substOne B)
  | eta : Con.Step (.lam k (.app (A.rename Nat.succ) (.var 0))) A
  | arrL : Con.Step A A' → Con.Step (.arr A B) (.arr A' B)
  | arrR : Con.Step B B' → Con.Step (.arr A B) (.arr A B')
  | all : Con.Step A A' → Con.Step (.all k A) (.all k A')
  | lam : Con.Step A A' → Con.Step (.lam k A) (.lam k A')
  | appL : Con.Step A A' → Con.Step (.app A B) (.app A' B)
  | appR : Con.Step B B' → Con.Step (.app A B) (.app A B')

/-! ## Strengthening -/

/-- Kind-reflecting renamings lift under a binder. -/
theorem kunren_lift {Δ Δ' : KCtx} {r : ℕ → ℕ}
    (hr : ∀ n k', Δ'[r n]? = some k' → Δ[n]? = some k') (k : Kind) :
    ∀ n k', (k :: Δ')[scons 0 (Nat.succ ∘ r) n]? = some k' → (k :: Δ)[n]? = some k'
  | 0, k', h => by simpa using h
  | n + 1, k', h => by simpa using hr n k' (by simpa using h)

/-- Kinding is reflected by renamings that reflect the kinds of the variables. -/
theorem Kinded.unrename : ∀ (A : Con) {Δ Δ' : KCtx} {r : ℕ → ℕ} {l : Kind},
    Kinded Δ' (A.rename r) l → (∀ n k', Δ'[r n]? = some k' → Δ[n]? = some k') →
    Kinded Δ A l
  | .var n, Δ, Δ', r, l, h, hr => by
    simp only [Con.rename] at h
    cases h with | var h => exact .var (hr _ _ h)
  | .arr A B, Δ, Δ', r, l, h, hr => by
    simp only [Con.rename] at h
    cases h with
    | arr h₁ h₂ => exact .arr (Kinded.unrename A h₁ hr) (Kinded.unrename B h₂ hr)
  | .all k A, Δ, Δ', r, l, h, hr => by
    simp only [Con.rename] at h
    cases h with | all h => exact .all (Kinded.unrename A h (kunren_lift hr k))
  | .lam k A, Δ, Δ', r, l, h, hr => by
    simp only [Con.rename] at h
    cases h with | lam h => exact .lam (Kinded.unrename A h (kunren_lift hr k))
  | .app A B, Δ, Δ', r, l, h, hr => by
    simp only [Con.rename] at h
    cases h with
    | app h₁ h₂ => exact .app (Kinded.unrename A h₁ hr) (Kinded.unrename B h₂ hr)

/-- Strengthening: a kinded weakening does not use the new variable. -/
theorem Kinded.unrename_succ (h : Kinded (k :: Δ) (A.rename Nat.succ) l) : Kinded Δ A l :=
  Kinded.unrename A h (fun n k' h' => by simpa using h')

/-- Subject reduction: one βη-step from a kinded constructor is a `ConEq`. -/
theorem Con.Step.toConEq (h : Con.Step A B) : ∀ {Δ : KCtx} {k : Kind},
    Kinded Δ A k → ConEq Δ A B k := by
  induction h with
  | beta =>
    intro Δ k hA
    cases hA with
    | app h₁ h₂ => cases h₁ with | lam h₁ => exact .beta h₁ h₂
  | eta =>
    intro Δ k hA
    cases hA with
    | lam h =>
      cases h with
      | app h₁ h₂ =>
        cases h₂ with
        | var h₂ =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h₂
          subst h₂
          exact .eta (Kinded.unrename_succ h₁)
  | arrL _ ih => intro Δ k hA; cases hA with | arr h₁ h₂ => exact .arr (ih h₁) (.refl h₂)
  | arrR _ ih => intro Δ k hA; cases hA with | arr h₁ h₂ => exact .arr (.refl h₁) (ih h₂)
  | all _ ih => intro Δ k hA; cases hA with | all h => exact .all (ih h)
  | lam _ ih => intro Δ k hA; cases hA with | lam h => exact .lam (ih h)
  | appL _ ih => intro Δ k hA; cases hA with | app h₁ h₂ => exact .app (ih h₁) (.refl h₂)
  | appR _ ih => intro Δ k hA; cases hA with | app h₁ h₂ => exact .app (.refl h₁) (ih h₂)

theorem Con.reflTransGen_toConEq (h : Relation.ReflTransGen Con.Step A B) (hA : Kinded Δ A k) :
    ConEq Δ A B k := by
  induction h with
  | refl => exact .refl hA
  | tail _ hs ih => exact ih.trans (hs.toConEq ih.kinded_right)

/-! ## Congruence of multi-step reduction -/

theorem Con.Step.rtg_map {f : Con → Con} (hf : ∀ {a b}, Con.Step a b → Con.Step (f a) (f b))
    (h : Relation.ReflTransGen Con.Step a b) : Relation.ReflTransGen Con.Step (f a) (f b) := by
  induction h with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail (hf s)

theorem Con.Step.rtg_arr (h₁ : Relation.ReflTransGen Con.Step A A')
    (h₂ : Relation.ReflTransGen Con.Step B B') :
    Relation.ReflTransGen Con.Step (.arr A B) (.arr A' B') :=
  (Con.Step.rtg_map (f := fun X => .arr X B) (fun s => .arrL s) h₁).trans
    (Con.Step.rtg_map (f := fun X => .arr A' X) (fun s => .arrR s) h₂)

theorem Con.Step.rtg_app (h₁ : Relation.ReflTransGen Con.Step A A')
    (h₂ : Relation.ReflTransGen Con.Step B B') :
    Relation.ReflTransGen Con.Step (.app A B) (.app A' B') :=
  (Con.Step.rtg_map (f := fun X => .app X B) (fun s => .appL s) h₁).trans
    (Con.Step.rtg_map (f := fun X => .app A' X) (fun s => .appR s) h₂)

theorem Con.Step.rtg_all (h : Relation.ReflTransGen Con.Step A A') :
    Relation.ReflTransGen Con.Step (.all k A) (.all k A') :=
  Con.Step.rtg_map (f := fun X => .all k X) (fun s => .all s) h

theorem Con.Step.rtg_lam (h : Relation.ReflTransGen Con.Step A A') :
    Relation.ReflTransGen Con.Step (.lam k A) (.lam k A') :=
  Con.Step.rtg_map (f := fun X => .lam k X) (fun s => .lam s) h

/-! ## Free variables and renaming -/

theorem Con.freeIn_rename (A : Con) : ∀ (r : ℕ → ℕ) m, (A.rename r).FreeIn m →
    ∃ j, A.FreeIn j ∧ m = r j := by
  induction A with
  | var n => intro r m h; exact ⟨n, rfl, h⟩
  | arr A B ihA ihB =>
    intro r m h
    simp only [Con.rename, Con.FreeIn] at h
    rcases h with h | h
    · obtain ⟨j, hj, rfl⟩ := ihA r m h; exact ⟨j, Or.inl hj, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := ihB r m h; exact ⟨j, Or.inr hj, rfl⟩
  | all k A ih =>
    intro r m h
    simp only [Con.rename, Con.FreeIn] at h
    obtain ⟨j, hj, he⟩ := ih (scons 0 (Nat.succ ∘ r)) (m + 1) h
    cases j with
    | zero => simp at he
    | succ j => exact ⟨j, hj, by simp at he; omega⟩
  | lam k A ih =>
    intro r m h
    simp only [Con.rename, Con.FreeIn] at h
    obtain ⟨j, hj, he⟩ := ih (scons 0 (Nat.succ ∘ r)) (m + 1) h
    cases j with
    | zero => simp at he
    | succ j => exact ⟨j, hj, by simp at he; omega⟩
  | app A B ihA ihB =>
    intro r m h
    simp only [Con.rename, Con.FreeIn] at h
    rcases h with h | h
    · obtain ⟨j, hj, rfl⟩ := ihA r m h; exact ⟨j, Or.inl hj, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := ihB r m h; exact ⟨j, Or.inr hj, rfl⟩

theorem Con.freeIn_rename_of (A : Con) : ∀ (r : ℕ → ℕ) j, A.FreeIn j →
    (A.rename r).FreeIn (r j) := by
  induction A with
  | var n =>
    intro r j h
    simp only [Con.FreeIn] at h
    subst h
    simp [Con.rename, Con.FreeIn]
  | arr A B ihA ihB =>
    intro r j h
    simp only [Con.rename, Con.FreeIn] at h ⊢
    exact h.imp (ihA r j) (ihB r j)
  | all k A ih =>
    intro r j h
    simp only [Con.rename, Con.FreeIn] at h ⊢
    exact ih (scons 0 (Nat.succ ∘ r)) (j + 1) h
  | lam k A ih =>
    intro r j h
    simp only [Con.rename, Con.FreeIn] at h ⊢
    exact ih (scons 0 (Nat.succ ∘ r)) (j + 1) h
  | app A B ihA ihB =>
    intro r j h
    simp only [Con.rename, Con.FreeIn] at h ⊢
    exact h.imp (ihA r j) (ihB r j)

theorem Con.freeIn_subst (A : Con) : ∀ (σ : ℕ → Con) m, (A.subst σ).FreeIn m →
    ∃ j, A.FreeIn j ∧ (σ j).FreeIn m := by
  induction A with
  | var n => intro σ m h; exact ⟨n, rfl, h⟩
  | arr A B ihA ihB =>
    intro σ m h
    simp only [Con.subst, Con.FreeIn] at h
    rcases h with h | h
    · obtain ⟨j, hj, h'⟩ := ihA σ m h; exact ⟨j, Or.inl hj, h'⟩
    · obtain ⟨j, hj, h'⟩ := ihB σ m h; exact ⟨j, Or.inr hj, h'⟩
  | all k A ih =>
    intro σ m h
    simp only [Con.subst, Con.FreeIn] at h
    obtain ⟨j, hj, h'⟩ := ih (Con.liftSub σ) (m + 1) h
    cases j with
    | zero => simp [Con.liftSub, Con.FreeIn] at h'
    | succ j =>
      simp only [Con.liftSub, scons_succ] at h'
      obtain ⟨i, hi, he⟩ := (σ j).freeIn_rename _ _ h'
      exact ⟨j, hj, by rw [show m = i by simp at he; omega]; exact hi⟩
  | lam k A ih =>
    intro σ m h
    simp only [Con.subst, Con.FreeIn] at h
    obtain ⟨j, hj, h'⟩ := ih (Con.liftSub σ) (m + 1) h
    cases j with
    | zero => simp [Con.liftSub, Con.FreeIn] at h'
    | succ j =>
      simp only [Con.liftSub, scons_succ] at h'
      obtain ⟨i, hi, he⟩ := (σ j).freeIn_rename _ _ h'
      exact ⟨j, hj, by rw [show m = i by simp at he; omega]; exact hi⟩
  | app A B ihA ihB =>
    intro σ m h
    simp only [Con.subst, Con.FreeIn] at h
    rcases h with h | h
    · obtain ⟨j, hj, h'⟩ := ihA σ m h; exact ⟨j, Or.inl hj, h'⟩
    · obtain ⟨j, hj, h'⟩ := ihB σ m h; exact ⟨j, Or.inr hj, h'⟩

/-- Substitutions agreeing on the free variables act alike. -/
theorem Con.subst_congr (A : Con) : ∀ σ τ : ℕ → Con, (∀ m, A.FreeIn m → σ m = τ m) →
    A.subst σ = A.subst τ := by
  have hl : ∀ (A : Con) (σ τ : ℕ → Con), (∀ m, A.FreeIn (m + 1) → σ m = τ m) →
      ∀ m, A.FreeIn m → Con.liftSub σ m = Con.liftSub τ m := by
    intro A σ τ h m hm
    cases m with
    | zero => rfl
    | succ m => simp only [Con.liftSub, scons_succ]; rw [h m hm]
  induction A with
  | var n => intro σ τ h; exact h n rfl
  | arr A B ihA ihB =>
    intro σ τ h
    simp only [Con.subst]
    rw [ihA σ τ (fun m hm => h m (Or.inl hm)), ihB σ τ (fun m hm => h m (Or.inr hm))]
  | all k A ih =>
    intro σ τ h
    simp only [Con.subst]
    rw [ih _ _ (hl A σ τ h)]
  | lam k A ih =>
    intro σ τ h
    simp only [Con.subst]
    rw [ih _ _ (hl A σ τ h)]
  | app A B ihA ihB =>
    intro σ τ h
    simp only [Con.subst]
    rw [ihA σ τ (fun m hm => h m (Or.inl hm)), ihB σ τ (fun m hm => h m (Or.inr hm))]

theorem Con.rename_subst (A : Con) (σ : ℕ → Con) (r : ℕ → ℕ) :
    (A.subst σ).rename r = A.subst (fun n => (σ n).rename r) := by
  apply Con.toPseudo_inj _ _ []
  rw [Con.toPseudo_nil_rename, Con.toPseudo_nil_subst, Con.toPseudo_nil_subst,
    Pseudo.rename_subst]
  congr 1
  funext n
  simp [Function.comp, Con.toPseudo_nil_rename]

theorem Con.subst_rename (A : Con) (σ : ℕ → Con) (r : ℕ → ℕ) :
    (A.rename r).subst σ = A.subst (σ ∘ r) := by
  apply Con.toPseudo_inj _ _ []
  rw [Con.toPseudo_nil_subst, Con.toPseudo_nil_rename, Con.toPseudo_nil_subst,
    Pseudo.subst_rename]
  rfl

theorem Con.not_freeIn_zero_rename_succ (A : Con) : ¬ (A.rename Nat.succ).FreeIn 0 := by
  intro h
  obtain ⟨j, _, e⟩ := A.freeIn_rename _ _ h
  exact Nat.succ_ne_zero j e.symm

/-- A constructor without free variable `0` is a weakening. -/
theorem Con.rename_succ_substOne_of_not_freeIn {B : Con} (h : ¬ B.FreeIn 0) (C : Con) :
    (B.substOne C).rename Nat.succ = B := by
  rw [Con.substOne, Con.rename_subst,
    Con.subst_congr B _ Con.var (fun m hm => by
      cases m with
      | zero => exact absurd hm h
      | succ m => rfl)]
  exact Con.subst_eq_self B Con.var (fun _ => rfl)

theorem Con.rename_lift_succ_substOne_var (X : Con) :
    (X.rename (scons 0 (Nat.succ ∘ Nat.succ))).substOne (.var 0) = X := by
  rw [Con.substOne, Con.subst_rename]
  exact Con.subst_eq_self X _ (fun n => by cases n <;> rfl)

/-! ## Parallel βη-reduction (Selinger §4.4) -/

/-- Parallel one-step βη-reduction of constructors (Selinger, rules (1)–(5)). -/
inductive Con.Par : Con → Con → Prop where
  | var {n : ℕ} : Con.Par (.var n) (.var n)
  | arr {A A' B B' : Con} : Con.Par A A' → Con.Par B B' → Con.Par (.arr A B) (.arr A' B')
  | all {k : Kind} {A A' : Con} : Con.Par A A' → Con.Par (.all k A) (.all k A')
  | lam {k : Kind} {A A' : Con} : Con.Par A A' → Con.Par (.lam k A) (.lam k A')
  | app {A A' B B' : Con} : Con.Par A A' → Con.Par B B' → Con.Par (.app A B) (.app A' B')
  | beta {k : Kind} {A A' B B' : Con} : Con.Par A A' → Con.Par B B' →
      Con.Par (.app (.lam k A) B) (A'.substOne B')
  | eta {k : Kind} {A A' : Con} : Con.Par A A' →
      Con.Par (.lam k (.app (A.rename Nat.succ) (.var 0))) A'

theorem Con.Par.refl : ∀ A : Con, Con.Par A A
  | .var _ => .var
  | .arr A B => .arr (Con.Par.refl A) (Con.Par.refl B)
  | .all _ A => .all (Con.Par.refl A)
  | .lam _ A => .lam (Con.Par.refl A)
  | .app A B => .app (Con.Par.refl A) (Con.Par.refl B)

/-- Selinger, Lemma 4.6(a). -/
theorem Con.Step.par (h : Con.Step A B) : Con.Par A B := by
  induction h with
  | beta => exact .beta (.refl _) (.refl _)
  | eta => exact .eta (.refl _)
  | arrL _ ih => exact .arr ih (.refl _)
  | arrR _ ih => exact .arr (.refl _) ih
  | all _ ih => exact .all ih
  | lam _ ih => exact .lam ih
  | appL _ ih => exact .app ih (.refl _)
  | appR _ ih => exact .app (.refl _) ih

/-- Selinger, Lemma 4.6(b). -/
theorem Con.Par.rtg (h : Con.Par A B) : Relation.ReflTransGen Con.Step A B := by
  induction h with
  | var => exact .refl
  | arr _ _ ih₁ ih₂ => exact Con.Step.rtg_arr ih₁ ih₂
  | all _ ih => exact Con.Step.rtg_all ih
  | lam _ ih => exact Con.Step.rtg_lam ih
  | app _ _ ih₁ ih₂ => exact Con.Step.rtg_app ih₁ ih₂
  | beta _ _ ih₁ ih₂ => exact (Con.Step.rtg_app (Con.Step.rtg_lam ih₁) ih₂).tail .beta
  | eta _ ih => exact Relation.ReflTransGen.head .eta ih

theorem Con.Par.kinded (h : Con.Par A B) (hA : Kinded Δ A k) : Kinded Δ B k :=
  (Con.reflTransGen_toConEq h.rtg hA).kinded_right

theorem Con.Par.rename (h : Con.Par A B) (r : ℕ → ℕ) : Con.Par (A.rename r) (B.rename r) := by
  induction h generalizing r with
  | var => exact .var
  | arr _ _ ih₁ ih₂ => exact .arr (ih₁ r) (ih₂ r)
  | all _ ih => exact .all (ih _)
  | lam _ ih => exact .lam (ih _)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ r) (ih₂ r)
  | beta _ _ ih₁ ih₂ =>
    rw [Con.rename_substOne]
    exact .beta (ih₁ _) (ih₂ r)
  | eta _ ih =>
    simp only [Con.rename, scons_zero]
    rw [Con.rename_succ_comm]
    exact .eta (ih r)

theorem Con.Par.subst (h : Con.Par A B) {σ τ : ℕ → Con} (hσ : ∀ n, Con.Par (σ n) (τ n)) :
    Con.Par (A.subst σ) (B.subst τ) := by
  have hl : ∀ {σ τ : ℕ → Con}, (∀ n, Con.Par (σ n) (τ n)) →
      ∀ n, Con.Par (Con.liftSub σ n) (Con.liftSub τ n) := by
    intro σ τ h n
    cases n with
    | zero => exact .var
    | succ n => exact (h n).rename Nat.succ
  induction h generalizing σ τ with
  | var => exact hσ _
  | arr _ _ ih₁ ih₂ => exact .arr (ih₁ hσ) (ih₂ hσ)
  | all _ ih => exact .all (ih (hl hσ))
  | lam _ ih => exact .lam (ih (hl hσ))
  | app _ _ ih₁ ih₂ => exact .app (ih₁ hσ) (ih₂ hσ)
  | beta _ _ ih₁ ih₂ =>
    rw [Con.subst_substOne]
    exact .beta (ih₁ (hl hσ)) (ih₂ hσ)
  | eta _ ih =>
    simp only [Con.subst]
    rw [Con.rename_succ_subst_liftSub]
    exact .eta (ih hσ)

/-- Selinger, Lemma 4.7. -/
theorem Con.Par.substOne (h : Con.Par A A') (h' : Con.Par B B') :
    Con.Par (A.substOne B) (A'.substOne B') :=
  h.subst fun n => by
    cases n with
    | zero => exact h'
    | succ n => exact .var

theorem Con.Par.freeIn (h : Con.Par A B) : ∀ m, B.FreeIn m → A.FreeIn m := by
  induction h with
  | var => exact fun _ h => h
  | arr _ _ ih₁ ih₂ => intro m h; exact h.imp (ih₁ m) (ih₂ m)
  | all _ ih => intro m h; exact ih (m + 1) h
  | lam _ ih => intro m h; exact ih (m + 1) h
  | app _ _ ih₁ ih₂ => intro m h; exact h.imp (ih₁ m) (ih₂ m)
  | @beta k A A' B B' _ _ ih₁ ih₂ =>
    intro m h
    obtain ⟨j, hj, h'⟩ := Con.freeIn_subst A' (scons B' Con.var) m h
    cases j with
    | zero => exact Or.inr (ih₂ m h')
    | succ j =>
      simp only [scons_succ, Con.FreeIn] at h'
      subst h'
      exact Or.inl (ih₁ _ hj)
  | eta _ ih =>
    intro m h
    exact Or.inl (Con.freeIn_rename_of _ Nat.succ m (ih m h))

/-- Parallel reduction from a weakening stays a weakening. -/
theorem Con.Par.unrename_succ (h : Con.Par (A.rename Nat.succ) B) :
    ∃ B', B = B'.rename Nat.succ ∧ Con.Par A B' := by
  refine ⟨B.substOne (.var 0), (Con.rename_succ_substOne_of_not_freeIn
    (fun hB => A.not_freeIn_zero_rename_succ (h.freeIn 0 hB)) _).symm, ?_⟩
  have := h.substOne (Con.Par.refl (.var 0))
  rwa [Con.rename_succ_substOne] at this

theorem Con.Par.lam_inv (h : Con.Par (.lam k N) M') :
    (∃ N', M' = .lam k N' ∧ Con.Par N N') ∨
      (∃ P, N = .app (P.rename Nat.succ) (.var 0) ∧ Con.Par P M') := by
  cases h with
  | lam h => exact Or.inl ⟨_, rfl, h⟩
  | eta h => exact Or.inr ⟨_, rfl, h⟩

theorem Con.Par.app_inv (h : Con.Par (.app X Y) M') :
    (∃ X' Y', M' = .app X' Y' ∧ Con.Par X X' ∧ Con.Par Y Y') ∨
      (∃ k Q Q' Y', X = .lam k Q ∧ M' = Q'.substOne Y' ∧ Con.Par Q Q' ∧ Con.Par Y Y') := by
  cases h with
  | app h₁ h₂ => exact Or.inl ⟨_, _, rfl, h₁, h₂⟩
  | beta h₁ h₂ => exact Or.inr ⟨_, _, _, _, rfl, rfl, h₁, h₂⟩

/-- Selinger, Lemma 4.8, for kinded constructors: every kinded `M` has a common
parallel reduct `Z` (the maximal parallel reduct) of all its parallel reducts.
Kinding is needed in the η-case: `λk. (λk'. Q)↑ 0` reduces to both `λk'. Q` (η) and
`λk. Q` (β under `λ`), which agree only because kinding forces `k = k'`. -/
theorem Con.Par.triangle_aux : ∀ (n : ℕ) (M : Con), sizeOf M < n → ∀ {Δ : KCtx} {k : Kind},
    Kinded Δ M k → ∃ Z, ∀ M', Con.Par M M' → Con.Par M' Z := by
  intro n
  induction n with
  | zero => intro M h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro M hM Δ k hK
    cases M with
    | var m => exact ⟨.var m, fun M' h => by cases h; exact .var⟩
    | arr A B =>
      cases hK with
      | arr hA hB =>
        obtain ⟨ZA, hZA⟩ := ih A (by simp at hM; omega) hA
        obtain ⟨ZB, hZB⟩ := ih B (by simp at hM; omega) hB
        exact ⟨.arr ZA ZB, fun M' h => by
          cases h with | arr h₁ h₂ => exact .arr (hZA _ h₁) (hZB _ h₂)⟩
    | all k₀ A =>
      cases hK with
      | all hA =>
        obtain ⟨ZA, hZA⟩ := ih A (by simp at hM; omega) hA
        exact ⟨.all k₀ ZA, fun M' h => by cases h with | all h => exact .all (hZA _ h)⟩
    | app A B =>
      cases hK with
      | app hA hB =>
        obtain ⟨ZB, hZB⟩ := ih B (by simp at hM; omega) hB
        by_cases hl : ∃ (k₀ : Kind) (Q : Con), A = .lam k₀ Q
        · obtain ⟨k₀, Q, rfl⟩ := hl
          cases hA with
          | lam hQ =>
            obtain ⟨ZQ, hZQ⟩ := ih Q (by simp at hM; omega) hQ
            refine ⟨ZQ.substOne ZB, fun M' h => ?_⟩
            rcases h.app_inv with ⟨L, B', rfl, hL, hB'⟩ | ⟨k₁, Q₁, Q', B', e, rfl, hQ', hB'⟩
            · rcases hL.lam_inv with ⟨Q', rfl, hQ'⟩ | ⟨R, rfl, hR⟩
              · exact .beta (hZQ _ hQ') (hZB _ hB')
              · have h₂ := (hZQ _ (.app (hR.rename Nat.succ) .var)).substOne (hZB _ hB')
                have e : (Con.app (L.rename Nat.succ) (.var 0)).substOne B' = .app L B' := by
                  change Con.app ((L.rename Nat.succ).substOne B') B' = _
                  rw [Con.rename_succ_substOne]
                rw [e] at h₂
                exact h₂
            · cases e
              exact (hZQ _ hQ').substOne (hZB _ hB')
        · obtain ⟨ZA, hZA⟩ := ih A (by simp at hM; omega) hA
          refine ⟨.app ZA ZB, fun M' h => ?_⟩
          rcases h.app_inv with ⟨A', B', rfl, h₁, h₂⟩ | ⟨k₁, Q₁, Q', B', e, -, -, -⟩
          · exact .app (hZA _ h₁) (hZB _ h₂)
          · exact absurd ⟨k₁, Q₁, e⟩ hl
    | lam k₀ N =>
      cases hK with
      | lam hN =>
        by_cases hη : ∃ P : Con, N = .app (P.rename Nat.succ) (.var 0)
        · obtain ⟨P, rfl⟩ := hη
          cases hN with
          | app hP hv =>
            cases hv with
            | var hv =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
              subst hv
              obtain ⟨ZP', hZP'⟩ := ih (P.rename Nat.succ) (by simp at hM; omega) hP
              have hZP : ∀ P', Con.Par P P' → Con.Par P' (ZP'.substOne (.var 0)) := by
                intro P' h
                have := (hZP' _ (h.rename Nat.succ)).substOne (Con.Par.refl (.var 0))
                rwa [Con.rename_succ_substOne] at this
              refine ⟨ZP'.substOne (.var 0), fun M' h => ?_⟩
              rcases h.lam_inv with ⟨N', rfl, hN'⟩ | ⟨P₁, e, hP₁⟩
              · rcases hN'.app_inv with ⟨X', Y', rfl, hX', hY'⟩ |
                  ⟨k₁, Q, Q', Y', e, rfl, hQ', hY'⟩
                · cases hY'
                  obtain ⟨P', rfl, hP'⟩ := hX'.unrename_succ
                  exact .eta (hZP _ hP')
                · cases hY'
                  have hPQ : Con.Par (P.rename Nat.succ) (.lam k₁ Q') := e ▸ .lam hQ'
                  obtain ⟨X, eX, hX⟩ := hPQ.unrename_succ
                  rw [e] at hP
                  cases hP with
                  | lam _ =>
                    cases X with
                    | lam k₂ X₁ =>
                      simp only [Con.rename] at eX
                      cases eX
                      rw [Con.rename_lift_succ_substOne_var]
                      exact hZP _ hX
                    | var _ => simp [Con.rename] at eX
                    | arr _ _ => simp [Con.rename] at eX
                    | all _ _ => simp [Con.rename] at eX
                    | app _ _ => simp [Con.rename] at eX
              · injection e with e₁ _
                have e₂ := congrArg (fun X => Con.substOne X (.var 0)) e₁
                simp only [Con.rename_succ_substOne] at e₂
                subst e₂
                exact hZP _ hP₁
        · obtain ⟨ZN, hZN⟩ := ih N (by simp at hM; omega) hN
          refine ⟨.lam k₀ ZN, fun M' h => ?_⟩
          rcases h.lam_inv with ⟨N', rfl, hN'⟩ | ⟨P, e, -⟩
          · exact .lam (hZN _ hN')
          · exact absurd ⟨P, e⟩ hη

theorem Con.Par.triangle (hM : Kinded Δ M k) : ∃ Z, ∀ M', Con.Par M M' → Con.Par M' Z :=
  Con.Par.triangle_aux _ M (Nat.lt_succ_self _) hM

/-- Parallel reduction restricted to constructors of kind `k` in `Δ`. -/
def Con.ParK (Δ : KCtx) (k : Kind) (X Y : Con) : Prop := Kinded Δ X k ∧ Con.Par X Y

/-- Church–Rosser for βη-reduction from a kinded constructor (Selinger, Theorem 4.2). -/
theorem Con.confluent (hA : Kinded Δ A k) (h₁ : Relation.ReflTransGen Con.Step A B)
    (h₂ : Relation.ReflTransGen Con.Step A C) :
    Relation.Join (Relation.ReflTransGen Con.Step) B C := by
  have toK : ∀ {B}, Relation.ReflTransGen Con.Step A B →
      Relation.ReflTransGen (Con.ParK Δ k) A B := by
    intro B h
    induction h with
    | refl => exact .refl
    | tail hX s ih => exact ih.tail ⟨(Con.reflTransGen_toConEq hX hA).kinded_right, s.par⟩
  have ofK : ∀ {X Y}, Relation.ReflTransGen (Con.ParK Δ k) X Y →
      Relation.ReflTransGen Con.Step X Y := by
    intro X Y h
    induction h with
    | refl => exact .refl
    | tail _ s ih => exact ih.trans s.2.rtg
  have hd : ∀ a b c, Con.ParK Δ k a b → Con.ParK Δ k a c →
      ∃ d, Relation.ReflGen (Con.ParK Δ k) b d ∧ Relation.ReflTransGen (Con.ParK Δ k) c d := by
    intro a b c hb hc
    obtain ⟨Z, hZ⟩ := Con.Par.triangle hb.1
    exact ⟨Z, .single ⟨hb.2.kinded hb.1, hZ _ hb.2⟩, .single ⟨hc.2.kinded hc.1, hZ _ hc.2⟩⟩
  obtain ⟨D, hB, hC⟩ := Relation.church_rosser hd (toK h₁) (toK h₂)
  exact ⟨D, ofK hB, ofK hC⟩

/-- Church–Rosser for βη: `ConEq`-equal constructors have a common reduct. -/
theorem ConEq.join (h : ConEq Δ A B k) : Relation.Join (Relation.ReflTransGen Con.Step) A B := by
  induction h with
  | refl _ => exact ⟨_, .refl, .refl⟩
  | symm _ ih => obtain ⟨D, a, b⟩ := ih; exact ⟨D, b, a⟩
  | trans h₁ _ ih₁ ih₂ =>
    obtain ⟨D₁, a₁, b₁⟩ := ih₁
    obtain ⟨D₂, b₂, c₂⟩ := ih₂
    obtain ⟨E, d₁, d₂⟩ := Con.confluent h₁.kinded_right b₁ b₂
    exact ⟨E, a₁.trans d₁, c₂.trans d₂⟩
  | beta _ _ => exact ⟨_, .single .beta, .refl⟩
  | eta _ => exact ⟨_, .single .eta, .refl⟩
  | arr _ _ ih₁ ih₂ =>
    obtain ⟨D, a, a'⟩ := ih₁
    obtain ⟨E, b, b'⟩ := ih₂
    exact ⟨.arr D E, Con.Step.rtg_arr a b, Con.Step.rtg_arr a' b'⟩
  | all _ ih =>
    obtain ⟨D, a, a'⟩ := ih
    exact ⟨.all _ D, Con.Step.rtg_all a, Con.Step.rtg_all a'⟩
  | lam _ ih =>
    obtain ⟨D, a, a'⟩ := ih
    exact ⟨.lam _ D, Con.Step.rtg_lam a, Con.Step.rtg_lam a'⟩
  | app _ _ ih₁ ih₂ =>
    obtain ⟨D, a, a'⟩ := ih₁
    obtain ⟨E, b, b'⟩ := ih₂
    exact ⟨.app D E, Con.Step.rtg_app a b, Con.Step.rtg_app a' b'⟩

/-- Joinable kinded constructors of the same kind are `ConEq`. -/
theorem ConEq.of_join (hA : Kinded Δ A k) (hB : Kinded Δ B k)
    (h : Relation.Join (Relation.ReflTransGen Con.Step) A B) : ConEq Δ A B k := by
  obtain ⟨C, h₁, h₂⟩ := h
  exact (Con.reflTransGen_toConEq h₁ hA).trans (Con.reflTransGen_toConEq h₂ hB).symm

theorem Con.reflTransGen_arr_inv (h : Relation.ReflTransGen Con.Step (.arr A B) C) :
    ∃ A' B', C = .arr A' B' ∧ Relation.ReflTransGen Con.Step A A' ∧
      Relation.ReflTransGen Con.Step B B' := by
  induction h with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | tail _ s ih =>
    obtain ⟨A', B', rfl, hA, hB⟩ := ih
    cases s with
    | arrL s => exact ⟨_, _, rfl, hA.tail s, hB⟩
    | arrR s => exact ⟨_, _, rfl, hA, hB.tail s⟩

theorem Con.reflTransGen_all_inv (h : Relation.ReflTransGen Con.Step (.all k A) C) :
    ∃ A', C = .all k A' ∧ Relation.ReflTransGen Con.Step A A' := by
  induction h with
  | refl => exact ⟨A, rfl, .refl⟩
  | tail _ s ih =>
    obtain ⟨A', rfl, hA⟩ := ih
    cases s with
    | all s => exact ⟨_, rfl, hA.tail s⟩

theorem ConEq.arr_inj (h : ConEq Δ (.arr X Y) (.arr X' Y') .star) :
    ConEq Δ X X' .star ∧ ConEq Δ Y Y' .star := by
  obtain ⟨C, h₁, h₂⟩ := h.join
  obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Con.reflTransGen_arr_inv h₁
  obtain ⟨A₂, B₂, e, hA₂, hB₂⟩ := Con.reflTransGen_arr_inv h₂
  injection e with e₁ e₂
  subst e₁ e₂
  cases h.kinded_left with
  | arr hX hY =>
    cases h.kinded_right with
    | arr hX' hY' => exact ⟨ConEq.of_join hX hX' ⟨_, hA₁, hA₂⟩, ConEq.of_join hY hY' ⟨_, hB₁, hB₂⟩⟩

theorem ConEq.all_inj (h : ConEq Δ (.all k Y) (.all k' Y') .star) :
    k = k' ∧ ConEq (k :: Δ) Y Y' .star := by
  obtain ⟨C, h₁, h₂⟩ := h.join
  obtain ⟨A₁, rfl, hA₁⟩ := Con.reflTransGen_all_inv h₁
  obtain ⟨A₂, e, hA₂⟩ := Con.reflTransGen_all_inv h₂
  injection e with e₁ e₂
  subst e₁ e₂
  cases h.kinded_left with
  | all hY =>
    cases h.kinded_right with
    | all hY' => exact ⟨rfl, ConEq.of_join hY hY' ⟨_, hA₁, hA₂⟩⟩

theorem ConEq.arr_ne_all (h : ConEq Δ (.arr X Y) (.all k Y') .star) : False := by
  obtain ⟨C, h₁, h₂⟩ := h.join
  obtain ⟨A₁, B₁, rfl, _, _⟩ := Con.reflTransGen_arr_inv h₁
  obtain ⟨A₂, e, _⟩ := Con.reflTransGen_all_inv h₂
  cases e


end Silmaril.Calculi.LambdaCube.PERModel.SystemFOmega
