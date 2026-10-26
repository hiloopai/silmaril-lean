module

public import Silmaril.Calculi.PCF.Definability

/-! # Definability of finite elements and density in PCF+`por`

We show that every monotone function of the environment which factors through the
`n`-th projections is definable by a PCF+`por` term (`DefinableAt`), given tests at
the types of the context:

* at a ground type (`definableAt_base`), the defining term is an if-chain over the
  finitely many non-`⊥` fixed values `v`, guarded by the parallel disjunction of the
  environment tests of the finitely many fixed environments `ē` with `g ē = v`;
* at an arrow type (`definableAt_arrow`), by currying.

Together with the tests of `Silmaril.Calculi.PCF.Definability`, an induction on types
(`hasTests_and_definableAt`) shows that every fixed point of a projection, i.e. every
finite element, is definable (`exists_denoteClosed_eq_proj`), so that every element of
the model is the supremum of a chain of definable elements (`exists_chain_definable`).
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open OmegaCompletePartialOrder Silmaril.Semantics.Domain TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

variable {Γ : Ctx Base} {σ τ : Ty} {n : ℕ}

/-- Every monotone `g` that factors through the `n`-th projections is definable in `Γ`. -/
def DefinableAt (n : ℕ) (Γ : Ctx Base) (τ : Ty) : Prop :=
  ∀ g : (model true).Env Γ → (model true).ty τ, Monotone g →
    (∀ ρ, proj n τ (g (projEnv n ρ)) = g ρ) → ∃ t : Term true Γ τ, ∀ ρ, denote t ρ = g ρ

/-- A function factoring through the projections is invariant under projecting its
argument. -/
theorem apply_projEnv_of_proj {g : (model true).Env Γ → (model true).ty τ}
    (hproj : ∀ ρ, proj n τ (g (projEnv n ρ)) = g ρ) (ρ : (model true).Env Γ) :
    g (projEnv n ρ) = g ρ := by
  have h := hproj (projEnv n ρ)
  rw [projEnv_projEnv] at h
  exact h.symm.trans (hproj ρ)

/-- A function factoring through the projections has fixed values. -/
theorem proj_apply_of_proj {g : (model true).Env Γ → (model true).ty τ}
    (hproj : ∀ ρ, proj n τ (g (projEnv n ρ)) = g ρ) (ρ : (model true).Env Γ) :
    proj n τ (g ρ) = g ρ := by
  have h := hproj ρ
  rwa [apply_projEnv_of_proj hproj] at h

/-- Ground definability: an if-chain over the non-`⊥` fixed values, guarded by
parallel disjunctions of environment tests. -/
theorem definableAt_base (hΓ : ∀ a (_ : Var Γ a), HasTests n a) (b : Base) :
    DefinableAt n Γ (.base b) := by
  classical
  intro g hg hproj
  choose TEST hTEST using exists_envTest hΓ
  obtain ⟨V, hV, hVall⟩ := exists_values n b
  have hw : ∀ v, ∃ w : Closed true (.base b), v ∈ V → denoteClosed w = v := fun v => by
    by_cases hv : v ∈ V
    · obtain ⟨w, hw⟩ := (hV v hv).2
      exact ⟨w, fun _ => hw⟩
    · exact ⟨Term.omega _, fun h => absurd h hv⟩
  choose w hw using hw
  let E := (finite_fixed_projEnv n Γ).toFinset
  have hE : ∀ ē, ē ∈ E ↔ projEnv n ē = ē := fun ē => by simp [E]
  let G : (model true).ty (.base b) → Term true Γ .bool := fun v =>
    Term.porList (((E.filter fun ē => g ē = v).toList).map TEST)
  have hmemG : ∀ v t, t ∈ ((E.filter fun ē => g ē = v).toList).map TEST ↔
      ∃ ē, (projEnv n ē = ē ∧ g ē = v) ∧ TEST ē = t := fun v t => by
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, hE]
  let l : List (Term true Γ .bool × Term true Γ (.base b)) :=
    V.map fun v => (G v, Term.ofClosed (w v))
  refine ⟨Term.ifChain l, fun ρ => ?_⟩
  have hGtt : ∀ v, (denote (G v) ρ : Part Bool) = .some true →
      ∃ ē, projEnv n ē = ē ∧ g ē = v ∧ ē ≤ projEnv n ρ := fun v h => by
    obtain ⟨t, ht, htt⟩ := (denote_porList_eq_true_iff _ ρ).1 h
    obtain ⟨ē, ⟨hfix, hgē⟩, rfl⟩ := (hmemG v t).1 ht
    exact ⟨ē, hfix, hgē, ((hTEST ē hfix ρ).1).1 htt⟩
  have hlit : ∀ v ∈ V, denote (Term.ofClosed (w v) : Term true Γ (.base b)) ρ = v :=
    fun v hv => by
      change (model true).denote (Term.ofClosed (w v)) ρ = v
      rw [Model.denote_ofClosed]
      exact hw v hv
  have hmeml : ∀ q ∈ l, ∃ v ∈ V, q = (G v, Term.ofClosed (w v)) := fun q hq => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hq
    exact ⟨v, hv, rfl⟩
  by_cases hbot : g ρ = ⊥
  · rw [hbot]
    refine denote_ifChain_eq_bot fun q hq htt => ?_
    obtain ⟨v, hv, rfl⟩ := hmeml q hq
    obtain ⟨ē, -, hgē, hle⟩ := hGtt v htt
    have : v ≤ g ρ := by
      rw [← hgē, ← apply_projEnv_of_proj hproj ρ]
      exact hg hle
    rw [hbot, le_bot_iff] at this
    exact (hV v hv).1 this
  · have hmemV : g ρ ∈ V := hVall _ (proj_apply_of_proj hproj ρ) hbot
    have hGself : (denote (G (g ρ)) ρ : Part Bool) = .some true := by
      refine (denote_porList_eq_true_iff _ ρ).2 ⟨TEST (projEnv n ρ), ?_, ?_⟩
      · exact (hmemG _ _).2
          ⟨projEnv n ρ, ⟨projEnv_projEnv n ρ, apply_projEnv_of_proj hproj ρ⟩, rfl⟩
      · exact ((hTEST _ (projEnv_projEnv n ρ) ρ).1).2 le_rfl
    refine denote_ifChain_eq (fun q hq => ?_)
      ⟨(G (g ρ), Term.ofClosed (w (g ρ))), List.mem_map.2 ⟨g ρ, hmemV, rfl⟩, hGself⟩
    obtain ⟨v, hv, rfl⟩ := hmeml q hq
    by_cases hvg : v = g ρ
    · subst hvg
      exact Or.inl ⟨hGself, hlit _ hv⟩
    · refine Or.inr (denote_porList_of_forall_false fun t ht => ?_)
      obtain ⟨ē, ⟨hfix, hgē⟩, rfl⟩ := (hmemG v t).1 ht
      refine (hTEST ē hfix ρ).2 ?_
      by_contra hall
      push Not at hall
      obtain ⟨c, hēc, hρc⟩ := exists_le_le_of_forall_bddAbove₂ (y := projEnv n ρ) hall
      have h₁ : v ≤ g c := by rw [← hgē]; exact hg hēc
      have h₂ : g ρ ≤ g c := by rw [← apply_projEnv_of_proj hproj ρ]; exact hg hρc
      have e₁ := (base_le_iff.1 h₁).resolve_left (hV v hv).1
      have e₂ := (base_le_iff.1 h₂).resolve_left hbot
      exact hvg (e₁.trans e₂.symm)

/-- Arrow definability, by currying. -/
theorem definableAt_arrow (h : DefinableAt n (σ :: Γ) τ) : DefinableAt n Γ (σ ⤳ τ) := by
  intro g hg hproj
  let g' : (model true).Env (σ :: Γ) → (model true).ty τ := fun ρ' =>
    Model.app (g (Tuple.tail ρ')) (Tuple.head ρ')
  have hg' : Monotone g' := fun ρ₁ ρ₂ hρ =>
    le_trans ((Model.fn (g (Tuple.tail ρ₁))).monotone ((Model.env_cons_le_iff.1 hρ).1))
      (hg (Model.env_cons_le_iff.1 hρ).2 _)
  have hproj' : ∀ ρ', proj n τ (g' (projEnv n ρ')) = g' ρ' := fun ρ' => by
    change proj n τ (Model.app (g (projEnv n (Tuple.tail ρ'))) (proj n σ (Tuple.head ρ'))) =
      Model.app (g (Tuple.tail ρ')) (Tuple.head ρ')
    rw [← app_proj, hproj]
  obtain ⟨t, ht⟩ := h g' hg' hproj'
  refine ⟨.lam t, fun ρ => Model.ext_app fun d => ?_⟩
  change denote t (d ::ₜ ρ) = _
  exact ht _

/-- The main induction on types: tests exist at every type, and every function
factoring through the projections is definable in any context with tests. -/
theorem hasTests_and_definableAt (n : ℕ) : ∀ τ : Ty, HasTests n τ ∧
    ∀ Γ, (∀ a (_ : Var Γ a), HasTests n a) → DefinableAt n Γ τ
  | .base b => ⟨hasTests_base n b, fun _ hΓ => definableAt_base hΓ b⟩
  | .arrow σ τ =>
    have ihσ := hasTests_and_definableAt n σ
    have ihτ := hasTests_and_definableAt n τ
    ⟨hasTests_arrow (fun d hd => by
        obtain ⟨u, hu⟩ := ihσ.2 [] nofun (fun _ => d) (fun _ _ _ => le_rfl) fun _ => hd
        exact ⟨u, hu Tuple.nil⟩) ihτ.1,
      fun Γ hΓ => definableAt_arrow (ihτ.2 (σ :: Γ) fun a x => by
        cases x with
        | zero => exact ihσ.1
        | succ x => exact hΓ a x)⟩

/-- Every element in the image of a finite projection `proj n τ` (equivalently, every
fixed point of some `proj n τ`) is definable. These fixed points play the role of the
finite (compact) elements; we do not need to identify them with the compact elements. -/
theorem exists_denoteClosed_eq_proj (n : ℕ) (d : (model true).ty τ) :
    ∃ u : Closed true τ, denoteClosed u = proj n τ d := by
  obtain ⟨u, hu⟩ := (hasTests_and_definableAt n τ).2 [] nofun (fun _ => proj n τ d)
    (fun _ _ _ => le_rfl) fun _ => proj_proj n τ d
  exact ⟨u, hu Tuple.nil⟩

/-- Density: every element is the supremum of a chain of definable elements. -/
theorem exists_chain_definable (d : (model true).ty τ) : ∃ c : Chain ((model true).ty τ),
    ωSup c = d ∧ ∀ n, ∃ u : Closed true τ, denoteClosed u = c n :=
  ⟨(finProj τ).chainAt d, ωSup_chain_proj d, fun n => exists_denoteClosed_eq_proj n d⟩

end Silmaril.Calculi.PCF
