module

public import Silmaril.Calculi.PCF.Projection
public import Silmaril.Calculi.PCF.Parallel

/-! # Definability of finite elements in PCF+`por`

Towards full abstraction of the PCF+`por` model, we show that the fixed points of the
finite projections `proj n τ` are definable. This file first builds *three-valued
tests*: for a fixed element `e = proj n τ e`, a closed term `T : τ → bool` with

* `⟦T⟧ x = true` exactly when `e ⊑ proj n τ x`, and
* `⟦T⟧ x = false` whenever `e` and `proj n τ x` have no common upper bound.

The `false` clause is essential: tests which only answer `true` or `⊥` do not
compose at arrow types. Tests exist at the base types (`hasTests_base`), and at an
arrow type `σ → τ` as soon as the fixed points of `proj n σ` are definable and tests
exist at `τ` (`hasTests_arrow`); the arrow test is the parallel conjunction over the
finitely many fixed points `d` of `proj n σ` of the test for `e d` applied to `x d`.
Bounded completeness of `⟦τ⟧` is what makes a failure of compatibility visible at a
single such `d`.

Tests at the types of a context combine into *environment tests* (`exists_envTest`).
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open OmegaCompletePartialOrder Silmaril.Semantics.Domain TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

variable {Γ : Ctx Base} {σ τ : Ty} {n : ℕ}

/-- A three-valued test for `e` relative to the `n`-th projection: `⟦T⟧ x` is `true`
exactly when `e ⊑ proj n τ x`, and `false` when `e` and `proj n τ x` are
incompatible. -/
def IsTest (n : ℕ) {τ : Ty} (e : (model true).ty τ) (T : Closed true (τ ⤳ Ty.bool)) : Prop :=
  ∀ x, ((Model.app (denoteClosed T) x : Part Bool) = .some true ↔ e ≤ proj n τ x) ∧
    (¬ BddAbove ({e, proj n τ x} : Set _) →
      (Model.app (denoteClosed T) x : Part Bool) = .some false)

/-- Every fixed point of the `n`-th projection at `τ` has a test. -/
def HasTests (n : ℕ) (τ : Ty) : Prop := ∀ e, proj n τ e = e → ∃ T, IsTest n e T

/-- `⊥` is tested by the constant `true`. -/
theorem isTest_bot (n : ℕ) (τ : Ty) :
    IsTest n (⊥ : (model true).ty τ) (.lam Term.tt) := fun _ =>
  ⟨iff_of_true rfl bot_le, fun h => absurd (bddAbove_pair_bot_left _) h⟩

/-- A numeral `k < n` is tested by `eqNum k`. -/
theorem isTest_nat_some {k : ℕ} (hk : k < n) :
    IsTest (τ := Ty.nat) n (Part.some k : Part ℕ) (.lam (Term.eqNum k Term.v0)) := by
  intro x
  have hT : (Model.app (denoteClosed (.lam (Term.eqNum k Term.v0) :
      Closed true (Ty.nat ⤳ Ty.bool))) x : Part Bool) = Flat.map (· == k) (x : Part ℕ) :=
    denote_eqNum k Term.v0 (x ::ₜ Tuple.nil)
  rw [hT]
  rcases Part.eq_none_or_eq_some (x : Part ℕ) with h | ⟨m, h⟩
  · have hp : proj n .nat x = Part.none := by rw [h]; exact proj_nat_none n
    rw [hp, h, Flat.map_none]
    refine ⟨iff_of_false (fun h => Part.some_ne_none true h.symm) fun h' => ?_, fun h' => ?_⟩
    · exact Part.some_ne_none k (Flat.some_le_iff.1 h').symm
    · exact absurd (bddAbove_pair_bot_right (D := Part ℕ) _) h'
  · have hp : proj n .nat x = if m < n then Part.some m else Part.none := by
      rw [h]; exact proj_nat_some n m
    rw [hp, h, Flat.map_some]
    split_ifs with hm
    · refine ⟨?_, fun h' => ?_⟩
      · rw [Flat.some_le_iff]
        constructor
        · intro h'
          rw [beq_iff_eq.1 (Part.some_injective h')]
        · intro h'
          rw [Part.some_injective h', beq_self_eq_true]
      · have hmk : m ≠ k := fun hmk => h' (Flat.bddAbove_some_some_iff.2 hmk.symm)
        exact congrArg Part.some (beq_false_of_ne hmk)
    · have hmk : m ≠ k := by omega
      refine ⟨iff_of_false (fun h' => hmk (beq_iff_eq.1 (Part.some_injective h'))) fun h' => ?_,
        fun _ => congrArg Part.some (beq_false_of_ne hmk)⟩
      exact Part.some_ne_none k (Flat.some_le_iff.1 h').symm

/-- `true` is tested by the identity. -/
theorem isTest_true (n : ℕ) :
    IsTest (τ := Ty.bool) n (Part.some true : Part Bool) (.lam Term.v0) := by
  intro x
  change ((x : Part Bool) = _ ↔ Part.some true ≤ (x : Part Bool)) ∧
    (¬ BddAbove ({Part.some true, (x : Part Bool)} : Set (Part Bool)) → (x : Part Bool) = _)
  rcases part_bool_cases (x : Part Bool) with h | h | h <;> rw [h]
  · exact ⟨iff_of_false (fun h => Part.some_ne_none true h.symm)
      fun h' => Part.some_ne_none true (Flat.some_le_iff.1 h').symm,
      fun h' => absurd (bddAbove_pair_bot_right _) h'⟩
  · exact ⟨iff_of_true rfl le_rfl, fun h' => absurd (Flat.bddAbove_some_some_iff.2 rfl) h'⟩
  · exact ⟨iff_of_false (fun h => Flat.some_true_ne_some_false h.symm)
      fun h' => Flat.some_true_ne_some_false (Flat.some_le_iff.1 h').symm, fun _ => rfl⟩

/-- `false` is tested by negation. -/
theorem isTest_false (n : ℕ) :
    IsTest (τ := Ty.bool) n (Part.some false : Part Bool) (.lam (Term.not Term.v0)) := by
  intro x
  have hT : (Model.app (denoteClosed (.lam (Term.not Term.v0) :
      Closed true (Ty.bool ⤳ Ty.bool))) x : Part Bool) = Flat.map (!·) (x : Part Bool) :=
    denote_not Term.v0 (x ::ₜ Tuple.nil)
  rw [hT]
  change (_ ↔ Part.some false ≤ (x : Part Bool)) ∧
    (¬ BddAbove ({Part.some false, (x : Part Bool)} : Set (Part Bool)) → _)
  rcases part_bool_cases (x : Part Bool) with h | h | h <;> rw [h]
  · rw [Flat.map_none]
    exact ⟨iff_of_false (fun h => Part.some_ne_none true h.symm)
      fun h' => Part.some_ne_none false (Flat.some_le_iff.1 h').symm,
      fun h' => absurd (bddAbove_pair_bot_right _) h'⟩
  · rw [Flat.map_some]
    exact ⟨iff_of_false (fun h => Flat.some_true_ne_some_false h.symm)
      fun h' => Flat.some_true_ne_some_false (Flat.some_le_iff.1 h'), fun _ => rfl⟩
  · rw [Flat.map_some]
    exact ⟨iff_of_true rfl le_rfl, fun h' => absurd (Flat.bddAbove_some_some_iff.2 rfl) h'⟩

/-- Every fixed point of a projection at a base type has a test. -/
theorem hasTests_base (n : ℕ) (b : Base) : HasTests n (.base b) := by
  intro e he
  cases b with
  | nat =>
    rcases Part.eq_none_or_eq_some (e : Part ℕ) with h | ⟨k, h⟩
    · rw [h]; exact ⟨_, isTest_bot n _⟩
    · have he' : proj n .nat e = e := he
      rw [h, proj_nat_some] at he'
      split_ifs at he' with hk
      · rw [h]; exact ⟨_, isTest_nat_some hk⟩
      · exact absurd he' (Part.none_ne_some k)
  | bool =>
    rcases part_bool_cases (e : Part Bool) with h | h | h <;> rw [h]
    · exact ⟨_, isTest_bot n _⟩
    · exact ⟨_, isTest_true n⟩
    · exact ⟨_, isTest_false n⟩

/-- Tests at an arrow type `σ → τ`, from definability of the fixed points at `σ` and
tests at `τ`: the parallel conjunction, over the fixed points `d` of `proj n σ`, of the
test for `e d` applied to `x d`. -/
theorem hasTests_arrow (hσ : ∀ d, proj n σ d = d → ∃ u : Closed true σ, denoteClosed u = d)
    (hτ : HasTests n τ) : HasTests n (σ ⤳ τ) := by
  classical
  have hσ' : ∀ d, ∃ u : Closed true σ, proj n σ d = d → denoteClosed u = d := fun d => by
    by_cases hd : proj n σ d = d
    · obtain ⟨u, hu⟩ := hσ d hd
      exact ⟨u, fun _ => hu⟩
    · exact ⟨Term.omega σ, fun h => absurd h hd⟩
  have hτ' : ∀ e', ∃ T, proj n τ e' = e' → IsTest n e' T := fun e' => by
    by_cases he' : proj n τ e' = e'
    · obtain ⟨T, hT⟩ := hτ e' he'
      exact ⟨T, fun _ => hT⟩
    · exact ⟨Term.omega _, fun h => absurd h he'⟩
  choose u hu using hσ'
  choose T hT using hτ'
  intro e he
  have he' : ((finProj σ).arrow (finProj τ)).proj n e = e := he
  have hfe : ∀ d, proj n τ (Model.app e d) = Model.app e d :=
    FiniteProjections.proj_apply_of_fixed he'
  let L := (finite_fixed_proj n σ).toFinset.toList
  have hmem : ∀ d, d ∈ L ↔ proj n σ d = d := by simp [L]
  let conj : (model true).ty σ → Term true [σ ⤳ τ] Ty.bool := fun d =>
    .app (Term.ofClosed (T (Model.app e d))) (.app Term.v0 (Term.ofClosed (u d)))
  refine ⟨.lam (Term.pandList (L.map conj)), fun x => ?_⟩
  have happ : Model.app (denoteClosed (.lam (Term.pandList (L.map conj)) :
      Closed true ((σ ⤳ τ) ⤳ Ty.bool))) x =
      denote (Term.pandList (L.map conj)) (x ::ₜ Tuple.nil) := rfl
  have hconj : ∀ d ∈ L, denote (conj d) (x ::ₜ Tuple.nil) =
      Model.app (denoteClosed (T (Model.app e d))) (Model.app x d) := by
    intro d hd
    change Model.app ((model true).denote (Term.ofClosed (T (Model.app e d)))
        (x ::ₜ Tuple.nil)) (Model.app x ((model true).denote (Term.ofClosed (u d))
        (x ::ₜ Tuple.nil))) = _
    rw [Model.denote_ofClosed, Model.denote_ofClosed]
    exact congrArg (fun y => Model.app _ (Model.app x y)) (hu d ((hmem d).1 hd))
  rw [happ]
  refine ⟨?_, fun hb => ?_⟩
  · rw [denote_pandList_eq_true_iff, List.forall_mem_map]
    refine Iff.trans ?_ (FiniteProjections.le_proj_iff_of_fixed he' (x := x)).symm
    refine forall_congr' fun d => ?_
    rw [hmem]
    refine imp_congr_right fun hd => ?_
    rw [hconj d ((hmem d).2 hd)]
    exact (hT _ (hfe d) (Model.app x d)).1
  · have hb' : ¬ ∀ d, proj n σ d = d →
        BddAbove ({Model.app e d, proj n τ (Model.app x d)} : Set ((model true).ty τ)) :=
      fun h => hb ((FiniteProjections.bddAbove_proj_iff_of_fixed (boundedComplete_ty τ) he'
        (x := x)).2 h)
    simp only [not_forall] at hb'
    obtain ⟨d, hd, hnb⟩ := hb'
    refine denote_pandList_of_exists_false ⟨conj d, List.mem_map_of_mem ((hmem d).2 hd), ?_⟩
    rw [hconj d ((hmem d).2 hd)]
    exact (hT _ (hfe d) (Model.app x d)).2 hnb

/-- Environment tests: given tests at the types of `Γ`, every fixed environment `ē`
has a test `Γ ⊢ t : bool`, which is `true` at `ρ` exactly when `ē ⊑ projEnv n ρ`, and
`false` when some coordinate of `ē` is incompatible with that of `projEnv n ρ`. -/
theorem exists_envTest (hΓ : ∀ a (_ : Var Γ a), HasTests n a) (ē : (model true).Env Γ) :
    ∃ t : Term true Γ .bool, projEnv n ē = ē → ∀ ρ,
      ((denote t ρ : Part Bool) = .some true ↔ ē ≤ projEnv n ρ) ∧
      ((∃ a x, ¬ BddAbove ({ē a x, proj n a (ρ a x)} : Set _)) →
        (denote t ρ : Part Bool) = .some false) := by
  induction Γ with
  | nil =>
    refine ⟨Term.tt, fun _ ρ => ⟨iff_of_true rfl nofun, ?_⟩⟩
    rintro ⟨_, x, _⟩
    exact nomatch x
  | cons σ Γ ih =>
    obtain ⟨t, ht⟩ := ih (fun a x => hΓ a x.succ) (Tuple.tail ē)
    by_cases hfix : projEnv n ē = ē
    · have hhead : proj n σ (Tuple.head ē) = Tuple.head ē := by rw [← head_projEnv, hfix]
      have htail : projEnv n (Tuple.tail ē) = Tuple.tail ē := by rw [← tail_projEnv, hfix]
      obtain ⟨T, hT⟩ := hΓ σ .zero (Tuple.head ē) hhead
      refine ⟨Term.pand (.app (Term.ofClosed T) Term.v0) t.weaken, fun _ ρ => ?_⟩
      have h₁ : denote (.app (Term.ofClosed T) Term.v0 : Term true (σ :: Γ) _) ρ =
          Model.app (denoteClosed T) (Tuple.head ρ) := by
        change Model.app ((model true).denote (Term.ofClosed T) ρ) (ρ σ .zero) = _
        rw [Model.denote_ofClosed]
        rfl
      have h₂ : denote t.weaken ρ = denote t (Tuple.tail ρ) := Model.denote_rename _ t ρ
      obtain ⟨htt, hff⟩ := ht htail (Tuple.tail ρ)
      refine ⟨?_, ?_⟩
      · rw [denote_pand_eq_true_iff, h₁, h₂, htt, Model.env_cons_le_iff, (hT (Tuple.head ρ)).1]
        rfl
      · rintro ⟨a, x, hx⟩
        cases x with
        | zero =>
          refine denote_pand_of_left_false ?_
          rw [h₁]
          exact (hT (Tuple.head ρ)).2 hx
        | succ x =>
          refine denote_pand_of_right_false ?_
          rw [h₂]
          exact hff ⟨a, x, hx⟩
    · exact ⟨Term.tt, fun h => absurd h hfix⟩

end Silmaril.Calculi.PCF
