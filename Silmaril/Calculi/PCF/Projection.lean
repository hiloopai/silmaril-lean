module

public import Silmaril.Calculi.PCF.Denotation
public import Silmaril.Semantics.Domain.FiniteProjection
public import Silmaril.Semantics.Domain.BoundedComplete

/-! # Finite projections on the PCF+`por` model

Every domain `⟦τ⟧` of the model of PCF+`por` carries an ω-chain of idempotent
deflations `proj n τ` with finitely many fixed points each, whose supremum is the
identity (`ωSup_chain_proj`). At `nat` the `n`-th projection truncates the
numerals `≥ n` to `⊥`; at `bool` it is the identity; at an arrow type it is
conjugation, `proj n (σ ⤳ τ) f = proj n τ ∘ f ∘ proj n σ` (`app_proj`, by `rfl`).

These projections are extended componentwise to environments (`projEnv`). We also
record that every `⟦τ⟧` is bounded complete (`boundedComplete_ty`), that the ground
domains are flat (`base_le_iff`), and that the non-`⊥` fixed points of a ground
projection are denoted by finitely many closed literals (`exists_values`).

These are the finite elements used in the proof that PCF+`por` is fully abstract.
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open OmegaCompletePartialOrder Silmaril.Semantics.Domain TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

/-- The finite projections on each domain `⟦τ⟧` of the PCF+`por` model. -/
noncomputable def finProj : (τ : Ty) → FiniteProjections ((model true).ty τ)
  | .base .nat => FiniteProjections.nat
  | .base .bool => FiniteProjections.ofFinite
  | .arrow σ τ => (finProj σ).arrow (finProj τ)

/-- The `n`-th projection on `⟦τ⟧`. -/
noncomputable abbrev proj (n : ℕ) (τ : Ty) : (model true).ty τ →𝒄 (model true).ty τ :=
  (finProj τ).proj n

variable {Γ : Ctx Base} {σ τ : Ty} {n : ℕ}

/-- At `nat`, the `n`-th projection keeps exactly the numerals below `n`. -/
theorem proj_nat_some (n k : ℕ) : proj n .nat (Part.some k : Part ℕ) =
    if k < n then Part.some k else Part.none :=
  FiniteProjections.natTrunc_some n k

/-- At `nat`, `⊥` is fixed by every projection. -/
theorem proj_nat_none (n : ℕ) : proj n .nat (Part.none : Part ℕ) = Part.none :=
  FiniteProjections.natTrunc_none n

/-- At `bool`, every projection is the identity. -/
theorem proj_bool (n : ℕ) (x : (model true).ty (.base .bool)) : proj n (.base .bool) x = x := rfl

/-- At an arrow type, the projection is conjugation by the projections. -/
theorem app_proj (f : (model true).ty (σ ⤳ τ)) (d : (model true).ty σ) :
    Model.app (proj n (σ ⤳ τ) f) d = proj n τ (Model.app f (proj n σ d)) := rfl

/-- Projections are deflations. -/
theorem proj_le (n : ℕ) (τ : Ty) (d : (model true).ty τ) : proj n τ d ≤ d :=
  (finProj τ).proj_le n d

/-- Projections are idempotent. -/
theorem proj_proj (n : ℕ) (τ : Ty) (d : (model true).ty τ) :
    proj n τ (proj n τ d) = proj n τ d :=
  (finProj τ).proj_proj n d

/-- The projections increase with `n`. -/
theorem monotone_proj (τ : Ty) : Monotone fun n => proj n τ :=
  (finProj τ).monotone_proj

/-- Every element is the supremum of its projections. -/
theorem ωSup_chain_proj (d : (model true).ty τ) : ωSup ((finProj τ).chainAt d) = d :=
  (finProj τ).ωSup_chainAt d

/-- Each projection has finitely many fixed points. -/
theorem finite_fixed_proj (n : ℕ) (τ : Ty) : {d : (model true).ty τ | proj n τ d = d}.Finite :=
  (finProj τ).finite_fixed n

/-- Projection of environments, componentwise. -/
noncomputable def projEnv (n : ℕ) {Γ : Ctx Base} (ρ : (model true).Env Γ) :
    (model true).Env Γ :=
  fun a x => proj n a (ρ a x)

/-- `projEnv` acts componentwise. -/
@[simp] theorem projEnv_apply (ρ : (model true).Env Γ) (a : Ty) (x : Var Γ a) :
    projEnv n ρ a x = proj n a (ρ a x) := rfl

/-- The projection of environments is idempotent. -/
theorem projEnv_projEnv (n : ℕ) (ρ : (model true).Env Γ) :
    projEnv n (projEnv n ρ) = projEnv n ρ :=
  Tuple.ext fun a x => proj_proj n a (ρ a x)

/-- The projection of environments is a deflation. -/
theorem projEnv_le (n : ℕ) (ρ : (model true).Env Γ) : projEnv n ρ ≤ ρ :=
  fun a x => proj_le n a (ρ a x)

/-- The projection of environments is monotone. -/
theorem projEnv_mono (n : ℕ) : Monotone (projEnv n (Γ := Γ)) :=
  fun _ _ h a x => (proj n a).monotone (h a x)

/-- The projection of environments increases with `n`. -/
theorem projEnv_le_projEnv {m : ℕ} (h : n ≤ m) (ρ : (model true).Env Γ) :
    projEnv n ρ ≤ projEnv m ρ :=
  fun a x => monotone_proj a h (ρ a x)

/-- Projecting an extended environment projects the new value and the rest. -/
theorem projEnv_cons (d : (model true).ty σ) (ρ : (model true).Env Γ) :
    projEnv n (d ::ₜ ρ) = proj n σ d ::ₜ projEnv n ρ :=
  Tuple.ext fun _ x => by cases x <;> rfl

/-- The head of a projected environment. -/
@[simp] theorem head_projEnv (ρ : (model true).Env (σ :: Γ)) :
    Tuple.head (projEnv n ρ) = proj n σ (Tuple.head ρ) := rfl

/-- The tail of a projected environment. -/
@[simp] theorem tail_projEnv (ρ : (model true).Env (σ :: Γ)) :
    Tuple.tail (projEnv n ρ) = projEnv n (Tuple.tail ρ) := rfl

/-- The projection of environments has finitely many fixed points. -/
theorem finite_fixed_projEnv (n : ℕ) :
    (Γ : Ctx Base) → {ρ : (model true).Env Γ | projEnv n ρ = ρ}.Finite
  | [] => Set.Subsingleton.finite fun ρ _ ρ' _ => by
      rw [Model.env_nil_eq ρ, Model.env_nil_eq ρ']
  | σ :: Γ => by
      refine (((finite_fixed_proj n σ).prod (finite_fixed_projEnv n Γ)).image
        fun p => (p.1 ::ₜ p.2 : (model true).Env (σ :: Γ))).subset ?_
      intro ρ hρ
      have hρ : projEnv n ρ = ρ := hρ
      refine ⟨(Tuple.head ρ, Tuple.tail ρ), ⟨?_, ?_⟩, (Tuple.eq_cons ρ).symm⟩
      · change proj n σ (Tuple.head ρ) = Tuple.head ρ
        rw [← head_projEnv, hρ]
      · change projEnv n (Tuple.tail ρ) = Tuple.tail ρ
        rw [← tail_projEnv, hρ]

/-- Every domain of the model is bounded complete. -/
theorem boundedComplete_ty : (τ : Ty) → BoundedComplete ((model true).ty τ)
  | .base .nat => Flat.boundedComplete ℕ
  | .base .bool => Flat.boundedComplete Bool
  | .arrow _ τ => ContinuousHom.boundedComplete (boundedComplete_ty τ)

/-- The ground domains are flat. -/
theorem base_le_iff {b : Base} {x y : (model true).ty (.base b)} :
    x ≤ y ↔ x = ⊥ ∨ x = y := by
  cases b
  · exact Flat.le_iff_eq_none_or_eq (X := ℕ)
  · exact Flat.le_iff_eq_none_or_eq (X := Bool)

/-- The non-⊥ fixed points at a base type, each a closed literal. -/
theorem exists_values (n : ℕ) (b : Base) : ∃ V : List ((model true).ty (.base b)),
    (∀ v ∈ V, v ≠ ⊥ ∧ ∃ w : Closed true (.base b), denoteClosed w = v) ∧
    ∀ v, proj n (.base b) v = v → v ≠ ⊥ → v ∈ V := by
  cases b
  · refine ⟨(List.range n).map fun k => (Part.some k : Part ℕ), ?_, ?_⟩
    · intro v hv
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hv
      exact ⟨Part.some_ne_none k, Term.num k, denote_num _ k⟩
    · intro v hfix hne
      obtain ⟨k, rfl⟩ := Part.ne_none_iff.1 hne
      have hfix : proj n .nat (Part.some k : Part ℕ) = Part.some k := hfix
      rw [proj_nat_some] at hfix
      split_ifs at hfix with hk
      · exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩
      · exact absurd hfix.symm (Part.some_ne_none k)
  · refine ⟨[(Part.some true : Part Bool), (Part.some false : Part Bool)], ?_, ?_⟩
    · intro v hv
      rcases List.mem_pair.1 hv with rfl | rfl
      · exact ⟨Part.some_ne_none _, Term.bool true, denote_bool _ true⟩
      · exact ⟨Part.some_ne_none _, Term.bool false, denote_bool _ false⟩
    · intro v _ hne
      rcases Flat.bool_cases (v : Part Bool) with h | h | h
      · exact absurd h hne
      · rw [h]; exact List.mem_pair.2 (Or.inl rfl)
      · rw [h]; exact List.mem_pair.2 (Or.inr rfl)

end Silmaril.Calculi.PCF
