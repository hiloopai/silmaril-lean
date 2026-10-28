module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Data.Set.Lattice.Order

/-! # §13 Constraint-based analysis (notes pp. 25–26; slides pp. 99–104)

"In constraint-based analysis, the approach taken is that of walking the
program emitting constraints […] on the sets of values which variables or
expressions may take" (notes p. 25). The constraint systems of the course
(LVA, 0CFA, Andersen) are sets of inclusions whose solutions are closed under
arbitrary intersections (a *Moore family*), so the intersection of all
solutions is the least solution (`IsMoore.isLeast_sInf`, notes §13.1: "such sets
of such constraints have a minimal solution").

The notes' exercise (p. 26): the transitive closure `T` of a relation `R` is the
least solution of `R ⊆ T` and `{(x, y)} ⊆ T ∧ {(y, z)} ⊆ R ⇒ {(x, z)} ⊆ T`
(`transClosure_isLeast`).
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.ConstraintBased

variable {α : Type*} [CompleteLattice α]

/-- A constraint system, given by its set of solutions, is closed under
arbitrary meets. -/
def IsMoore (C : Set α) : Prop := ∀ S ⊆ C, sInf S ∈ C

/-- The least solution of a Moore family. -/
theorem IsMoore.isLeast_sInf {C : Set α} (h : IsMoore C) : IsLeast C (sInf C) :=
  ⟨h C le_rfl, fun _ hx => sInf_le hx⟩

/-- Membership in a pointwise meet of set-valued functions. -/
theorem mem_sInf_apply {ι γ : Type*} {S : Set (ι → Set γ)} {i : ι} {x : γ} :
    x ∈ sInf S i ↔ ∀ f ∈ S, x ∈ f i := by
  constructor
  · intro h f hf
    exact (sInf_le hf : sInf S ≤ f) i h
  · intro h
    rw [sInf_apply]
    exact Set.mem_iInter.2 fun f => h f.1 f.2

/-- Inclusions valid in every member of `S` are valid in its meet. -/
theorem sInf_apply_subset {ι γ : Type*} {S : Set (ι → Set γ)} {i j : ι}
    (h : ∀ f ∈ S, f i ⊆ f j) : sInf S i ⊆ sInf S j := fun _ hx =>
  mem_sInf_apply.2 fun f hf => h f hf (mem_sInf_apply.1 hx f hf)

/-- Pointwise meet of relations. -/
theorem sInf_rel_iff {β : Type*} {S : Set (β → β → Prop)} {x y : β} :
    sInf S x y ↔ ∀ T ∈ S, T x y := by
  constructor
  · intro h T hT
    exact (sInf_le hT : sInf S ≤ T) x y h
  · intro h
    have : (fun a b => a = x ∧ b = y) ≤ sInf S :=
      le_sInf fun T hT a b hab => by
        obtain ⟨rfl, rfl⟩ := hab
        exact h T hT
    exact this x y ⟨rfl, rfl⟩

/-- The transitive-closure constraints of notes p. 26. -/
def TransClosureConstraints {β : Type*} (R : β → β → Prop) : Set (β → β → Prop) :=
  {T | (∀ x y, R x y → T x y) ∧ ∀ x y z, T x y → R y z → T x z}

/-- The transitive-closure constraints form a Moore family. -/
theorem transClosureConstraints_isMoore {β : Type*} (R : β → β → Prop) :
    IsMoore (TransClosureConstraints R) := fun _ hS =>
  ⟨fun x y hR => sInf_rel_iff.2 fun _ hT => (hS hT).1 x y hR,
    fun x y z hT hR => sInf_rel_iff.2 fun T' hT' => (hS hT').2 x y z (sInf_rel_iff.1 hT T' hT') hR⟩

/-- Their least solution is the transitive closure. -/
theorem transClosure_isLeast {β : Type*} (R : β → β → Prop) :
    IsLeast (TransClosureConstraints R) (Relation.TransGen R) := by
  refine ⟨⟨fun _ _ h => Relation.TransGen.single h, fun _ _ _ h r => h.tail r⟩, ?_⟩
  intro T hT x y h
  induction h with
  | single hr => exact hT.1 _ _ hr
  | tail _ hr ih => exact hT.2 _ _ _ ih hr

end Silmaril.Courses.Cambridge.OptimisingCompilers.ConstraintBased
