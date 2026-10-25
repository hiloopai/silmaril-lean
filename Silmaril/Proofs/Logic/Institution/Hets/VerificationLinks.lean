module

public import Silmaril.Logic.Institution.Hets.Verification.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.Institution.Hets

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.StrSpec

universe u v w m₁ m₂

variable {Sign : Type u} [Category.{v} Sign] {I : Sign ⥤ Room.{w, m₁, m₂}}

/-- Links of the verification graph only come from immediate subterms, so the link relation is
well-founded. -/
theorem nodeLink_wf : WellFounded fun M N : Node I =>
    (nodeGlobalDef M N).Nonempty ∨ (∅ : Set (M.1 ⟶ N.1)).Nonempty ∨
      (nodeHidingDef M N).Nonempty := by
  refine Subrelation.wf (r := InvImage (· < ·) fun N : Node I => N.2.size) ?_
    (InvImage.wf _ wellFounded_lt)
  intro M N h
  obtain ⟨S, SP⟩ := N
  show M.2.size < SP.size
  rcases h with ⟨σ, hσ⟩ | ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · cases SP with
    | basic => exact absurd hσ (Set.notMem_empty σ)
    | union SP₁ SP₂ =>
      rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp only [size] <;> omega
    | translate τ SP =>
      obtain ⟨rfl, -⟩ := hσ
      simp only [size]; omega
    | hide => exact absurd hσ (Set.notMem_empty σ)
  · exact absurd hσ (Set.notMem_empty σ)
  · cases SP with
    | basic => exact absurd hσ (Set.notMem_empty σ)
    | union => exact absurd hσ (Set.notMem_empty σ)
    | translate => exact absurd hσ (Set.notMem_empty σ)
    | hide τ SP' =>
      obtain ⟨rfl, -⟩ := hσ
      simp only [size]; omega


end Silmaril.Proofs.Logic.Institution.Hets
