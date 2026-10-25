module

public import Silmaril.Logic.Institution.Hets.Verification.Graph

@[expose] public section

namespace Silmaril.Proofs.Logic.Institution.Hets

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.StrSpec

universe u v w m₁ m₂

variable {Sign : Type u} [Category.{v} Sign] {I : Sign ⥤ Room.{w, m₁, m₂}}

/-- **The verification semantics preserves model classes**: the models of a structured
specification are the models of its node in the development graph.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §8.1
(PDF pages 19–21: "`Mod(SP) = Mod_S(O)`");
`mossakowski-2005-habilitation-hets` in `references.bib`, §5.5, Theorem 5.19 (printed page 137, PDF page 139). -/
theorem models_devGraph {S : Sign} (SP : StrSpec I S) :
    (devGraph I).models ⟨S, SP⟩ = SP.models := by
  induction SP with
  | basic S E =>
    ext n
    refine ((devGraph I).mem_models_iff _ n).trans ⟨fun h => h.1, fun h => ⟨h, ?_, ?_, ?_⟩⟩
    · exact fun K σ hσ => absurd hσ (Set.notMem_empty σ)
    · exact fun K σ hσ => absurd hσ (Set.notMem_empty σ)
    · exact fun K σ hσ => absurd hσ (Set.notMem_empty σ)
  | @union S SP₁ SP₂ ih₁ ih₂ =>
    ext n
    refine ((devGraph I).mem_models_iff _ n).trans ⟨?_, ?_⟩
    · rintro ⟨-, hg, -, -⟩
      have h₁ := (Set.ext_iff.1 ih₁ _).1
        (hg (⟨S, SP₁⟩ : Node I) (𝟙 S) (Or.inl ⟨rfl, (eqToHom_refl _ _).symm⟩))
      have h₂ := (Set.ext_iff.1 ih₂ _).1
        (hg (⟨S, SP₂⟩ : Node I) (𝟙 S) (Or.inr ⟨rfl, (eqToHom_refl _ _).symm⟩))
      exact ⟨(congrArg (· ∈ SP₁.models) (mod_obj_id n)).mp h₁,
        (congrArg (· ∈ SP₂.models) (mod_obj_id n)).mp h₂⟩
    · rintro ⟨h₁, h₂⟩
      refine ⟨fun φ hφ => absurd hφ (Set.notMem_empty φ), ?_,
        fun K σ hσ => absurd hσ (Set.notMem_empty σ),
        fun K σ hσ => absurd hσ (Set.notMem_empty σ)⟩
      rintro K σ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact (Set.ext_iff.1 ih₁ _).2
          ((congrArg (· ∈ SP₁.models) (mod_obj_eqToHom _ n)).mpr h₁)
      · exact (Set.ext_iff.1 ih₂ _).2
          ((congrArg (· ∈ SP₂.models) (mod_obj_eqToHom _ n)).mpr h₂)
  | @translate S S' τ SP ih =>
    ext n
    refine ((devGraph I).mem_models_iff _ n).trans ⟨?_, ?_⟩
    · rintro ⟨-, hg, -, -⟩
      exact (Set.ext_iff.1 ih _).1
        (hg (⟨S, SP⟩ : Node I) τ ⟨rfl, by simp⟩)
    · intro h
      refine ⟨fun φ hφ => absurd hφ (Set.notMem_empty φ), ?_,
        fun K σ hσ => absurd hσ (Set.notMem_empty σ),
        fun K σ hσ => absurd hσ (Set.notMem_empty σ)⟩
      rintro K σ ⟨rfl, rfl⟩
      exact (Set.ext_iff.1 ih _).2
        ((congrArg (· ∈ SP.models) (mod_obj_eqToHom_comp _ τ n)).mpr h)
  | @hide S S' τ SP' ih =>
    ext n
    refine ((devGraph I).mem_models_iff _ n).trans ⟨?_, ?_⟩
    · rintro ⟨-, -, -, hh⟩
      obtain ⟨k, hk, hkn⟩ := hh (⟨S', SP'⟩ : Node I) τ ⟨rfl, by simp⟩
      exact ⟨k, (Set.ext_iff.1 ih _).1 hk, hkn⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨fun φ hφ => absurd hφ (Set.notMem_empty φ),
        fun K σ hσ => absurd hσ (Set.notMem_empty σ),
        fun K σ hσ => absurd hσ (Set.notMem_empty σ), ?_⟩
      rintro K σ ⟨rfl, rfl⟩
      exact ⟨k, (Set.ext_iff.1 ih _).2 hk, mod_obj_comp_eqToHom τ _ k⟩

/-- Entailment of a structured specification is the local implication at its node.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 11 (PDF page 9) and §8.1 (PDF page 19). -/
theorem entails_iff_localImpl {S : Sign} (SP : StrSpec I S) (Γ : Set (I.obj S).Sen) :
    (∀ φ ∈ Γ, SP.Entails φ) ↔ (devGraph I).LocalImpl ⟨S, SP⟩ Γ := by
  unfold DevGraph.LocalImpl Entails
  rw [models_devGraph]
  exact ⟨fun h n hn φ hφ => h φ hφ n hn, fun h φ hφ n hn => h n hn φ hφ⟩

/-- Refinement of structured specifications is a global theorem link along the identity
between their nodes.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.5 (printed page 137,
PDF page 139: the verification semantics of views, `N₁ ⇢σ N₂`). -/
theorem refines_iff_globalThm {S : Sign} (SP₁ SP₂ : StrSpec I S) :
    SP₁.Refines SP₂ ↔ (devGraph I).GlobalThm ⟨S, SP₁⟩ ⟨S, SP₂⟩ (𝟙 S) := by
  unfold DevGraph.GlobalThm Refines
  rw [models_devGraph, models_devGraph]
  exact ⟨fun h m hm => (congrArg (· ∈ SP₁.models) (mod_obj_id m)).mpr (h hm),
    fun h m hm => (congrArg (· ∈ SP₁.models) (mod_obj_id m)).mp (h m hm)⟩

end Silmaril.Proofs.Logic.Institution.Hets
