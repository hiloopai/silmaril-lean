module

public import Silmaril.Logic.Inst.Core.Thms
public import Silmaril.Logic.Inst.Defs

/-!
# Borrowing lemmas of the institution facade

Re-exports the core transfer lemmas (`Silmaril.Logic.Inst.Core.Thms`) and adds the lemmas that
need silmaril's borrowing API (`Silmaril.Logic.Institution.Borrowing`): model-expansiveness of
identities and composites, and borrowing of consequence and validity along model-expansive
comorphisms (`Comorphism.entails_iff`, `Comorphism.valid_iff`) and sound morphisms
(`Morphism.entails_iff`).
-/

@[expose] public section

namespace Silmaril.Inst

open CategoryTheory
open Silmaril.Logic.Institution (Inst)

universe u v w m₁ m₂ u₁ v₁ u₂ v₂ u₃ v₃

namespace Comorphism

variable {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}
  {C : Institution.{u₃, v₃, w, m₁, m₂}}

theorem modelExpansive_id (A : Institution.{u₁, v₁, w, m₁, m₂}) : (𝟙ᶜ A).ModelExpansive :=
  Inst.CoHom.modelExpansive_id A

theorem ModelExpansive.comp {f : Comorphism A B} {g : Comorphism B C} (hf : f.ModelExpansive)
    (hg : g.ModelExpansive) : (f ≫ᶜ g).ModelExpansive :=
  Inst.CoHom.ModelExpansive.comp hf hg

/-- A comorphism is model-expansive when every source model is the translation of a target
model. -/
theorem modelExpansive_iff (f : Comorphism A B) :
    f.ModelExpansive ↔ ∀ S (M : A.Mod S), ∃ M' : B.Mod (f.sig S), f.mod S M' = M :=
  Iff.rfl

/-- **Borrowing**: a model-expansive comorphism preserves and reflects consequence. -/
theorem entails_iff (f : Comorphism A B) (hf : f.ModelExpansive) (S : A.Sign)
    (Γ : Set (A.Sen S)) (φ : A.Sen S) :
    A.Entails Γ φ ↔ B.Entails (f.sen S '' Γ) (f.sen S φ) :=
  Inst.CoHom.entails_iff f hf S Γ φ

/-- Comorphisms preserve consequence. -/
theorem entails_map (f : Comorphism A B) {S : A.Sign} {Γ : Set (A.Sen S)} {φ : A.Sen S}
    (h : A.Entails Γ φ) : B.Entails (f.sen S '' Γ) (f.sen S φ) :=
  Inst.CoHom.entails_map f h

/-- **Borrowing validity** along a model-expansive comorphism. -/
theorem valid_iff (f : Comorphism A B) (hf : f.ModelExpansive) {S : A.Sign} (φ : A.Sen S) :
    A.Valid φ ↔ B.Valid (f.sen S φ) := by
  refine ⟨Valid.sen f, fun h M => ?_⟩
  obtain ⟨M', rfl⟩ := hf S M
  exact (sat_sen_iff f S M' φ).1 (h M')

end Comorphism

namespace Morphism

variable {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}

/-- **Borrowing** along a sound morphism. -/
theorem entails_iff (f : Morphism A B) (hf : f.Sound) (S : A.Sign)
    (Γ : Set (B.Sen (f.sig S))) (φ : B.Sen (f.sig S)) :
    B.Entails Γ φ ↔ A.Entails (f.sen S '' Γ) (f.sen S φ) :=
  Inst.Hom.entails_iff f hf S Γ φ

end Morphism

end Silmaril.Inst

/-! ## Dot notation on silmaril-typed values

The borrowing lemmas, exported as aliases into silmaril's namespace (see the end of
`Silmaril.Logic.Inst.Core.Thms`). -/

namespace Silmaril.Logic.Institution.Inst.CoHom

export Silmaril.Inst.Comorphism (modelExpansive_iff valid_iff)

end Silmaril.Logic.Institution.Inst.CoHom
