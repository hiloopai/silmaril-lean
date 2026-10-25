module

public import Cslib.Foundations.Logic.InferenceSystem

@[expose] public section

/-!
# Morphisms of inference systems

A translation of conclusions together with a map of derivations. This interface
works with CSLib's `InferenceSystem`, including both proof-relevant derivations
and judgments in `Prop`.
-/

namespace Silmaril.Logic.Metatheory

open Cslib.Logic Cslib.Logic.InferenceSystem

/-- A translation that carries each source derivation to a target derivation. -/
structure InferenceMorphism (S T α β : Type*)
    [InferenceSystem S α] [InferenceSystem T β] where
  map : α → β
  mapDerivation : {a : α} → (S⇓a) → (T⇓(map a))

namespace InferenceMorphism

variable {S T U α β γ : Type*}
  [InferenceSystem S α] [InferenceSystem T β] [InferenceSystem U γ]

instance : CoeFun (InferenceMorphism S T α β) (fun _ => α → β) := ⟨map⟩

/-- Derivation maps also preserve CSLib's proposition-valued derivability. -/
theorem preserves (f : InferenceMorphism S T α β) {a : α}
    (h : DerivableIn S a) : DerivableIn T (f a) := by
  obtain ⟨d⟩ := h
  exact ⟨f.mapDerivation d⟩

/-- The identity translation. -/
def id : InferenceMorphism S S α α where
  map := fun a => a
  mapDerivation := fun d => d

/-- Composition translates both conclusions and their derivations. -/
def comp (g : InferenceMorphism T U β γ) (f : InferenceMorphism S T α β) :
    InferenceMorphism S U α γ where
  map := fun a => g (f a)
  mapDerivation := fun d => g.mapDerivation (f.mapDerivation d)

@[simp] theorem id_apply (a : α) : (id (S := S) : InferenceMorphism S S α α) a = a := rfl

@[simp] theorem comp_apply (g : InferenceMorphism T U β γ)
    (f : InferenceMorphism S T α β) (a : α) : g.comp f a = g (f a) := rfl

end InferenceMorphism

end Silmaril.Logic.Metatheory
