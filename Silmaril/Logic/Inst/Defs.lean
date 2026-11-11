module

public import Silmaril.Logic.Inst.Core.Defs
public import Silmaril.Logic.Institution.Hets.LogicGraph
public import Silmaril.Logic.Institution.Borrowing

/-! # Broad institution facade

Compatibility entry point including Hets and borrowing. Generic constructions can import
`Silmaril.Logic.Inst.Core.Defs` to depend only on the public institution core.
-/

@[expose] public section

namespace Silmaril.Inst

open Silmaril.Logic.Institution (Inst)
universe u₁ v₁ u₂ v₂ w m₁ m₂

namespace Comorphism
variable {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}
  (f : Comorphism A B)

/-- Every model of the source is a reduct (borrowing holds). -/
abbrev ModelExpansive : Prop := Inst.CoHom.ModelExpansive f
end Comorphism

namespace Morphism
variable {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}
  (f : Morphism A B)

/-- Every model translation is surjective (borrowing holds; silmaril's `Inst.Hom.Sound`). -/
abbrev Sound : Prop := Inst.Hom.Sound f
end Morphism
end Silmaril.Inst
