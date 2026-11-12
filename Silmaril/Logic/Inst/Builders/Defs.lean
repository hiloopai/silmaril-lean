module

public import Silmaril.Logic.Inst.Builders.Core.Defs
public import Silmaril.Logic.Inst.Defs

/-! # Institution builders with the borrowing compatibility API -/

@[expose] public section

namespace Silmaril.Inst.Comorphism
open CategoryTheory
open Silmaril.Logic.Institution (Room)
universe u v w m₁ m₂

/-- The comorphism of an equivalence is model-expansive: the inverse provides preimages. -/
theorem ofIso_modelExpansive {Sign : Type u} [Category.{v} Sign] {I J : Sign ⥤ Room.{w, m₁, m₂}}
    (e : I ≅ J) : (ofIso e).ModelExpansive := by
  intro S M
  refine ⟨(e.inv.app S).mod.obj M, ?_⟩
  have h := congrArg (fun c : I.obj S ⟶ I.obj S => c.mod.obj M) (e.hom_inv_id_app S)
  exact h

end Silmaril.Inst.Comorphism
