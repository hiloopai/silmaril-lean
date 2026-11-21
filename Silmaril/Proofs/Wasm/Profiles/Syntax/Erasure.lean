module

public import Silmaril.Wasm.Profiles.Syntax.Defs

public section

namespace Silmaril.Proofs.Wasm.Profiles.Syntax

open Silmaril.Wasm.Profiles.Syntax

theorem erasureChecked_injective {family : Family} (witness : Intrinsic family) (index : family.Index) :
    Function.Injective (witness.erasureChecked (index := index)) := by
  intro left right
  induction left using Quot.ind with
  | mk left =>
    induction right using Quot.ind with
    | mk right =>
      intro eq
      exact Quot.sound (congrArg Subtype.val eq)

theorem someChecked_surjective {family : Family} {witness : Intrinsic family} (covers : witness.Lifts) :
    Function.Surjective witness.someChecked := by
  rintro ⟨index, term, valid⟩
  obtain ⟨witnessTerm, rfl⟩ := covers valid
  exact ⟨⟨index, witnessTerm⟩, rfl⟩

theorem forget_injective {family : Family} (unique : family.UniqueIndex) : Function.Injective family.forget := by
  rintro ⟨leftIndex, left, leftOk⟩ ⟨rightIndex, right, rightOk⟩ eq
  have rawEq : left = right := congrArg Subtype.val eq
  subst right
  obtain rfl := unique leftOk rightOk
  rfl

theorem coreFunction_unique (context : Wasm.Validation.Context) : (Core.functionSyntax context).UniqueIndex := by
  intro fn left right leftOk rightOk
  cases leftOk with
  | mk leftResolved _ _ _ =>
    cases rightOk with
    | mk rightResolved _ _ _ => exact Option.some.inj (leftResolved.symm.trans rightResolved)

end Silmaril.Proofs.Wasm.Profiles.Syntax
