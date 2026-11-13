module

public import Silmaril.Machine.SystemV.Abi.Ctypes.Defs

@[expose] public section
namespace Silmaril.Machine.SystemV.Abi
open Silmaril.Cerberus
open Silmaril.Cerberus.Mem.Concrete (Tags)

/-- Supported LP64 integer widths are explicit. -/
theorem integerBytes_supported (base : IntegerBaseType) (bytes : Nat)
    (classified : integerBytes base = .ok bytes) :
    bytes = 1 ∨ bytes = 2 ∨ bytes = 4 ∨ bytes = 8 ∨ bytes = 16 := by
  cases base <;> simp_all [integerBytes]
  split at classified
  · rename_i width
    have equality : _ = bytes := Except.ok.inj classified
    omega
  · cases classified

/-- Successful non-enum integer classification retains its native size and alignment. -/
theorem integerObject_ordinary_shape (tags : Tags) (integer : IntegerType) (object : Object)
    (nonenum : ∀ tag, integer ≠ .enum tag) (classified : integerObject tags integer = .ok object) :
    ∃ bytes, object = Object.integer bytes bytes ∧
      (bytes = 1 ∨ bytes = 2 ∨ bytes = 4 ∨ bytes = 8 ∨ bytes = 16) := by
  cases integer with
  | enum tag => exact False.elim (nonenum tag rfl)
  | signed base | unsigned base =>
    cases computed : integerBytes base with
    | error why => simp [integerObject, computed] at classified
    | ok bytes =>
      have same : object = Object.integer bytes bytes := by
        simpa [integerObject, computed] using classified.symm
      exact ⟨bytes, same, integerBytes_supported base bytes computed⟩
  | char | bool | wchar | wint | size | ptrdiff | ptraddr =>
    simp only [integerObject] at classified
    cases classified
    first | exact ⟨1, rfl, Or.inl rfl⟩
          | exact ⟨4, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
          | exact ⟨8, rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩

/-- Unsupported source attributes cannot receive a native object classification. -/
theorem objectOfCtype_annotations_supported (tags : Tags) (annotations : List Annot)
    (node : CtypeNode) (object : Object)
    (classified : objectOfCtype tags (.mk annotations node) = .ok object) :
    annotationsSupported annotations = true := by
  by_contra unsupported
  have rejected : annotationsSupported annotations = false := Bool.eq_false_iff.mpr unsupported
  unfold objectOfCtype layoutOfCtype at classified
  rw [layoutOfCtypeWithFuel.eq_def] at classified
  simp only [rejected, Bool.false_eq_true, ↓reduceIte] at classified
  change (Except.error "native type attributes require resolved layout metadata" : Except String Object) =
    Except.ok object at classified
  cases classified

/-- Source integer object classification is exactly its integer implementation classification. -/
theorem objectOfCtype_integer (tags : Tags) (annotations : List Annot)
    (integer : IntegerType) (object : Object) (supported : annotationsSupported annotations = true)
    (classified : objectOfCtype tags (.mk annotations (.basic (.integer integer))) = .ok object) :
    integerObject tags integer = .ok object := by
  cases computed : integerObject tags integer with
  | error why =>
    simp [objectOfCtype, layoutOfCtype, layoutOfCtypeWithFuel, scalarObject,
      supported, computed, Except.map] at classified
  | ok result =>
    have same : result = object := by
      simpa [objectOfCtype, layoutOfCtype, layoutOfCtypeWithFuel, scalarObject,
        supported, computed, Except.map] using classified
    exact congrArg Except.ok same


end Silmaril.Machine.SystemV.Abi
