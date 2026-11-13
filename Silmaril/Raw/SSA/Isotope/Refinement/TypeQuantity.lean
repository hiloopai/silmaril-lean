module

public import Silmaril.Raw.SSA.Isotope.Refinement.Contexts
public import Silmaril.SSA.Isotope.Types.Thms

@[expose] public section

/-! # Extending base-type quantities to the free type language -/

namespace Silmaril.Isotope.Refinement

universe u
variable {α : Type u} [HasQuantity α]

/-- Linearity of a freely generated type, exactly as in the written signature. -/
def typeQuantity : Ty α → Quantity
  | .base a => quantity a
  | .product A B | .coprod A B => typeQuantity A ⊓ typeQuantity B
  | .unit | .empty => ⊤

instance : TypeQuantity (Ty α) where
  quantity := typeQuantity
  product_quantity _ _ := rfl
  coproduct_quantity _ _ := rfl
  unit_quantity := rfl
  empty_quantity := rfl

@[simp] theorem quantity_base (a : α) : quantity (Ty.base a) = quantity a := rfl
@[simp] theorem quantity_product (A B : Ty α) : quantity (Ty.product A B) = quantity A ⊓ quantity B := rfl
@[simp] theorem quantity_coprod (A B : Ty α) : quantity (Ty.coprod A B) = quantity A ⊓ quantity B := rfl
@[simp] theorem quantity_unit : quantity (Ty.unit : Ty α) = ⊤ := rfl
@[simp] theorem quantity_empty : quantity (Ty.empty : Ty α) = ⊤ := rfl

end Silmaril.Isotope.Refinement
