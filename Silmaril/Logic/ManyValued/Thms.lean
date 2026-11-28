module

public import Silmaril.Logic.ManyValued.Defs

@[expose] public section

/-! # Laws of the finite truth and information orders -/

namespace Silmaril.Logic.ManyValued

namespace K3

@[simp] theorem bot_eq : (⊥ : K3) = ff := rfl
@[simp] theorem top_eq : (⊤ : K3) = tt := rfl

theorem le_iff_truthRank_le (a b : K3) : a ≤ b ↔ a.truthRank ≤ b.truthRank := Iff.rfl

@[simp] theorem neg_neg (a : K3) : a.neg.neg = a := by cases a <;> rfl

theorem neg_le_neg_iff (a b : K3) : a.neg ≤ b.neg ↔ b ≤ a := by
  cases a <;> cases b <;> decide

@[simp] theorem neg_inf (a b : K3) : (a ⊓ b).neg = a.neg ⊔ b.neg := by
  cases a <;> cases b <;> rfl

@[simp] theorem neg_sup (a b : K3) : (a ⊔ b).neg = a.neg ⊓ b.neg := by
  cases a <;> cases b <;> rfl

@[simp] theorem ofBool_not (a : Bool) : ofBool (!a) = (ofBool a).neg := by cases a <;> rfl

@[simp] theorem ofBool_and (a b : Bool) : ofBool (a && b) = ofBool a ⊓ ofBool b := by
  cases a <;> cases b <;> rfl

@[simp] theorem ofBool_or (a b : Bool) : ofBool (a || b) = ofBool a ⊔ ofBool b := by
  cases a <;> cases b <;> rfl

@[simp] theorem ofBool_le_ofBool (a b : Bool) : ofBool a ≤ ofBool b ↔ a ≤ b := by
  cases a <;> cases b <;> decide

@[simp] theorem isDesignated_ofBool (a : Bool) : (ofBool a).isDesignated = a := by
  cases a <;> rfl

theorem isDesignated_iff (a : K3) : a.isDesignated = true ↔ a = tt := by
  cases a <;> decide

@[simp] theorem toOptionBool_ofOptionBool (a : Option Bool) : (ofOptionBool a).toOptionBool = a := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl

@[simp] theorem ofOptionBool_toOptionBool (a : K3) : ofOptionBool a.toOptionBool = a := by
  cases a <;> rfl

@[simp] theorem toOptionBool_neg (a : K3) : a.neg.toOptionBool = a.toOptionBool.map Bool.not := by
  cases a <;> rfl

namespace Information

@[simp] theorem bot_eq : (⊥ : Information) = ⟨K3.unknown⟩ := rfl

theorem le_iff (a b : Information) : a ≤ b ↔ a.val = .unknown ∨ a.val = b.val := Iff.rfl

/-- In partial Boolean form, refinement preserves each known result. -/
theorem le_iff_toOptionBool (a b : Information) :
    a ≤ b ↔ ∀ x, a.val.toOptionBool = some x → b.val.toOptionBool = some x := by
  rcases a with ⟨⟨⟩⟩ <;> rcases b with ⟨⟨⟩⟩ <;> simp [le_iff, toOptionBool]

/-- The two known values have no common information upper bound. -/
theorem known_no_common_upper_bound (c : Information) : ¬ (⟨K3.ff⟩ ≤ c ∧ ⟨K3.tt⟩ ≤ c) := by
  obtain ⟨c⟩ := c
  cases c <;> decide

@[simp] theorem neg_le_neg_iff (a b : Information) : a.neg ≤ b.neg ↔ a ≤ b := by
  rcases a with ⟨⟨⟩⟩ <;> rcases b with ⟨⟨⟩⟩ <;> decide

@[simp] theorem neg_inf (a b : Information) : (a ⊓ b).neg = a.neg ⊓ b.neg := by
  rcases a with ⟨⟨⟩⟩ <;> rcases b with ⟨⟨⟩⟩ <;> rfl

end Information
end K3

namespace FDE

@[simp] theorem bot_eq : (⊥ : FDE) = ff := rfl
@[simp] theorem top_eq : (⊤ : FDE) = tt := rfl

@[simp] theorem ofBits_support_refute (a : FDE) : ofBits a.support a.refute = a := by
  cases a <;> rfl

@[simp] theorem support_ofBits (s r : Bool) : (ofBits s r).support = s := by
  cases s <;> cases r <;> rfl

@[simp] theorem refute_ofBits (s r : Bool) : (ofBits s r).refute = r := by
  cases s <;> cases r <;> rfl

@[simp] theorem support_neg (a : FDE) : a.neg.support = a.refute := support_ofBits _ _

@[simp] theorem refute_neg (a : FDE) : a.neg.refute = a.support := refute_ofBits _ _

theorem le_iff_bits (a b : FDE) : a ≤ b ↔ a.support ≤ b.support ∧ b.refute ≤ a.refute := Iff.rfl

@[simp] theorem neg_neg (a : FDE) : a.neg.neg = a := by cases a <;> rfl

theorem neg_le_neg_iff (a b : FDE) : a.neg ≤ b.neg ↔ b ≤ a := by
  cases a <;> cases b <;> decide

@[simp] theorem neg_inf (a b : FDE) : (a ⊓ b).neg = a.neg ⊔ b.neg := by
  cases a <;> cases b <;> rfl

@[simp] theorem neg_sup (a b : FDE) : (a ⊔ b).neg = a.neg ⊓ b.neg := by
  cases a <;> cases b <;> rfl

@[simp] theorem ofBool_not (a : Bool) : ofBool (!a) = (ofBool a).neg := by cases a <;> rfl

@[simp] theorem ofBool_and (a b : Bool) : ofBool (a && b) = ofBool a ⊓ ofBool b := by
  cases a <;> cases b <;> rfl

@[simp] theorem ofBool_or (a b : Bool) : ofBool (a || b) = ofBool a ⊔ ofBool b := by
  cases a <;> cases b <;> rfl

@[simp] theorem ofBool_le_ofBool (a b : Bool) : ofBool a ≤ ofBool b ↔ a ≤ b := by
  cases a <;> cases b <;> decide

@[simp] theorem isDesignated_ofBool (a : Bool) : (ofBool a).isDesignated = a := by
  cases a <;> rfl

theorem isDesignated_iff (a : FDE) : a.isDesignated = true ↔ a = tt ∨ a = both := by
  cases a <;> decide

namespace Information

@[simp] theorem bot_eq : (⊥ : Information) = ⟨FDE.neither⟩ := rfl
@[simp] theorem top_eq : (⊤ : Information) = ⟨FDE.both⟩ := rfl

theorem le_iff_bits (a b : Information) :
    a ≤ b ↔ a.val.support ≤ b.val.support ∧ a.val.refute ≤ b.val.refute := Iff.rfl

@[simp] theorem neg_le_neg_iff (a b : Information) : a.neg ≤ b.neg ↔ a ≤ b := by
  rcases a with ⟨⟨⟩⟩ <;> rcases b with ⟨⟨⟩⟩ <;> decide

@[simp] theorem neg_inf (a b : Information) : (a ⊓ b).neg = a.neg ⊓ b.neg := by
  rcases a with ⟨⟨⟩⟩ <;> rcases b with ⟨⟨⟩⟩ <;> rfl

@[simp] theorem neg_sup (a b : Information) : (a ⊔ b).neg = a.neg ⊔ b.neg := by
  rcases a with ⟨⟨⟩⟩ <;> rcases b with ⟨⟨⟩⟩ <;> rfl

end Information
end FDE

namespace K3

@[simp] theorem toFDE_ofBool (a : Bool) : (ofBool a).toFDE = FDE.ofBool a := by
  cases a <;> rfl

@[simp] theorem toFDE_ofOptionBool (a : Option Bool) :
    (ofOptionBool a).toFDE = FDE.ofOptionBool a := by
  cases a with
  | none => rfl
  | some b => exact toFDE_ofBool b

@[simp] theorem toFDE_neg (a : K3) : a.neg.toFDE = a.toFDE.neg := by
  cases a <;> rfl

@[simp] theorem toFDE_inf (a b : K3) : (a ⊓ b).toFDE = a.toFDE ⊓ b.toFDE := by
  cases a <;> cases b <;> rfl

@[simp] theorem toFDE_sup (a b : K3) : (a ⊔ b).toFDE = a.toFDE ⊔ b.toFDE := by
  cases a <;> cases b <;> rfl

@[simp] theorem toFDE_le_iff (a b : K3) : a.toFDE ≤ b.toFDE ↔ a ≤ b := by
  cases a <;> cases b <;> decide

@[simp] theorem toFDE_isDesignated (a : K3) : a.toFDE.isDesignated = a.isDesignated := by
  cases a <;> rfl

@[simp] theorem toFDE_toK3? (a : K3) : a.toFDE.toK3? = some a := by
  cases a <;> rfl

theorem toFDE_injective : Function.Injective toFDE := by
  intro a b h
  simpa using congrArg FDE.toK3? h

namespace Information

@[simp] theorem toFDE_le_iff (a b : Information) : a.toFDE ≤ b.toFDE ↔ a ≤ b := by
  rcases a with ⟨⟨⟩⟩ <;> rcases b with ⟨⟨⟩⟩ <;> decide

@[simp] theorem toFDE_inf (a b : Information) : (a ⊓ b).toFDE = a.toFDE ⊓ b.toFDE := by
  rcases a with ⟨⟨⟩⟩ <;> rcases b with ⟨⟨⟩⟩ <;> rfl

@[simp] theorem toFDE_neg (a : Information) : a.neg.toFDE = a.toFDE.neg :=
  congrArg FDE.Information.mk (K3.toFDE_neg a.val)

end Information
end K3

namespace FDE

/-- Membership in the consistent image is equivalent to successfully decoding
the corresponding K3 value. -/
theorem toK3?_eq_some_iff (a : FDE) (b : K3) : a.toK3? = some b ↔ b.toFDE = a := by
  cases a <;> cases b <;> decide

@[simp] theorem toK3?_eq_none_iff (a : FDE) : a.toK3? = none ↔ a = both := by
  cases a <;> decide

theorem toOptionBool?_eq_some_iff (a : FDE) (b : Option Bool) :
    a.toOptionBool? = some b ↔ ofOptionBool b = a := by
  cases b with
  | none => cases a <;> decide
  | some b => cases a <;> cases b <;> decide

@[simp] theorem toOptionBool?_ofOptionBool (b : Option Bool) :
    (ofOptionBool b).toOptionBool? = some b :=
  (toOptionBool?_eq_some_iff _ _).2 rfl

@[simp] theorem toOptionBool?_eq_none_iff (a : FDE) : a.toOptionBool? = none ↔ a = both := by
  cases a <;> decide

end FDE

end Silmaril.Logic.ManyValued
