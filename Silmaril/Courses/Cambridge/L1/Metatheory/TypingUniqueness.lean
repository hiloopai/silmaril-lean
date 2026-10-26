module

public import Silmaril.Courses.Cambridge.L1.Metatheory.PreservationByTyping

/-! # Cambridge L1 Exercise 18: uniqueness by typing induction

`HasType.unique` already follows from the sound and complete inferencer. This
proof instead uses only the typing rules. Every rule fixes its result type
except conditionals and sequencing, whose result comes from a subderivation.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1

/-- Theorem 7, proved directly by induction over the first typing derivation. -/
theorem HasType.unique_by_rules {Γ : TypeEnv} {e : Expr} {T U : Ty}
    (first : HasType Γ e T) (second : HasType Γ e U) : T = U := by
  induction first generalizing U with
  | int => cases second; rfl
  | bool => cases second; rfl
  | add => cases second; rfl
  | ge => cases second; rfl
  | cond _ _ _ _ ihYes _ =>
      cases second with
      | cond _ otherYes _ => exact ihYes otherYes
  | assign => cases second; rfl
  | deref => cases second; rfl
  | skip => cases second; rfl
  | seq _ _ _ ihRight =>
      cases second with
      | seq _ otherRight => exact ihRight otherRight
  | loop => cases second; rfl

end Silmaril.Courses.Cambridge.L1
