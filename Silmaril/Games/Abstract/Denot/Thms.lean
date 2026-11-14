module

public import Silmaril.Games.Abstract.Denot.Defs
public import Silmaril.Games.Abstract.Game.Thms

/-!
# Partial denotations: theorems

* `ofPartial_le_iff`: for partial maps read with undefined as `⊤`, `d ≤ e` iff
  wherever `e` is defined, `d` is defined too, with a smaller model.
* `toLower_mono`, `toLower_coe_le_coe_iff`: the lower-set reading is monotone
  and reflects the order on defined models.
* `toLower_top_eq_coe_top`: it collapses "undefined" onto the chaotic model.
* `coe_top_lt_top`: in the `WithTop` reading the two are distinct, with
  chaos strictly below "no claim".
-/

public section

namespace Silmaril.Games.Abstract.Denot

universe u v

variable {α : Type v} {G : Game.{u}}

/-- The order on partial denotations: less defined or larger. -/
theorem ofPartial_le_iff {f g : α → Option (TraceModel G)} :
    ofPartial f ≤ ofPartial g ↔
      ∀ a, ∀ U, g a = some U → ∃ T, f a = some T ∧ T ≤ U := by
  constructor
  · intro h a U hU
    have := h a
    unfold ofPartial at this
    rw [hU] at this
    cases hf : f a with
    | none => rw [hf] at this; exact absurd this (by simp)
    | some T => rw [hf] at this; exact ⟨T, rfl, WithTop.coe_le_coe.1 this⟩
  · intro h a
    unfold ofPartial
    cases hg : g a with
    | none => exact le_top
    | some U =>
      obtain ⟨T, hT, hle⟩ := h a U hg
      rw [hT]
      exact WithTop.coe_le_coe.2 hle

/-- The lower-set reading of a defined model. -/
@[simp] theorem toLower_coe (T : TraceModel G) : toLower (T : WithTop (TraceModel G)) =
    LowerSet.Iic T := rfl

/-- The lower-set reading of "undefined". -/
@[simp] theorem toLower_top : toLower (⊤ : WithTop (TraceModel G)) = ⊤ := rfl

/-- On defined models the lower-set reading reflects the order. -/
theorem toLower_coe_le_coe_iff {T U : TraceModel G} :
    toLower (T : WithTop (TraceModel G)) ≤ toLower (U : WithTop (TraceModel G)) ↔ T ≤ U := by
  simp only [toLower_coe, LowerSet.Iic_le, LowerSet.mem_Iic_iff]

/-- The lower-set reading is monotone. -/
theorem toLower_mono : Monotone (toLower (G := G)) := by
  intro x y h
  cases y with
  | top => exact le_top
  | coe U =>
    cases x with
    | top => exact absurd h (by simp)
    | coe T => exact toLower_coe_le_coe_iff.2 (WithTop.coe_le_coe.1 h)

/-- The lower-set reading identifies "undefined" with the chaotic model. -/
theorem toLower_top_eq_coe_top :
    toLower (⊤ : WithTop (TraceModel G)) = toLower ((⊤ : TraceModel G) : WithTop _) := by
  simp [LowerSet.Iic_top]

/-- In the `WithTop` reading the chaotic model is strictly below "no claim". -/
theorem coe_top_lt_top : ((⊤ : TraceModel G) : WithTop (TraceModel G)) < ⊤ := WithTop.coe_lt_top _

end Silmaril.Games.Abstract.Denot
