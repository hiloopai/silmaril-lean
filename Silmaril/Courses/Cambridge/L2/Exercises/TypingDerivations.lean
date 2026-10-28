module

public import Silmaril.Courses.Cambridge.L2.Typing

/-! # Cambridge L2, Exercise 21

The conditional with integer test has no derivation. In the second expression,
the inner Boolean parameter shadows the outer integer parameter only within
the inner function; resolving the names makes the two `x` occurrences point to
different binders.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.Exercises.TypingDerivations

open Silmaril.Courses.Cambridge.L2

def badConditional : Expr :=
  .cond (.int 6) (.int 7) (.int 8)

theorem badConditional_infer : infer TypeEnv.empty badConditional = none := rfl

theorem badConditional_untypable :
    ¬ ∃ T, HasType TypeEnv.empty badConditional T := by
  rintro ⟨T, typing⟩
  have result := infer_complete typing
  rw [badConditional_infer] at result
  cases result

def shadowing : RawExpr :=
  .lam "x" .int
    (.binary (.var "x") .add
      (.app
        (.lam "x" .bool (.cond (.var "x") (.int 3) (.int 4)))
        (.bool true)))

theorem shadowing_tree : shadowing.resolve [] =
    .lam .int
      (.binary (.bvar 0) .add
        (.app (.lam .bool (.cond (.bvar 0) (.int 3) (.int 4))) (.bool true))) := by
  decide

theorem shadowing_hasType :
    HasType TypeEnv.empty (shadowing.resolve []) (.arr .int .int) := by
  rw [shadowing_tree]
  apply HasType.lam
  apply HasType.add
  · exact HasType.bvar rfl
  · apply HasType.app
    · apply HasType.lam
      apply HasType.cond
      · exact HasType.bvar rfl
      · exact HasType.int 3
      · exact HasType.int 4
    · exact HasType.bool true

theorem shadowing_infer :
    infer TypeEnv.empty (shadowing.resolve []) = some (.arr .int .int) :=
  infer_complete shadowing_hasType

end Silmaril.Courses.Cambridge.L2.Exercises.TypingDerivations
