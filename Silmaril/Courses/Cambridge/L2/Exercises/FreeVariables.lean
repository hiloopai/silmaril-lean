module

public import Silmaril.Courses.Cambridge.L2.Syntax

/-! # Cambridge L2, Exercise 19

The five printed expressions are represented in named syntax. For each, the
free-variable answer is checked against `RawExpr.freeVars`, and the resolved
expression gives its abstract syntax tree up to alpha equivalence. In the third
tree, the innermost `y` shadows the other two and resolves to index zero.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.Exercises.FreeVariables

open Silmaril.Courses.Cambridge.L2

def first : RawExpr :=
  .binary (.var "x") .add (.app (.lam "y" .int (.var "z")) (.int 2))

def second : RawExpr :=
  .binary (.var "x") .add (.lam "y" .int (.var "z"))

def third : RawExpr :=
  .lam "y" .int (.lam "y" .int (.lam "y" .int (.var "y")))

def fourth : RawExpr := .deref "l0"

def fifth : RawExpr :=
  .loop (.binary (.deref "l0") .ge (.var "y")) (.assign "l0" (.var "x"))

theorem first_freeVars : first.freeVars = {"x", "z"} := by decide
theorem first_tree : first.resolve [] =
    .binary (.fvar "x") .add (.app (.lam .int (.fvar "z")) (.int 2)) := by decide

theorem second_freeVars : second.freeVars = {"x", "z"} := by decide
theorem second_tree : second.resolve [] =
    .binary (.fvar "x") .add (.lam .int (.fvar "z")) := by decide

theorem third_freeVars : third.freeVars = ∅ := by decide
theorem third_tree : third.resolve [] =
    .lam .int (.lam .int (.lam .int (.bvar 0))) := by decide

theorem fourth_freeVars : fourth.freeVars = ∅ := by decide
theorem fourth_tree : fourth.resolve [] = .deref "l0" := by decide

theorem fifth_freeVars : fifth.freeVars = {"x", "y"} := by decide
theorem fifth_tree : fifth.resolve [] =
    .loop (.binary (.deref "l0") .ge (.fvar "y"))
      (.assign "l0" (.fvar "x")) := by decide

end Silmaril.Courses.Cambridge.L2.Exercises.FreeVariables
