module

import Silmaril.SSA.Peggy.Bridge.Equational.Thms

namespace Silmaril.SSA.Peggy.Bridge.Equational.Tests

open CategoryTheory Silmaril.Logic.Algebraic
open RVSDG (Tuple)

private inductive TestSort where
  | flag
  | number

private def operandSorts : Fin 3 → TestSort := Fin.cases .flag (fun _ => .number)
private def context : Fin 2 → TestSort := Fin.cases .flag (fun _ => .number)

private inductive Op : (n : Nat) → (Fin n → TestSort) → TestSort → Type where
  | pick : Op 3 operandSorts .number
  | alternate : Op 3 operandSorts .number
  | seven : Op 0 Fin.elim0 .number

private abbrev source : ManySorted.Signature TestSort := ⟨Op⟩

private def identify : source ⟶ source where
  operations
    | .alternate => .pick
    | .pick => .pick
    | .seven => .seven

private def carrier : TestSort → Type
  | .flag => Bool
  | .number => Nat

private def model : ManySorted.Model source where
  carrier := carrier
  operation
    | .pick, args | .alternate, args => if (show Bool from args 0) then args 1 else args 2
    | .seven, _ => (7 : Nat)

private abbrev Expr := ManySorted.Term source context TestSort.number
private def inputValue : Expr := .var 1
private def literal : Expr := .app .seven (fun i => i.elim0)

private def choose (op : Op 3 operandSorts .number) (left right : Expr) : Expr :=
  .app op (Fin.cases (.var 0) (Fin.cases left (fun _ => right)))

/-- The mixed-sort guard is used repeatedly. Both sides have a nullary application. -/
private abbrev law : ManySorted.Equation source :=
  ⟨2, context, .number, choose .alternate (choose .pick inputValue literal) literal,
    choose .pick inputValue literal⟩

private theorem holds : law.Satisfies model := by
  intro assignment
  let flag : Bool := assignment 0
  let number : Nat := assignment 1
  change (if flag then (if flag then number else 7) else 7) = (if flag then number else 7)
  cases flag <;> rfl

private abbrev peggy := totalPrimitiveInst TestSort
private def translatedModel := expand model

example : peggy.Sat translatedModel (compileEquation law) := by
  apply (((comorphism TestSort).ρ.app source).sat translatedModel law).2
  change law.Satisfies (algebra (expand model))
  rw [algebra_expand]
  exact holds

example : compileEquation (ManySorted.Equation.map identify law) =
    (compileEquation law).map ((signature TestSort).map identify) :=
  compileEquation_map identify law

example : (comorphism TestSort).ModelExpansive := modelExpansive TestSort

private def assignment (flag : Bool) : ∀ j, model.carrier (context j) :=
  Fin.cases flag (fun _ => (9 : Nat))

-- Distinguish the two number slots by evaluating the same compiled term at both guards.
example (flag : Bool) : (compileTerm law.lhs).2.observe translatedModel.val
    (pack context (assignment flag)) Fin.elim0 =
    .cons (some (if flag then 9 else 7 : Nat)) .nil := by
  refine (observe_compileTerm translatedModel law.lhs _ Fin.elim0).trans ?_
  cases flag <;> rfl

private abbrev falseLaw : ManySorted.Equation source := { law with rhs := literal }

example : ¬ peggy.Sat translatedModel (compileEquation falseLaw) := by
  intro satisfied
  have ordinary := (((comorphism TestSort).ρ.app source).sat translatedModel falseLaw).1 satisfied
  change falseLaw.Satisfies (algebra (expand model)) at ordinary
  rw [algebra_expand] at ordinary
  have counterexample := ordinary (assignment true)
  change (9 : Nat) = 7 at counterexample
  cases counterexample

private def partialModel : Institution.Model.{0,0,0} ((signature TestSort).obj source) where
  carrier := carrier
  run _ _ := none

example : ¬ PrimitivesTotal partialModel := by
  intro h
  have defined := h (Opcode.app Op.seven) .nil
  cases defined

end Silmaril.SSA.Peggy.Bridge.Equational.Tests
