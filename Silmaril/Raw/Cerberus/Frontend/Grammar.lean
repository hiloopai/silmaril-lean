module

public import Silmaril.Cerberus.Frontend.Expressions.Defs
public import Silmaril.Cerberus.Frontend.Statements.Defs

/-! # The grammar: the recursion knot

`knot n` is the record of the recursive nonterminals, each calling the others through
`knot (n - 1)`; at depth 0 they reject. The record is built lazily, one level per
recursive call, so the depth bounds the nesting that the parser follows, and it never
reaches the native stack's limit.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Grammar

open Silmaril.Cerberus Cabs

/-- The nonterminals of `Rec`, with recursion depth `n`. -/
def knot : Nat → Rec
  | 0 => Rec.exhausted
  | n + 1 =>
    { expression := fun s => Expressions.expression (knot n) s
      assignmentExpression := fun s => Expressions.assignmentExpression (knot n) s
      constantExpression := fun s => Expressions.constantExpression (knot n) s
      unaryExpression := fun s => Expressions.unaryExpression (knot n) s
      castExpression := fun s => Expressions.castExpression (knot n) s
      binaryExpression := fun p s => Expressions.binaryExpression (knot n) p s
      conditionalExpression := fun s => Expressions.conditionalExpression (knot n) s
      typeName := fun s => Declarations.typeName (knot n) s
      initr := fun s => Declarations.initr (knot n) s
      compoundStatement := fun s => Statements.compoundStatement (knot n) s
      statement := fun s => Statements.statement (knot n) s
      declarator := fun m s => Declarations.declaratorAny (knot n) m s
      specifiers := fun m s => Declarations.specifiers (knot n) m s }

/-- How deep the parser follows nesting through `Rec`. -/
def depth : Nat := 1000000

end Silmaril.Cerberus.Frontend.Grammar
