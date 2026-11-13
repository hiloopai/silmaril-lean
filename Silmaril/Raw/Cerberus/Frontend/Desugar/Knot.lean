module

public import Silmaril.Cerberus.Frontend.Desugar.External.Defs

/-! # The desugaring: the recursion knot

`knot n` is the record of the recursive desugaring functions, each calling the others
through `knot (n - 1)`; at depth 0 they reject. The record is built lazily, one level per
recursive call, as the parser's `Grammar.knot`.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus

/-- The recursive desugaring functions, with recursion depth `n`. -/
def knot : Nat → Rec
  | 0 => Rec.exhausted
  | n + 1 =>
    { typeSpecifiers := fun s => desugarTypeSpecifiers (knot n) s
      pointerDeclarator := fun p => desugarPointerDeclarator (knot n) p
      abstractDeclarator := fun u d => desugarAbstractDeclarator (knot n) u d
      directAbstractDeclarator := fun u d => desugarDirectAbstractDeclarator (knot n) u d
      directDeclarator := fun f u d => desugarDirectDeclarator (knot n) f u d
      declarator := fun f d => desugarDeclarator (knot n) f d
      typeName := fun t => desugarTypeName (knot n) t
      expression := fun e => desugarExpression (knot n) e
      wipInitializer := fun loc dur ty init => wipDesugarInitialiser (knot n) loc dur ty init
      statementAux := fun ctx s => desugarStatementAux (knot n) ctx s }

/-- How deep the desugaring follows nesting through `Rec`: as deep as the parser. -/
def depth : Nat := 1000000

end Silmaril.Cerberus.Frontend.Desugar
