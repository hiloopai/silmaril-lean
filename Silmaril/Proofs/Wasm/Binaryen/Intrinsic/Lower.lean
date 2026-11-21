module

public import Silmaril.Wasm.Binaryen.Intrinsic.Defs

public section

namespace Silmaril.Proofs.Wasm.Binaryen.Intrinsic

open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Binaryen.Intrinsic
open Silmaril.Wasm.Validation (Context CValType)
open Silmaril.Wasm.Validation.Intrinsic (Body Step)

mutual

theorem lower_expr : {context : Context} → {result : Option CValType} → (expr : Expr context result) →
    expr.erase.lower = expr.toCore.erase
  | _, _, .nop | _, _, .intConst .. | _, _, .localGet .. => rfl
  | _, _, .drop _ value => by
    simp only [Expr.erase, Expr.toCore, BExpr.lower, BExpr.lowerList_singleton,
      thenPlain, Body.erase, Step.erase]
    rw [lower_expr value]
  | _, result, .call ref args => by
    change BExpr.lowerList args.erase ++ [.call ref.ref.index] =
      args.toCore.erase ++ [(callStep (result := result) ref).erase]
    rw [lower_operands args, callStep_erase (result := result) ref]
  | _, _, .block _ _ body | _, _, .loop _ _ body => by
    simp only [Expr.erase, Expr.toCore, BExpr.lower, BExpr.lowerList_singleton, Body.erase, Step.erase]
    rw [lower_expr body]
  | _, _, .if_ _ _ cond thenExpr elseExpr => by
    simp only [Expr.erase, Expr.toCore, BExpr.lower, BExpr.lowerList_singleton,
      thenPlain, Body.erase, Step.erase, lower_expr cond, lower_expr thenExpr, lower_expr elseExpr]
    rfl
  | _, _, .brIf _ cond => by
    simp only [Expr.erase, Expr.toCore, BExpr.lower, BExpr.lowerList_singleton,
      thenPlain, Body.erase, Step.erase]
    rw [lower_expr cond]
termination_by structural _ _ expr => expr

theorem lower_operands : {context : Context} → {types : List CValType} → (args : Operands context types) →
    BExpr.lowerList args.erase = args.toCore.erase
  | _, _, .nil => rfl
  | _, _, .cons _ head rest => by
    change head.erase.lower ++ BExpr.lowerList rest.erase = head.toCore.erase ++ rest.toCore.erase
    rw [lower_expr head, lower_operands rest]
termination_by structural _ _ args => args

end

end Silmaril.Proofs.Wasm.Binaryen.Intrinsic
