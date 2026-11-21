module

public import Silmaril.Compiler.C.Compact.Defs

public section
namespace Silmaril.Proofs.Compiler.C.Compact

open Silmaril.Compiler.C.Compact Silmaril.Compile.C Silmaril.Compile.C.Sem
open Silmaril.Cerberus Silmaril.Cerberus.Ail

theorem typeOf_eq {scope : List Sym} {expr : Expr} {ail : TypedExpression}
    (matched : Projects scope expr ail) : typeOf ail = .int 4 true := by
  cases matched <;> assumption

theorem eval_eq {scope : List Sym} {expr : Expr} {ail : TypedExpression}
    (matched : Projects scope expr ail) (program : C0.Prog) (fn : C0.FunDef) (env : C0.Env)
    (read : Nat → Except C0.Stop Int)
    (related : ∀ index symbol, scope[index]? = some symbol → read index = C0.readVar fn env symbol)
    (fuel : Nat) (enough : expr.depth ≤ fuel) :
    C0.evalE program fuel fn ail env = (expr.eval read).map (·, env) := by
  induction matched generalizing fuel with
  | literal typed value annots loc =>
    cases fuel with
    | zero => simp [Expr.depth] at enough
    | succ fuel =>
      simp only [C0.evalE.eq_2, Expression.node, typeOf, Expression.annotation, valueType, typed]
      rfl
  | slot lookup typed quals ctype annots innerAnnots loc innerLoc =>
    cases fuel with
    | zero => simp [Expr.depth] at enough
    | succ fuel =>
      simp only [C0.evalE.eq_2, Expression.node, C0.lvalSym, Expr.eval, bind, Except.bind]
      rw [← related _ _ lookup]
      generalize read _ = value
      cases value <;> rfl
  | @bin left right ailLeft ailRight op ty typed annots loc lhs rhs ihLeft ihRight =>
    cases fuel with
    | zero => simp [Expr.depth] at enough
    | succ fuel =>
      have bound := Nat.le_of_succ_le_succ enough
      have evalLeft := ihLeft fuel (le_trans (Nat.le_max_left _ _) bound)
      have evalRight := ihRight fuel (le_trans (Nat.le_max_right _ _) bound)
      cases op <;> simp only [Op.ail, C0.evalE.eq_2, Expression.node, Expr.eval]
      all_goals
        rw [evalLeft]
        cases left.eval read with
        | error stop => rfl
        | ok lhsValue =>
          simp only [Except.map, bind, Except.bind]
          rw [evalRight]
          cases right.eval read with
          | error stop => rfl
          | ok rhsValue =>
            simp only [Except.map]
            first
            | rw [typeOf_eq lhs, typeOf_eq rhs]
              change Except.ok ((if decide (C0.wrap 4 true lhsValue > C0.wrap 4 true rhsValue)
                then 1 else 0), env) = Except.ok ((if C0.wrap 4 true lhsValue > C0.wrap 4 true rhsValue
                then 1 else 0), env)
              simp
            | simp only [typeOf, Expression.annotation, valueType, typed]
              change (do
                let value ← Op.eval .add lhsValue rhsValue
                pure (value, env)) = (Op.eval .add lhsValue rhsValue).map (·, env)
              cases Op.eval .add lhsValue rhsValue <;> rfl

end Silmaril.Proofs.Compiler.C.Compact
