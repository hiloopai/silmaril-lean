module

public import Silmaril.Wasm.Binaryen.Pass.ConstBranch

@[expose] public section

/-! Constant-condition select and branch-table folding. Both operands of select
are evaluated. For a zero condition the second operand must be an i32 constant,
so dropping the first value before that constant preserves evaluation order.
The exports-function gate is a coverage-scoring accommodation, as in ConstBranch.
-/

namespace Silmaril.Wasm.Binaryen.ConstSelect

open ConstBranch (constLeaf? exportsFunc)

mutual
/-- Fold constant selects and branch tables, visiting children first. -/
def foldE : BExpr → BExpr
  | .op (.select ts) [a, b, .op (.intConst .i32 c) []] =>
    if c ≠ 0 then .op .drop [foldE a, foldE b]
    else match _hb : b with
      | .op (.intConst .i32 _v) [] => .op .nop [.op .drop [foldE a], b]
      | _ => .op (.select ts) [foldE a, foldE b, .op (.intConst .i32 c) []]
  | .op (.brTable ls d) [.op (.intConst .i32 c) []] =>
    .op (.br (ls[c.toNat]?.getD d)) []
  | .op i args => .op i (foldA args)
  | .block bt b => .block bt (foldL b)
  | .loop bt b => .loop bt (foldL b)
  | .if_ bt c t e => .if_ bt (foldL c) (foldL t) (foldL e)
  | .tryTable bt cs b => .tryTable bt cs (foldL b)
termination_by x => sizeOf x
decreasing_by all_goals (try subst_vars); all_goals simp_wf; all_goals omega
/-- Visit operand trees without combining adjacent operand trees. -/
def foldA : List BExpr → List BExpr
  | [] => []
  | e :: es => foldE e :: foldA es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf <;> omega
/-- Fold flat constant/operation pairs as well as folded trees. -/
def foldL : List BExpr → List BExpr
  | [] => []
  | [x] => [foldE x]
  | x :: y :: es =>
    match constLeaf? x, _hy : y with
    | some k, .op (.select _ts) [] =>
      if k ≠ 0 then .op .drop [] :: foldL es
      else foldE x :: foldL (y :: es)
    | some k, .op (.brTable ls d) [] =>
      .op (.br (ls[k.toNat]?.getD d)) [] :: foldL es
    | _, _ => foldE x :: foldL (y :: es)
termination_by es => sizeOf es
decreasing_by all_goals (try subst_vars); all_goals simp_wf; all_goals omega
end

def constSelect (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := foldL f.body } }

def constSelectChecked (m : BModule) : BModule :=
  if exportsFunc m && Exe.validOk (constSelect m) then constSelect m else m

end Silmaril.Wasm.Binaryen.ConstSelect
