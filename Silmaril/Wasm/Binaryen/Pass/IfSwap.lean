module

public import Silmaril.Wasm.Binaryen.Syntax
public import Silmaril.Wasm.Binaryen.Exe.Valid

@[expose] public section

/-! # OptimizeInstructions-lite: swap the arms of an `if` on `i32.eqz`

The arm swap of Binaryen's `OptimizeInstructions::visitIf`
(`src/passes/OptimizeInstructions.cpp`, `version_133`): an `if` whose condition is
`i32.eqz c` runs its else arm exactly when `c` is nonzero, so

  `if bt (i32.eqz c) A else B` ⟶ `if bt c B else A`

drops one instruction. The swap is done only when the else arm is non-empty: an empty
else arm would need an `else` byte in the output, cancelling the saved `eqz`. Only
`i32.eqz` qualifies (`i64.eqz` would leave an `i64` condition). Bottom-up; the result
of a swap is not matched again.

Run functions only. The verified stage is `ifSwapChecked`, kept when the validator
accepts its result; its contract is `optimizeInstructions_stageOk`
(`Exe/PeepholeStage.lean`).
-/

namespace Silmaril.Wasm.Binaryen.IfSwap

/-- Rebuild an `if` from its visited parts, swapping the arms when the condition is
`i32.eqz c` and the else arm is non-empty. -/
def swapIf (bt : BlockType) (c t e : List BExpr) : BExpr :=
  match c, e with
  | [.op (.intTestOp .i32 .eqz) a], _ :: _ => .if_ bt a e t
  | _, _ => .if_ bt c t e

mutual
/-- Swap the arms of every eligible `if` in a tree, children first. -/
def swapE : BExpr → BExpr
  | .op i args => .op i (swapL args)
  | .block bt b => .block bt (swapL b)
  | .loop bt b => .loop bt (swapL b)
  | .if_ bt c t e => swapIf bt (swapL c) (swapL t) (swapL e)
  | .tryTable bt cs b => .tryTable bt cs (swapL b)
/-- `swapE` on each tree of a sequence. -/
def swapL : List BExpr → List BExpr
  | [] => []
  | e :: es => swapE e :: swapL es
end

/-- The arm swap of every function body. -/
def ifSwap (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := swapL f.body } }

/-- **The OptimizeInstructions-lite stage**: the arm swap, kept when the validator
accepts it. -/
def ifSwapChecked (m : BModule) : BModule :=
  if Exe.validOk (ifSwap m) then ifSwap m else m

end Silmaril.Wasm.Binaryen.IfSwap
