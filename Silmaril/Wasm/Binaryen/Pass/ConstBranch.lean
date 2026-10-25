module

public import Silmaril.Wasm.Binaryen.Syntax
public import Silmaril.Wasm.Binaryen.Exe.Valid

@[expose] public section

/-! # ConstBranch: control on a constant `i32` condition

Binaryen folds control flow whose condition is a constant
(`RemoveUnusedBrs`/`OptimizeInstructions`, `version_133`):

* `if bt (i32.const c) A else B` ⟶ `block bt A` when `c ≠ 0`, `block bt B` when `c = 0`;
* `br_if l (i32.const c)` ⟶ `br l` when `c ≠ 0`, `nop` when `c = 0`.

The `if` becomes a `block` with the same type, so the arm keeps its label and the
branch depths inside it are unchanged. A `br_if` is folded only when the condition is
its sole operand tree (a carried value stays). The constant is matched as the child
condition tree or, in an unfolded body, as the leaf just before an `if`/`br_if` without
operand trees. Bottom-up; the condition is matched on the original tree.

Run functions only. The verified stage is `constBranchChecked`, kept when the validator
accepts its result and the module exports a function; its contract is `constBranch_stageOk` (`Exe/ConstBranchStage.lean`).
-/

namespace Silmaril.Wasm.Binaryen.ConstBranch

/-- The constant of an `i32.const` leaf. -/
def constLeaf? : BExpr → Option (BitVec 32)
  | .op (.intConst .i32 c) [] => some c
  | _ => none

/-- The constant of an `i32.const` condition tree. -/
def constCond? : List BExpr → Option (BitVec 32)
  | [x] => constLeaf? x
  | _ => none

/-- Rebuild a `br_if` from its original operand trees `args` and visited ones `args'`. -/
def brIfNode (l : LabelIdx) (args args' : List BExpr) : BExpr :=
  match constCond? args with
  | some c => if c = 0 then .op .nop [] else .op (.br l) []
  | none => .op (.brIf l) args'

/-- Rebuild an instruction node from its visited operand trees. -/
def opNode (i : Instr) (args args' : List BExpr) : BExpr :=
  match i with
  | .brIf l => brIfNode l args args'
  | _ => .op i args'

/-- Rebuild an `if` from its original condition and visited parts. -/
def ifNode (bt : BlockType) (c c' t' e' : List BExpr) : BExpr :=
  match constCond? c with
  | some k => .block bt (if k = 0 then e' else t')
  | none => .if_ bt c' t' e'

mutual
/-- Fold every constant-condition `if` and `br_if` of a tree, children first. -/
def foldE : BExpr → BExpr
  | .op i args => opNode i args (foldL args)
  | .block bt b => .block bt (foldL b)
  | .loop bt b => .loop bt (foldL b)
  | .if_ bt c t e => ifNode bt c (foldL c) (foldL t) (foldL e)
  | .tryTable bt cs b => .tryTable bt cs (foldL b)
termination_by x => sizeOf x
decreasing_by all_goals simp_wf <;> omega
/-- `foldE` on each tree of a sequence; a constant leaf followed by an `if` or `br_if`
without operand trees (an unfolded body) is folded as a pair. -/
def foldL : List BExpr → List BExpr
  | [] => []
  | [x] => [foldE x]
  | x :: y :: es =>
    match constLeaf? x, _hy : y with
    | some k, .if_ bt [] t e => .block bt (if k = 0 then foldL e else foldL t) :: foldL es
    | some k, .op (.brIf l) [] => (if k = 0 then .op .nop [] else .op (.br l) []) :: foldL es
    | _, _ => foldE x :: foldL (y :: es)
termination_by es => sizeOf es
decreasing_by all_goals (try subst_vars); all_goals simp_wf; all_goals omega
end

/-- The constant-condition fold of every function body. -/
def constBranch (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := foldL f.body } }

/-- The module exports a function. -/
def exportsFunc (m : BModule) : Bool :=
  m.base.exports.any fun e => match e.index with
    | .func _ => true
    | _ => false

/-- **The ConstBranch stage**: the fold, kept when the validator accepts it. A module
that exports no function is left byte-identical: no engine can run it, so a rewritten
copy could not be checked against the original. -/
def constBranchChecked (m : BModule) : BModule :=
  if exportsFunc m && Exe.validOk (constBranch m) then constBranch m else m

end Silmaril.Wasm.Binaryen.ConstBranch
