module

public import Silmaril.Machine.RTL.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Thms

/-!
# λRTL over `Lir` operators (operator-level connection)

An instruction alphabet and a λRTL model built from the **actual** `Lir` operator semantics
(`Silmaril.Machine.Lir.Unop.eval`, `Silmaril.Machine.Lir.Binop.eval`, 64-bit `Lir.Word`), so that
λRTL programs, their flat CFGs (`Silmaril.SSA.LambdaRTL.CFG`) and the validator run on `Lir`
arithmetic:

* `LirOp`: `const w`, `unary u`, `binary b` (operands passed as a pair `(x, y)`), and `test`,
  which turns a word into `ιₗ ()` when nonzero and `ιᵣ ()` when zero — the branch condition of
  `Lir.Term.branch c ifNonzero ifZero`.
* `LVal`: tree-shaped values (`word w`, `unit`, `pair`, `inl`, `inr`); the monad is `Option`
  (`none` for partial division/remainder and for ill-shaped operands, aborts and eliminations).

Scope: operators only. Memory, calls, stack slots, floating point, and the lowering of flat
CFGs to `Lir.Func` blocks are not covered here (see `docs/projects/ssa.md`).
-/

@[expose] public section

namespace Silmaril.Machine.LambdaRTLLir

open Silmaril.SSA.LambdaRTL

/-- Instructions: `Lir` constants, unary and binary operators, and the branch test. -/
inductive LirOp
  | const (w : Lir.Word)
  | unary (u : Lir.Unop)
  | binary (b : Lir.Binop)
  | test
  deriving DecidableEq

/-- Tree-shaped values over 64-bit words. -/
inductive LVal
  | word (w : Lir.Word)
  | unit
  | pair (a b : LVal)
  | inl (a : LVal)
  | inr (a : LVal)
  deriving DecidableEq

/-- Instruction semantics, from `Lir.Unop.eval` and `Lir.Binop.eval`. -/
def app : LirOp → LVal → Option LVal
  | .const w, _ => some (.word w)
  | .unary u, .word x => some (.word (u.eval x))
  | .binary b, .pair (.word x) (.word y) => (b.eval x y).map .word
  | .test, .word x => some (if x ≠ 0 then .inl .unit else .inr .unit)
  | _, _ => none

/-- The λRTL model of `Lir` operators in `Option`. -/
def model : Model LirOp Option LVal where
  unit := .unit
  pair := .pair
  inl := .inl
  inr := .inr
  unpair
    | .pair a b => some (a, b)
    | _ => none
  split
    | .inl a => some (.inl a)
    | .inr b => some (.inr b)
    | _ => none
  app := app
  abort _ := none

end Silmaril.Machine.LambdaRTLLir
