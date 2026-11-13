module

public import Silmaril.Compiler.Core.SignedArithmetic.Main.Defs
public import Silmaril.Compiler.Native.Correctness.AdditionLower.Defs
/-! Expected native syntax of the existing recursive typed-Ail arithmetic
family. Actual Lower.expr/compile equations and real open invocation semantics
are separate proved obligations, without supplying successful compilation. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.ArithmeticLower
open Silmaril.Compile Silmaril.Machine Silmaril.Cerberus
open Silmaril.Compiler.Core.SignedArithmetic
open Silmaril.Compiler.Native Silmaril.Compiler.Native.Optimize

/-- The actual existing signed arithmetic operation selected by Lower.arith. -/
def operation : Operator → Lir.Binop
  | .add => .add
  | .sub => .sub
  | .mul => .mul

/-- Word arithmetic before the actual signed-width normalization. -/
def rawWord (operator : Operator) (left right : Int) : Lir.Word :=
  match operator with
  | .add => BitVec.ofInt 64 left + BitVec.ofInt 64 right
  | .sub => BitVec.ofInt 64 left - BitVec.ofInt 64 right
  | .mul => BitVec.ofInt 64 left * BitVec.ofInt 64 right

structure ExpressionPlan where
  instructions : List Mir.Instr
  result : Nat
  nextReg : Nat

/-- Actual native lowering allocates children left-to-right, then two operand
normalizations, the arithmetic instruction and result normalization. -/
def plan : Expression → Nat → ExpressionPlan
  | .literal number, next =>
      ⟨[.op (.const next (BitVec.ofInt 64 number)), .op (.unary .sext32 (next + 1) next)], next + 1, next + 2⟩
  | .binary operator left right, next =>
      let first := plan left next
      let last := plan right first.nextReg
      ⟨first.instructions ++ last.instructions ++
        [.op (.unary .sext32 last.nextReg first.result),
          .op (.unary .sext32 (last.nextReg + 1) last.result),
          .op (.binary (operation operator) (last.nextReg + 2) last.nextReg (last.nextReg + 1)),
          .op (.unary .sext32 (last.nextReg + 3) (last.nextReg + 2))],
        last.nextReg + 3, last.nextReg + 4⟩

/-- The expression updates only its actual instruction buffer and allocator. -/
def ExpressionPlan.write (output : ExpressionPlan) (state : Lower.FState) : Lower.FState :=
  {state with instrs := state.instrs ++ output.instructions.toArray, nextReg := output.nextReg}

def body (expression : Expression) : Mir.Block :=
  let output := plan expression 2
  ⟨output.instructions.toArray.push (.op (.unary .sext32 output.nextReg output.result)),
    .ret [.reg output.nextReg]⟩

def function (expression : Expression) : Mir.Func :=
  {name := "main", params := [], results := 1,
    blocks := #[AdditionLower.prologue, body expression, AdditionLower.fallback]}

def unit (expression : Expression) : Mir.Unit := {funcs := #[function expression]}

def artifact (expression : Expression) : Artifact :=
  {mir := unit expression, functions := #[{
    name := "main", signature := ⟨.int 4 true, [], false, true⟩,
    tags := ∅, frameBytes := 0, frameAlign := 16}], calls := #[]}

/-- Exact register writes of the selected straight-line instructions. This is
an expected post-state; successful actual execution is proved separately. -/
def frame (expression : Expression) (next : Nat) (initial : Lir.Frame Nat) : Lir.Frame Nat :=
  match expression with
  | .literal number =>
      (initial.set next (BitVec.ofInt 64 number)).set (next + 1)
        (AdditionLower.normalize (BitVec.ofInt 64 number))
  | .binary operator left right =>
      let first := plan left next
      let last := plan right first.nextReg
      let state := frame right first.nextReg (frame left next initial)
      let state := state.set last.nextReg (BitVec.ofInt 64 left.value)
      let state := state.set (last.nextReg + 1) (BitVec.ofInt 64 right.value)
      let raw := rawWord operator left.value right.value
      (state.set (last.nextReg + 2) raw).set (last.nextReg + 3) (AdditionLower.normalize raw)

def bodyFrame (expression : Expression) (initial : Lir.Frame Nat) : Lir.Frame Nat :=
  (frame expression 2 initial).set (plan expression 2).nextReg (BitVec.ofInt 64 expression.value)

end Silmaril.Compiler.Native.Correctness.ArithmeticLower
