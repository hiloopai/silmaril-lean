module

public import Silmaril.Wasm.V1.Types
public import Mathlib.Data.BitVec

/-!
# WebAssembly 1.0 instructions

Structured bodies are source instruction lists. Memory instructions and indirect
calls refer implicitly to memory and table zero. Later reference, vector, bulk
memory, multivalue-block, sign-extension and saturating-conversion instructions
have no constructors here. Operand typing and packed-width/alignment conditions
are separate validation judgments.
-/

@[expose] public section

namespace Silmaril.Wasm.V1

inductive Instr where
  | nop | unreachable | drop | select
  | block (type : BlockType) (body : List Instr)
  | loop (type : BlockType) (body : List Instr)
  | if_ (type : BlockType) (thenBody elseBody : List Instr)
  | br (label : LabelIdx)
  | brIf (label : LabelIdx)
  | brTable (labels : List LabelIdx) (default : LabelIdx)
  | call (function : FuncIdx)
  | callIndirect (type : TypeIdx)
  | return_
  | localGet (index : LocalIdx)
  | localSet (index : LocalIdx)
  | localTee (index : LocalIdx)
  | globalGet (global : GlobalIdx)
  | globalSet (global : GlobalIdx)
  | intLoad (type : IntType) (packed : Option (PackSize × Signedness)) (arg : MemArg)
  | floatLoad (type : FloatType) (arg : MemArg)
  | intStore (type : IntType) (packed : Option PackSize) (arg : MemArg)
  | floatStore (type : FloatType) (arg : MemArg)
  | memorySize | memoryGrow
  | intConst (type : IntType) (bits : BitVec type.width)
  | floatConst (type : FloatType) (bits : BitVec type.width)
  | intUnOp (type : IntType) (op : IntUnOp)
  | intBinOp (type : IntType) (op : IntBinOp)
  | intTestOp (type : IntType) (op : IntTestOp)
  | intRelOp (type : IntType) (op : IntRelOp)
  | floatUnOp (type : FloatType) (op : FloatUnOp)
  | floatBinOp (type : FloatType) (op : FloatBinOp)
  | floatRelOp (type : FloatType) (op : FloatRelOp)
  | convert (op : ConvertOp)
  deriving Repr

abbrev Expr := List Instr

/-- The source-level instruction bodies are exactly the structured-control forms. -/
def Instr.bodies : Instr → List Expr
  | .block _ body | .loop _ body => [body]
  | .if_ _ left right => [left, right]
  | _ => []

end Silmaril.Wasm.V1
