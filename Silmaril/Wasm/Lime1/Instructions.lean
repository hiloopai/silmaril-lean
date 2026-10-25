module

public import Silmaril.Wasm.Lime1.Types
public import Mathlib.Data.BitVec

/-! # Lime1 instructions

The profile adds multi-value block signatures, integer sign extension,
saturating float-to-integer conversion, and memory copy/fill to WebAssembly 1.0.
Memory and table operands remain implicit zero; there are no reference-value,
SIMD, passive-segment, table-manipulation, exception, or tail-call instructions.
Width and alignment constraints remain validation judgments.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1

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
  | memorySize | memoryGrow | memoryFill | memoryCopy
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

end Silmaril.Wasm.Lime1
