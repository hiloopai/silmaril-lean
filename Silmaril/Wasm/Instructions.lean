module

public import Silmaril.Wasm.Ops
public import Mathlib.Data.BitVec

@[expose] public section

/-! # WebAssembly Core 3.0 source instructions

The datatype covers the source instruction families, including GC, exceptions,
tail calls, memory64, SIMD, and relaxed SIMD. Constants retain their bits;
floating-point execution must separately account for the permitted NaN results.
Administrative execution instructions are deliberately a separate future layer.

See the [instruction grammar](https://webassembly.github.io/spec/core/syntax/instructions.html)
and its [pinned SpecTec source](https://github.com/WebAssembly/spec/blob/608711107b7f1edb13efd57b7d79b49477462d36/specification/wasm-3.0/1.3-syntax.instructions.spectec).
-/

namespace Silmaril.Wasm

/-- Alignment is an exponent; the offset is unsigned and permits memory64. -/
structure MemArg where
  align : Fin (2 ^ 32)
  offset : Fin (2 ^ 64)
  deriving DecidableEq, Repr

/-- The source and binary grammar use a byte; the selected shape bounds the lane. -/
abbrev LaneIdx := Fin (2 ^ 8)

inductive Catch where
  | catch_ (tag : TagIdx) (label : LabelIdx)
  | catchRef (tag : TagIdx) (label : LabelIdx)
  | catchAll (label : LabelIdx)
  | catchAllRef (label : LabelIdx)
  deriving DecidableEq, Repr

/-- Raw source syntax. Context-dependent validity is not a constructor premise. -/
inductive Instr where
  | nop | unreachable | drop
  | select (types : Option (List ValType))
  | block (type : BlockType) (body : List Instr)
  | loop (type : BlockType) (body : List Instr)
  | if_ (type : BlockType) (thenBody elseBody : List Instr)
  | br (label : LabelIdx)
  | brIf (label : LabelIdx)
  | brTable (labels : List LabelIdx) (default : LabelIdx)
  | brOnNull (label : LabelIdx)
  | brOnNonNull (label : LabelIdx)
  | brOnCast (label : LabelIdx) (source target : RefType)
  | brOnCastFail (label : LabelIdx) (source target : RefType)
  | call (function : FuncIdx)
  | callRef (type : TypeIdx)
  | callIndirect (table : TableIdx) (type : TypeIdx)
  | return_
  | returnCall (function : FuncIdx)
  | returnCallRef (type : TypeIdx)
  | returnCallIndirect (table : TableIdx) (type : TypeIdx)
  | throw (tag : TagIdx)
  | throwRef
  | tryTable (type : BlockType) (catches : List Catch) (body : List Instr)
  | localGet (index : LocalIdx)
  | localSet (index : LocalIdx)
  | localTee (index : LocalIdx)
  | globalGet (global : GlobalIdx)
  | globalSet (global : GlobalIdx)
  | tableGet (table : TableIdx)
  | tableSet (table : TableIdx)
  | tableSize (table : TableIdx)
  | tableGrow (table : TableIdx)
  | tableFill (table : TableIdx)
  | tableCopy (destination source : TableIdx)
  | tableInit (table : TableIdx) (element : ElemIdx)
  | elemDrop (element : ElemIdx)
  | intLoad (type : IntType) (packed : Option (PackSize × Signedness))
      (memory : MemIdx) (arg : MemArg)
  | floatLoad (type : FloatType) (memory : MemIdx) (arg : MemArg)
  | intStore (type : IntType) (packed : Option PackSize) (memory : MemIdx) (arg : MemArg)
  | floatStore (type : FloatType) (memory : MemIdx) (arg : MemArg)
  | vecLoad (op : VecLoadOp) (memory : MemIdx) (arg : MemArg)
  | vecLoadLane (size : PackSize) (memory : MemIdx) (arg : MemArg) (lane : LaneIdx)
  | vecStore (memory : MemIdx) (arg : MemArg)
  | vecStoreLane (size : PackSize) (memory : MemIdx) (arg : MemArg) (lane : LaneIdx)
  | memorySize (memory : MemIdx)
  | memoryGrow (memory : MemIdx)
  | memoryFill (memory : MemIdx)
  | memoryCopy (destination source : MemIdx)
  | memoryInit (memory : MemIdx) (data : DataIdx)
  | dataDrop (data : DataIdx)
  | refNull (heap : HeapType)
  | refIsNull | refAsNonNull | refEq
  | refTest (type : RefType)
  | refCast (type : RefType)
  | refFunc (function : FuncIdx)
  | refI31
  | i31Get (sign : Signedness)
  | structNew (type : TypeIdx)
  | structNewDefault (type : TypeIdx)
  | structGet (sign : Option Signedness) (type : TypeIdx) (field : FieldIdx)
  | structSet (type : TypeIdx) (field : FieldIdx)
  | arrayNew (type : TypeIdx)
  | arrayNewDefault (type : TypeIdx)
  | arrayNewFixed (type : TypeIdx) (length : Fin (2 ^ 32))
  | arrayNewData (type : TypeIdx) (data : DataIdx)
  | arrayNewElem (type : TypeIdx) (element : ElemIdx)
  | arrayGet (sign : Option Signedness) (type : TypeIdx)
  | arraySet (type : TypeIdx)
  | arrayLen
  | arrayFill (type : TypeIdx)
  | arrayCopy (destination source : TypeIdx)
  | arrayInitData (type : TypeIdx) (data : DataIdx)
  | arrayInitElem (type : TypeIdx) (element : ElemIdx)
  | externConvertAny | anyConvertExtern
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
  | vecConst (bits : BitVec 128)
  | vecUnOp (op : VecUnOp)
  | vecBinOp (op : VecBinOp)
  | vecTernOp (op : VecTernOp)
  | vecTestOp (op : VecTestOp)
  | vecIntUnOp (shape : IntShape) (op : VecIntUnOp)
  | vecFloatUnOp (shape : FloatShape) (op : FloatUnOp)
  | vecIntBinOp (shape : IntShape) (op : VecIntBinOp)
  | vecFloatBinOp (shape : FloatShape) (op : VecFloatBinOp)
  | vecIntTernOp (shape : IntShape) (op : VecIntTernOp)
  | vecFloatTernOp (shape : FloatShape) (op : VecFloatTernOp)
  | vecAllTrue (shape : IntShape)
  | vecIntRelOp (shape : IntShape) (op : IntRelOp)
  | vecFloatRelOp (shape : FloatShape) (op : FloatRelOp)
  | vecShiftOp (shape : IntShape) (op : VecShiftOp)
  | vecBitmask (shape : IntShape)
  | vecSwizzle (op : VecSwizzleOp)
  | vecShuffle (lanes : List LaneIdx)
  | vecExtUnOp (source target : IntShape) (op : VecExtUnOp)
  | vecExtBinOp (source target : IntShape) (op : VecExtBinOp)
  | vecExtTernOp (source target : IntShape) (op : VecExtTernOp)
  | vecNarrow (source target : IntShape) (sign : Signedness)
  | vecConvert (source target : Shape) (op : VecConvertOp)
  | vecSplat (shape : Shape)
  | vecExtractLane (shape : Shape) (sign : Option Signedness) (lane : LaneIdx)
  | vecReplaceLane (shape : Shape) (lane : LaneIdx)
  deriving Repr

abbrev Expr := List Instr

/-- Local shape and immediate checks only; this is not Wasm's typing judgment.
Index existence, stack typing, reference matching, alignments, and memory address
bounds need a validation context and are intentionally not asserted here. -/
def Instr.immediatesValid : Instr → Bool
  | .select (some types) => types.length == 1
  | .block _ body | .loop _ body | .tryTable _ _ body =>
      body.attach.all (fun i => immediatesValid i.val)
  | .if_ _ left right => left.attach.all (fun i => immediatesValid i.val) &&
      right.attach.all (fun i => immediatesValid i.val)
  | .intUnOp t op => op.valid t
  | .intLoad t (some (size, _)) _ _ | .intStore t (some size) _ _ => size.width < t.width
  | .vecLoadLane size _ _ lane | .vecStoreLane size _ _ lane => lane.val < 128 / size.width
  | .vecIntUnOp shape op => op.valid shape
  | .vecIntBinOp shape op => op.valid shape
  | .vecIntRelOp shape op => op.validShape shape
  | .vecShuffle lanes => lanes.length == 16 && lanes.all (fun lane => lane.val < 32)
  | .vecExtUnOp source target op => op.valid source target
  | .vecExtBinOp source target op => op.valid source target
  | .vecExtTernOp source target op => op.valid source target
  | .vecNarrow source target _ => source.laneWidth == 2 * target.laneWidth && source.laneWidth ≤ 32
  | .vecConvert source target op => op.valid source target
  | .vecExtractLane shape sign lane =>
      lane.val < shape.lanes && (sign.isSome == (shape.laneWidth < 32))
  | .vecReplaceLane shape lane => lane.val < shape.lanes
  | _ => true
termination_by instruction => sizeOf instruction
decreasing_by
  all_goals simp_wf
  all_goals have h := List.sizeOf_lt_of_mem i.property
  all_goals omega

/-- The source-level structured bodies occur only in these four instruction forms. -/
def Instr.bodies : Instr → List Expr
  | .block _ body | .loop _ body | .tryTable _ _ body => [body]
  | .if_ _ left right => [left, right]
  | _ => []

end Silmaril.Wasm
