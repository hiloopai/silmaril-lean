module

public import Silmaril.Wasm.V2.Ops
public import Mathlib.Data.BitVec

/-!
# WebAssembly 2.0 instructions

Transcribed from `specification/wasm-2.0/1-syntax.spectec`, section
`Instructions` (`1-syntax:396-531`), at WebAssembly/spec revision
`608711107b7f1edb13efd57b7d79b49477462d36`.

SpecTec writes `CONST numtype num_(numtype)`, `UNOP numtype unop_(numtype)` and
so on, where the payload type depends on the number type. We split each such
constructor into an integer and a floating-point form, as the 1.0 and Core 3.0
layers do; this is a representation choice and changes no program.

The syntactic side conditions written as `-- if …` on the SpecTec productions
are collected in `Instr.immediatesValid`. Three of its conjuncts have no such
side condition behind them and are ours; all three are documented in
`Silmaril.Wasm.V2.Validation`:

* `vecCvtOp`. `1-syntax:470-472` says `;; TODO: missing constraints` and
  `Instr_ok/vcvtop` (`6-typing:365`) is correspondingly unconditional, so a
  literal reading types `VCVTOP (I8 X 16) (F64 X 2) (EXTEND LOW S)`, for which
  no `Step_pure/vcvtop-*` rule applies — progress fails. We impose exactly the
  combinations the reduction rules define (deviation 3, filed as instruction-immediate side-condition deviation).
* `cvtOp`'s definedness premise `(op.toShared target source).isSome`.
  `1-syntax:437-438` carries only `-- if numtype_1 =/= numtype_2`, and `cvtop`
  (`1-syntax:305-313`) is a flat operator set, so a literal reading types
  `CVTOP I32 F64 PROMOTE`, for which there is no `$cvtop__` equation and no
  `Step_pure/cvtop-*` rule — progress fails again (deviation 16).
* `intUnOp`'s bound on `EXTEND n`, i.e. `IntUnOp.valid`'s `size.width <
  t.width`. `1-syntax:283` is `syntax unop_(Inn) = CLZ | CTZ | POPCNT |
  EXTEND n` with `n` an unconstrained `nat`, and `Instr_ok/unop`
  (`6-typing:267-268`) is premise-free (second table of `Silmaril.Wasm.V2.Validation`).

`vecShuffle` is *not* among them: the length condition `lanes.length = 16` is
verbatim the second conjunct of the side condition of `1-syntax:457`, and the
first conjunct, which pins the shape to `I8 X 16`, is absorbed by the
constructor carrying no shape at all. What `immediatesValid` does leave out is
the lane bound `i < 2*$dim(sh)`, which SpecTec states as a *typing* premise of
`Instr_ok/vshuffle` (`6-typing:340-342`) rather than as syntax; it stays a
typing premise here too.

**Omitted.** `1-syntax:439` declares `EXTEND numtype n` as an instruction in
addition to `UNOP numtype (EXTEND n)`. It has no typing rule in `6-typing`, no
reduction rule in `8-reduction` and no production in `A-binary`, so it is dead
syntax; we do not transcribe it. See `Silmaril.Wasm.V2.Validation`.
-/

@[expose] public section

namespace Silmaril.Wasm.V2

/-- `laneidx = u8` (`1-syntax:102`). -/
abbrev LaneIdx := Fin (2 ^ 8)

/-- `blocktype ::= _RESULT valtype? | _IDX typeidx` (`1-syntax:400`). -/
inductive BlockType where
  | result (type : Option ValType)
  | typeIdx (index : TypeIdx)
  deriving DecidableEq, Repr

/-- `instr` (`1-syntax:406-522`). -/
inductive Instr where
  -- Parametric instructions (`1-syntax:406`).
  | nop
  | unreachable
  | drop
  | select (types : Option (List ValType))
  -- Block instructions (`1-syntax:413`).
  | block (type : BlockType) (body : List Instr)
  | loop (type : BlockType) (body : List Instr)
  | if_ (type : BlockType) (thenBody elseBody : List Instr)
  -- Branch instructions (`1-syntax:419`).
  | br (label : LabelIdx)
  | brIf (label : LabelIdx)
  | brTable (labels : List LabelIdx) (default : LabelIdx)
  -- Call instructions (`1-syntax:425`).
  | call (function : FuncIdx)
  | callIndirect (table : TableIdx) (type : TypeIdx)
  | return_
  -- Numeric instructions (`1-syntax:431`).
  | intConst (type : IntType) (bits : BitVec type.width)
  | floatConst (type : FloatType) (bits : BitVec type.width)
  | intUnOp (type : IntType) (op : IntUnOp)
  | floatUnOp (type : FloatType) (op : FloatUnOp)
  | intBinOp (type : IntType) (op : IntBinOp)
  | floatBinOp (type : FloatType) (op : FloatBinOp)
  | intTestOp (type : IntType) (op : IntTestOp)
  | intRelOp (type : IntType) (op : IntRelOp)
  | floatRelOp (type : FloatType) (op : FloatRelOp)
  | cvtOp (target source : NumType) (op : CvtOp)
  -- Vector instructions (`1-syntax:442`).
  | vecConst (bits : BitVec 128)
  | vvUnOp (op : VecUnOp)
  | vvBinOp (op : VecBinOp)
  | vvTernOp (op : VecTernOp)
  | vvTestOp (op : VecTestOp)
  | vecIntUnOp (shape : IntShape) (op : VecIntUnOp)
  | vecFloatUnOp (shape : FloatShape) (op : FloatUnOp)
  | vecIntBinOp (shape : IntShape) (op : V2.VecIntBinOp)
  | vecFloatBinOp (shape : FloatShape) (op : V2.VecFloatBinOp)
  | vecAllTrue (shape : IntShape)
  | vecIntRelOp (shape : IntShape) (op : IntRelOp)
  | vecFloatRelOp (shape : FloatShape) (op : FloatRelOp)
  | vecShiftOp (shape : IntShape) (op : VecShiftOp)
  | vecBitmask (shape : IntShape)
  | vecSwizzle
  | vecShuffle (lanes : List LaneIdx)
  | vecSplat (shape : Shape)
  | vecExtractLane (shape : Shape) (sign : Option Signedness) (lane : LaneIdx)
  | vecReplaceLane (shape : Shape) (lane : LaneIdx)
  | vecExtUnOp (target source : IntShape) (op : VecExtUnOp)
  | vecExtBinOp (target source : IntShape) (op : V2.VecExtBinOp)
  | vecNarrow (target source : IntShape) (sign : Signedness)
  | vecCvtOp (target source : Shape) (op : VecCvtOp)
  -- Reference instructions (`1-syntax:475`).
  | refNull (type : RefType)
  | refFunc (function : FuncIdx)
  | refIsNull
  -- Local instructions (`1-syntax:481`).
  | localGet (index : LocalIdx)
  | localSet (index : LocalIdx)
  | localTee (index : LocalIdx)
  -- Global instructions (`1-syntax:487`).
  | globalGet (global : GlobalIdx)
  | globalSet (global : GlobalIdx)
  -- Table instructions (`1-syntax:492`).
  | tableGet (table : TableIdx)
  | tableSet (table : TableIdx)
  | tableSize (table : TableIdx)
  | tableGrow (table : TableIdx)
  | tableFill (table : TableIdx)
  | tableCopy (destination source : TableIdx)
  | tableInit (table : TableIdx) (element : ElemIdx)
  -- Element instructions (`1-syntax:502`).
  | elemDrop (element : ElemIdx)
  -- Memory instructions (`1-syntax:506`).
  | intLoad (type : IntType) (packed : Option (PackSize × Signedness)) (arg : MemArg)
  | floatLoad (type : FloatType) (arg : MemArg)
  | intStore (type : IntType) (packed : Option PackSize) (arg : MemArg)
  | floatStore (type : FloatType) (arg : MemArg)
  | vecLoad (op : Option VecLoadOp) (arg : MemArg)
  | vecLoadLane (size : PackSize) (arg : MemArg) (lane : LaneIdx)
  | vecStore (arg : MemArg)
  | vecStoreLane (size : PackSize) (arg : MemArg) (lane : LaneIdx)
  | memorySize
  | memoryGrow
  | memoryFill
  | memoryCopy
  | memoryInit (data : DataIdx)
  -- Data instructions (`1-syntax:521`).
  | dataDrop (data : DataIdx)
  deriving Repr

/-- `expr ::= instr*` (`1-syntax:525`). -/
abbrev Expr := List Instr

namespace Instr

/-- The nested expressions of a structured instruction. -/
def bodies : Instr → List Expr
  | .block _ body | .loop _ body => [body]
  | .if_ _ left right => [left, right]
  | _ => []

/-- The syntactic side conditions of the `syntax instr/…` productions
(`1-syntax:406-522`) and of the operator families (`1-syntax:277-393`). See the
module documentation for the three additions. -/
def immediatesValid : Instr → Bool
  | .block _ body | .loop _ body => body.attach.all fun i => immediatesValid i.val
  | .if_ _ left right =>
      (left.attach.all fun i => immediatesValid i.val) &&
        (right.attach.all fun i => immediatesValid i.val)
  | .intUnOp t op => op.valid t
  | .cvtOp target source op => target != source && (op.toShared target source).isSome
  | .vecIntUnOp s op => op.valid s
  | .vecIntBinOp s op => op.valid s
  | .vecIntRelOp s op => op.validShape s
  | .vecShuffle lanes => lanes.length == 16
  | .vecExtractLane s sign _ => sign.isSome == (s.laneWidth < 32)
  | .vecExtUnOp target source op => VecExtUnOp.valid2 target source op
  | .vecExtBinOp target source op => op.valid target source
  | .vecNarrow target source _ => source.laneWidth == 2 * target.laneWidth && source.laneWidth ≤ 32
  | .vecCvtOp target source op => op.valid target source
  | .intLoad t (some (size, _)) _ => size.width < t.width
  | .intStore t (some size) _ => size.width < t.width
  | _ => true
  termination_by instruction => sizeOf instruction
  decreasing_by
    all_goals exact Nat.lt_trans (List.sizeOf_lt_of_mem i.property) (by simp; omega)

end Instr

end Silmaril.Wasm.V2
