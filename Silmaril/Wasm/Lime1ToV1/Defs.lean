module

public import Silmaril.Wasm.Lime1.FromV1

/-!
# The checked projection from Lime1 into Wasm 1.0 syntax: definitions

silmaril-lean has the injection `V1.Instr.toLime` of Wasm 1.0 syntax into Lime1. This is its
partial inverse: `instrToV1?` and `exprToV1?` return the Wasm 1.0 instruction a Lime1
instruction came from, and `none` on the Lime1 extensions (bulk memory, sign extension,
saturating truncation, indexed block types), also inside structured bodies. It is a syntactic
profile check, not validation. The theorems are in `Silmaril.Wasm.Lime1ToV1.Thms`.

Ported from an earlier development `Silmaril/Wasm/Lime1/ToV1.lean`, with the functions
renamed into `Silmaril.Wasm.Lime1ToV1` (`Lime1.Instr.toV1?` there is `instrToV1?` here, and so
on).
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1ToV1

open Silmaril.Wasm

/-- The Wasm 1.0 block type of a Lime1 block type: indexed block types have none. -/
def blockTypeToV1? : Lime1.BlockType → Option V1.BlockType
  | .empty => some none
  | .value t => some (some t)
  | .typeIdx _ => none

/-- The Wasm 1.0 unary integer operator: sign extension has none. -/
def intUnOpToV1? : Lime1.IntUnOp → Option V1.IntUnOp
  | .clz => some .clz
  | .ctz => some .ctz
  | .popcnt => some .popcnt
  | .extend _ => none

/-- The Wasm 1.0 conversion: saturating truncation has none. -/
def convertOpToV1? : ConvertOp → Option V1.ConvertOp
  | .wrap => some .wrap
  | .extend s => some (.extend s)
  | .trunc s t sign => some (.trunc s t sign)
  | .truncSat .. => none
  | .convert s t sign => some (.convert s t sign)
  | .demote => some .demote
  | .promote => some .promote
  | .reinterpretInt t => some (.reinterpretInt t)
  | .reinterpretFloat t => some (.reinterpretFloat t)

mutual

/-- The Wasm 1.0 instruction a Lime1 instruction came from, if any. -/
def instrToV1? : Lime1.Instr → Option V1.Instr
  | .nop => some .nop
  | .unreachable => some .unreachable
  | .drop => some .drop
  | .select => some .select
  | .block t body => do return .block (← blockTypeToV1? t) (← exprToV1? body)
  | .loop t body => do return .loop (← blockTypeToV1? t) (← exprToV1? body)
  | .if_ t left right =>
    do return .if_ (← blockTypeToV1? t) (← exprToV1? left) (← exprToV1? right)
  | .br l => some (.br l)
  | .brIf l => some (.brIf l)
  | .brTable ls l => some (.brTable ls l)
  | .call f => some (.call f)
  | .callIndirect t => some (.callIndirect t)
  | .return_ => some .return_
  | .localGet i => some (.localGet i)
  | .localSet i => some (.localSet i)
  | .localTee i => some (.localTee i)
  | .globalGet i => some (.globalGet i)
  | .globalSet i => some (.globalSet i)
  | .intLoad t p a => some (.intLoad t p a)
  | .floatLoad t a => some (.floatLoad t a)
  | .intStore t p a => some (.intStore t p a)
  | .floatStore t a => some (.floatStore t a)
  | .memorySize => some .memorySize
  | .memoryGrow => some .memoryGrow
  | .memoryCopy | .memoryFill => none
  | .intConst t x => some (.intConst t x)
  | .floatConst t x => some (.floatConst t x)
  | .intUnOp t op => do return .intUnOp t (← intUnOpToV1? op)
  | .intBinOp t op => some (.intBinOp t op)
  | .intTestOp t op => some (.intTestOp t op)
  | .intRelOp t op => some (.intRelOp t op)
  | .floatUnOp t op => some (.floatUnOp t op)
  | .floatBinOp t op => some (.floatBinOp t op)
  | .floatRelOp t op => some (.floatRelOp t op)
  | .convert op => do return .convert (← convertOpToV1? op)

/-- The Wasm 1.0 expression a Lime1 expression came from, if any. -/
def exprToV1? : Lime1.Expr → Option V1.Expr
  | [] => some []
  | i :: es => do return (← instrToV1? i) :: (← exprToV1? es)

end

end Silmaril.Wasm.Lime1ToV1
