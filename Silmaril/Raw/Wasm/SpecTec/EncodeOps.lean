module

public import Silmaril.Raw.Wasm.SpecTec.Basic
public import Silmaril.Wasm.Ops

@[expose] public section

/-! # Type and operator payloads for the SpecTec structural view

Tags are the elaborated SpecTec constructor names, including mixfix tags and
single-`%` wrappers. Encoding preserves payload structure; it does not discharge
SpecTec side conditions or claim execution correspondence.
-/

namespace Silmaril.Wasm.SpecTecEnc

/-- SpecTec's named, length-bounded `list(X)` wraps its underlying sequence. -/
def namedList (xs : List Value) : Value := node "%" [list xs]

/-- Bounded unsigned integers use the elaborated `%` constructor around a natural
number. Integer/vector values and all indices alias this representation. -/
def encodeUnsigned (n : Nat) : Value := node "%" [nat n]

def encodeFlag (tag : String) (present : Bool) : Value :=
  option (fun _ : Unit => node tag []) (if present then some () else none)

def encodeIntType : IntType → Value
  | .i32 => node "I32" [] | .i64 => node "I64" []

def encodeFloatType : FloatType → Value
  | .f32 => node "F32" [] | .f64 => node "F64" []

def encodeNumType : NumType → Value
  | .int t => encodeIntType t | .float t => encodeFloatType t

def encodeVecType : VecType → Value
  | .v128 => node "V128" []

def encodeAbsHeapType : AbsHeapType → Value
  | .any => node "ANY" [] | .eq => node "EQ" []
  | .i31 => node "I31" [] | .struct => node "STRUCT" []
  | .array => node "ARRAY" [] | .none => node "NONE" []
  | .func => node "FUNC" [] | .nofunc => node "NOFUNC" []
  | .exn => node "EXN" [] | .noexn => node "NOEXN" []
  | .extern => node "EXTERN" [] | .noextern => node "NOEXTERN" []

/-- A source type use adds `_IDX` around the bounded-integer index representation. -/
def encodeTypeUse (i : TypeIdx) : Value := node "_IDX" [encodeUnsigned i.toNat]

def encodeHeapType : HeapType → Value
  | .abstract t => encodeAbsHeapType t | .typeIdx i => encodeTypeUse i

def encodeRefType (t : RefType) : Value :=
  node "REF" [encodeFlag "NULL" t.nullable, encodeHeapType t.heap]

def encodeValType : ValType → Value
  | .num t => encodeNumType t | .vec t => encodeVecType t | .ref t => encodeRefType t

def encodePackType : PackType → Value
  | .i8 => node "I8" [] | .i16 => node "I16" []

def encodeStorageType : StorageType → Value
  | .val t => encodeValType t | .packed t => encodePackType t

/-- Mutability is represented by an optional `MUT`, not a Boolean payload. -/
def encodeMutability : Mutability → Value
  | .const => encodeFlag "MUT" false
  | .var => encodeFlag "MUT" true

def encodeFieldType (t : Silmaril.Wasm.FieldType) : Value :=
  node "%%" [encodeMutability t.mutability, encodeStorageType t.storage]

def encodeResultType (ts : ResultType) : Value := namedList (ts.map encodeValType)

def encodeFuncType (t : FuncType) : Value :=
  node "FUNC%->%" [encodeResultType t.params, encodeResultType t.results]

def encodeCompositeType : CompositeType → Value
  | .func t => encodeFuncType t
  | .struct fields => node "STRUCT" [namedList (fields.map encodeFieldType)]
  | .array field => node "ARRAY" [encodeFieldType field]

def encodeSubType (t : SubType) : Value :=
  node "SUB" [encodeFlag "FINAL" t.final_, list (t.supertypes.map encodeTypeUse),
    encodeCompositeType t.body]

def encodeRecType (t : RecType) : Value := node "REC" [namedList (t.types.map encodeSubType)]

def encodeBlockType : BlockType → Value
  | .empty => node "_RESULT" [option encodeValType none]
  | .value t => node "_RESULT" [option encodeValType (some t)]
  | .typeIdx i => encodeTypeUse i

def encodeAddrType (t : AddrType) : Value := encodeIntType t.intType

def encodeLimits (t : Limits) : Value :=
  node "[%..%]" [encodeUnsigned t.min.val, option (fun n => encodeUnsigned n.val) t.max]

def encodeMemoryType (t : MemoryType) : Value :=
  node "%%PAGE" [encodeAddrType t.address, encodeLimits t.limits]

def encodeTableType (t : TableType) : Value :=
  node "%%%" [encodeAddrType t.address, encodeLimits t.limits, encodeRefType t.element]

def encodeGlobalType (t : GlobalType) : Value :=
  node "%%" [encodeMutability t.mutability, encodeValType t.value]

def encodeExternType : ExternType → Value
  | .tag t => node "TAG" [encodeTypeUse t]
  | .global t => node "GLOBAL" [encodeGlobalType t]
  | .memory t => node "MEM" [encodeMemoryType t]
  | .table t => node "TABLE" [encodeTableType t]
  | .func t => node "FUNC" [encodeTypeUse t]

def encodeSignedness : Signedness → Value
  | .signed => node "S" [] | .unsigned => node "U" []

def encodePackSize (size : PackSize) : Value := node "%" [nat size.width]

def encodeIntUnOp : IntUnOp → Value
  | .clz => node "CLZ" [] | .ctz => node "CTZ" [] | .popcnt => node "POPCNT" []
  | .extend size => node "EXTEND" [encodePackSize size]

def encodeIntBinOp : IntBinOp → Value
  | .add => node "ADD" [] | .sub => node "SUB" [] | .mul => node "MUL" []
  | .div s => node "DIV" [encodeSignedness s]
  | .rem s => node "REM" [encodeSignedness s]
  | .and => node "AND" [] | .or => node "OR" [] | .xor => node "XOR" []
  | .shl => node "SHL" [] | .shr s => node "SHR" [encodeSignedness s]
  | .rotl => node "ROTL" [] | .rotr => node "ROTR" []

def encodeIntTestOp : IntTestOp → Value
  | .eqz => node "EQZ" []

def encodeIntRelOp : IntRelOp → Value
  | .eq => node "EQ" [] | .ne => node "NE" []
  | .lt s => node "LT" [encodeSignedness s] | .gt s => node "GT" [encodeSignedness s]
  | .le s => node "LE" [encodeSignedness s] | .ge s => node "GE" [encodeSignedness s]

def encodeFloatUnOp : FloatUnOp → Value
  | .abs => node "ABS" [] | .neg => node "NEG" [] | .sqrt => node "SQRT" []
  | .ceil => node "CEIL" [] | .floor => node "FLOOR" []
  | .trunc => node "TRUNC" [] | .nearest => node "NEAREST" []

def encodeFloatBinOp : FloatBinOp → Value
  | .add => node "ADD" [] | .sub => node "SUB" [] | .mul => node "MUL" []
  | .div => node "DIV" [] | .min => node "MIN" [] | .max => node "MAX" []
  | .copysign => node "COPYSIGN" []

def encodeFloatRelOp : FloatRelOp → Value
  | .eq => node "EQ" [] | .ne => node "NE" []
  | .lt => node "LT" [] | .gt => node "GT" [] | .le => node "LE" [] | .ge => node "GE" []

/-- The instruction encoder supplies the separately encoded target and source types. -/
def encodeConvertOp : ConvertOp → Value
  | .wrap => node "WRAP" []
  | .extend s => node "EXTEND" [encodeSignedness s]
  | .trunc _ _ s => node "TRUNC" [encodeSignedness s]
  | .truncSat _ _ s => node "TRUNC_SAT" [encodeSignedness s]
  | .convert _ _ s => node "CONVERT" [encodeSignedness s]
  | .demote => node "DEMOTE" [] | .promote => node "PROMOTE" []
  | .reinterpretInt _ | .reinterpretFloat _ => node "REINTERPRET" []

def encodeIntLaneType : IntShape → Value
  | .i8x16 => node "I8" [] | .i16x8 => node "I16" []
  | .i32x4 => node "I32" [] | .i64x2 => node "I64" []

def encodeIntShape (s : IntShape) : Value :=
  node "%X%" [encodeIntLaneType s, node "%" [nat s.lanes]]

def encodeFloatShape (s : FloatShape) : Value :=
  node "%X%" [encodeFloatType (match s with | .f32x4 => .f32 | .f64x2 => .f64),
    node "%" [nat s.lanes]]

def encodeShape : Shape → Value
  | .int s => encodeIntShape s | .float s => encodeFloatShape s

/-- `ishape` and `bshape` are restricted-shape wrappers in the elaborated AST. -/
def encodeIShape (s : IntShape) : Value := node "%" [encodeIntShape s]

def encodeBShape : Value := node "%" [encodeIntShape .i8x16]

def encodeHalf : Half → Value
  | .low => node "LOW" [] | .high => node "HIGH" []

def encodeVecUnOp : VecUnOp → Value
  | .not => node "NOT" []

def encodeVecBinOp : VecBinOp → Value
  | .and => node "AND" [] | .andnot => node "ANDNOT" []
  | .or => node "OR" [] | .xor => node "XOR" []

def encodeVecTernOp : VecTernOp → Value
  | .bitselect => node "BITSELECT" []

def encodeVecTestOp : VecTestOp → Value
  | .anyTrue => node "ANY_TRUE" []

def encodeVecIntUnOp : VecIntUnOp → Value
  | .abs => node "ABS" [] | .neg => node "NEG" [] | .popcnt => node "POPCNT" []

def encodeVecIntBinOp : VecIntBinOp → Value
  | .add => node "ADD" [] | .sub => node "SUB" [] | .mul => node "MUL" []
  | .addSat s => node "ADD_SAT" [encodeSignedness s]
  | .subSat s => node "SUB_SAT" [encodeSignedness s]
  | .avgrU => node "AVGRU" [] | .q15mulrSatS => node "Q15MULR_SATS" []
  | .relaxedQ15mulrS => node "RELAXED_Q15MULRS" []
  | .min s => node "MIN" [encodeSignedness s] | .max s => node "MAX" [encodeSignedness s]

def encodeVecFloatBinOp : VecFloatBinOp → Value
  | .add => node "ADD" [] | .sub => node "SUB" [] | .mul => node "MUL" []
  | .div => node "DIV" [] | .min => node "MIN" [] | .max => node "MAX" []
  | .pmin => node "PMIN" [] | .pmax => node "PMAX" []
  | .relaxedMin => node "RELAXED_MIN" [] | .relaxedMax => node "RELAXED_MAX" []

def encodeVecIntTernOp : VecIntTernOp → Value
  | .relaxedLaneSelect => node "RELAXED_LANESELECT" []

def encodeVecFloatTernOp : VecFloatTernOp → Value
  | .relaxedMadd => node "RELAXED_MADD" [] | .relaxedNmadd => node "RELAXED_NMADD" []

def encodeVecShiftOp : VecShiftOp → Value
  | .shl => node "SHL" [] | .shr s => node "SHR" [encodeSignedness s]

def encodeVecSwizzleOp : VecSwizzleOp → Value
  | .swizzle => node "SWIZZLE" [] | .relaxedSwizzle => node "RELAXED_SWIZZLE" []

def encodeVecExtUnOp : VecExtUnOp → Value
  | .extaddPairwise s => node "EXTADD_PAIRWISE" [encodeSignedness s]

def encodeVecExtBinOp : VecExtBinOp → Value
  | .extmul h s => node "EXTMUL" [encodeHalf h, encodeSignedness s]
  | .dotS => node "DOTS" [] | .relaxedDotS => node "RELAXED_DOTS" []

def encodeVecExtTernOp : VecExtTernOp → Value
  | .relaxedDotAddS => node "RELAXED_DOT_ADDS" []

def encodeVecConvertOp : VecConvertOp → Value
  | .extend h s => node "EXTEND" [encodeHalf h, encodeSignedness s]
  | .convert h s => node "CONVERT" [option encodeHalf h, encodeSignedness s]
  | .truncSat s zero => node "TRUNC_SAT" [encodeSignedness s, encodeFlag "ZERO" zero]
  | .relaxedTrunc s zero => node "RELAXED_TRUNC" [encodeSignedness s, encodeFlag "ZERO" zero]
  | .demoteZero => node "DEMOTE" [node "ZERO" []]
  | .promoteLow => node "PROMOTELOW" []

/-- Includes the optional wrapper: a full-width vector load has no load-op annotation. -/
def encodeVecLoadOp : VecLoadOp → Value
  | .full => node "$none" []
  | .extend8x8 s => node "$some" [node "SHAPE%X%_%"
      [encodePackSize .i8, node "%" [nat 8], encodeSignedness s]]
  | .extend16x4 s => node "$some" [node "SHAPE%X%_%"
      [encodePackSize .i16, node "%" [nat 4], encodeSignedness s]]
  | .extend32x2 s => node "$some" [node "SHAPE%X%_%"
      [encodePackSize .i32, node "%" [nat 2], encodeSignedness s]]
  | .splat size => node "$some" [node "SPLAT" [encodePackSize size]]
  | .zero32 => node "$some" [node "ZERO" [encodePackSize .i32]]
  | .zero64 => node "$some" [node "ZERO" [encodePackSize .i64]]

end Silmaril.Wasm.SpecTecEnc
