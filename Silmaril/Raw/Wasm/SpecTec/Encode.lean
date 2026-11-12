module

public import Silmaril.Wasm.Instructions
public import Silmaril.Raw.Wasm.SpecTec.EncodeOps
public import Silmaril.Raw.Wasm.SpecTec.FloatBits
public import Silmaril.Raw.Wasm.SpecTec.Generated

@[expose] public section

/-! # Instruction payloads and generated schema agreement

The encoder retains immediate values and structured children. Its theorem checks
constructor tags and ordered payload-family annotations against the official
schema. Annotations do not prove payload membership or dependent side conditions.
Floating-point constants decompose their IEEE bits into SpecTec's signed
magnitude constructors; this does not implement floating-point execution.
-/

namespace Silmaril.Wasm.SpecTec

def field (name : String) (value : Value) : Argument := ⟨.named name [], value⟩
def dependentField (name : String) (parameters : List Nat) (value : Value) : Argument :=
  ⟨.named name parameters, value⟩
def optionalField (name : String) (value : Value) : Argument :=
  ⟨.optional (.named name []), value⟩
def sequenceField (name : String) (values : List Value) : Argument :=
  ⟨.sequence (.named name []), list values⟩

/-- `$record` carries named fields rather than a source constructor tag. -/
def encodeMemArg (arg : MemArg) : Value :=
  node "$record" [node "ALIGN" [encodeUnsigned arg.align.val],
    node "OFFSET" [encodeUnsigned arg.offset.val]]

def encodeCatch : Catch → Value
  | .catch_ tag label => node "CATCH" [encodeUnsigned tag.toNat, encodeUnsigned label.toNat]
  | .catchRef tag label => node "CATCH_REF" [encodeUnsigned tag.toNat, encodeUnsigned label.toNat]
  | .catchAll label => node "CATCH_ALL" [encodeUnsigned label.toNat]
  | .catchAllRef label => node "CATCH_ALL_REF" [encodeUnsigned label.toNat]

def encodeLoadOp (op : PackSize × Signedness) : Value :=
  node "%_%" [encodePackSize op.1, encodeSignedness op.2]

def encodeStoreOp (size : PackSize) : Value := node "%" [encodePackSize size]

/-- The source grammar writes target type before source type for conversions. -/
def encodeInstruction : Instr → Constructor
  | .nop => ⟨"NOP", []⟩
  | .unreachable => ⟨"UNREACHABLE", []⟩
  | .drop => ⟨"DROP", []⟩
  | .select ts => ⟨"SELECT", [⟨.optional (.sequence (.named "valtype" [])),
      option (fun ts => list (ts.map encodeValType)) ts⟩]⟩
  | .block t body => ⟨"BLOCK", [field "blocktype" (encodeBlockType t),
      sequenceField "instr" (body.attach.map (fun i => (encodeInstruction i.val).toValue))]⟩
  | .loop t body => ⟨"LOOP", [field "blocktype" (encodeBlockType t),
      sequenceField "instr" (body.attach.map (fun i => (encodeInstruction i.val).toValue))]⟩
  | .if_ t yes no => ⟨"IF%%ELSE%", [field "blocktype" (encodeBlockType t),
      sequenceField "instr" (yes.attach.map (fun i => (encodeInstruction i.val).toValue)),
      sequenceField "instr" (no.attach.map (fun i => (encodeInstruction i.val).toValue))]⟩
  | .br i => ⟨"BR", [field "labelidx" (encodeUnsigned i.toNat)]⟩
  | .brIf i => ⟨"BR_IF", [field "labelidx" (encodeUnsigned i.toNat)]⟩
  | .brTable is d => ⟨"BR_TABLE", [sequenceField "labelidx" (is.map (fun i => encodeUnsigned i.toNat)),
      field "labelidx" (encodeUnsigned d.toNat)]⟩
  | .brOnNull i => ⟨"BR_ON_NULL", [field "labelidx" (encodeUnsigned i.toNat)]⟩
  | .brOnNonNull i => ⟨"BR_ON_NON_NULL", [field "labelidx" (encodeUnsigned i.toNat)]⟩
  | .brOnCast i s t => ⟨"BR_ON_CAST", [field "labelidx" (encodeUnsigned i.toNat),
      field "reftype" (encodeRefType s), field "reftype" (encodeRefType t)]⟩
  | .brOnCastFail i s t => ⟨"BR_ON_CAST_FAIL", [field "labelidx" (encodeUnsigned i.toNat),
      field "reftype" (encodeRefType s), field "reftype" (encodeRefType t)]⟩
  | .call i => ⟨"CALL", [field "funcidx" (encodeUnsigned i.toNat)]⟩
  | .callRef i => ⟨"CALL_REF", [field "typeuse" (encodeTypeUse i)]⟩
  | .callIndirect table t => ⟨"CALL_INDIRECT", [field "tableidx" (encodeUnsigned table.toNat),
      field "typeuse" (encodeTypeUse t)]⟩
  | .return_ => ⟨"RETURN", []⟩
  | .returnCall i => ⟨"RETURN_CALL", [field "funcidx" (encodeUnsigned i.toNat)]⟩
  | .returnCallRef i => ⟨"RETURN_CALL_REF", [field "typeuse" (encodeTypeUse i)]⟩
  | .returnCallIndirect table t => ⟨"RETURN_CALL_INDIRECT", [field "tableidx" (encodeUnsigned table.toNat),
      field "typeuse" (encodeTypeUse t)]⟩
  | .throw i => ⟨"THROW", [field "tagidx" (encodeUnsigned i.toNat)]⟩
  | .throwRef => ⟨"THROW_REF", []⟩
  | .tryTable t catches body => ⟨"TRY_TABLE", [field "blocktype" (encodeBlockType t),
      ⟨.namedList (.named "catch" []), namedList (catches.map encodeCatch)⟩,
      sequenceField "instr" (body.attach.map (fun i => (encodeInstruction i.val).toValue))]⟩
  | .localGet i => ⟨"LOCAL.GET", [field "localidx" (encodeUnsigned i.toNat)]⟩
  | .localSet i => ⟨"LOCAL.SET", [field "localidx" (encodeUnsigned i.toNat)]⟩
  | .localTee i => ⟨"LOCAL.TEE", [field "localidx" (encodeUnsigned i.toNat)]⟩
  | .globalGet i => ⟨"GLOBAL.GET", [field "globalidx" (encodeUnsigned i.toNat)]⟩
  | .globalSet i => ⟨"GLOBAL.SET", [field "globalidx" (encodeUnsigned i.toNat)]⟩
  | .tableGet i => ⟨"TABLE.GET", [field "tableidx" (encodeUnsigned i.toNat)]⟩
  | .tableSet i => ⟨"TABLE.SET", [field "tableidx" (encodeUnsigned i.toNat)]⟩
  | .tableSize i => ⟨"TABLE.SIZE", [field "tableidx" (encodeUnsigned i.toNat)]⟩
  | .tableGrow i => ⟨"TABLE.GROW", [field "tableidx" (encodeUnsigned i.toNat)]⟩
  | .tableFill i => ⟨"TABLE.FILL", [field "tableidx" (encodeUnsigned i.toNat)]⟩
  | .tableCopy d s => ⟨"TABLE.COPY", [field "tableidx" (encodeUnsigned d.toNat), field "tableidx" (encodeUnsigned s.toNat)]⟩
  | .tableInit t e => ⟨"TABLE.INIT", [field "tableidx" (encodeUnsigned t.toNat), field "elemidx" (encodeUnsigned e.toNat)]⟩
  | .elemDrop i => ⟨"ELEM.DROP", [field "elemidx" (encodeUnsigned i.toNat)]⟩
  | .intLoad t packed m a => ⟨"LOAD", [field "numtype" (encodeIntType t),
      ⟨.optional (.named "loadop_" [0]), option encodeLoadOp packed⟩,
      field "memidx" (encodeUnsigned m.toNat), field "memarg" (encodeMemArg a)]⟩
  | .floatLoad t m a => ⟨"LOAD", [field "numtype" (encodeFloatType t),
      ⟨.optional (.named "loadop_" [0]), node "$none" []⟩,
      field "memidx" (encodeUnsigned m.toNat), field "memarg" (encodeMemArg a)]⟩
  | .intStore t packed m a => ⟨"STORE", [field "numtype" (encodeIntType t),
      ⟨.optional (.named "storeop_" [0]), option encodeStoreOp packed⟩,
      field "memidx" (encodeUnsigned m.toNat), field "memarg" (encodeMemArg a)]⟩
  | .floatStore t m a => ⟨"STORE", [field "numtype" (encodeFloatType t),
      ⟨.optional (.named "storeop_" [0]), node "$none" []⟩,
      field "memidx" (encodeUnsigned m.toNat), field "memarg" (encodeMemArg a)]⟩
  | .vecLoad op m a => ⟨"VLOAD", [field "vectype" (encodeVecType .v128),
      ⟨.optional (.named "vloadop_" [0]), encodeVecLoadOp op⟩,
      field "memidx" (encodeUnsigned m.toNat), field "memarg" (encodeMemArg a)]⟩
  | .vecLoadLane size m a lane => ⟨"VLOAD_LANE", [field "vectype" (encodeVecType .v128),
      field "sz" (encodePackSize size), field "memidx" (encodeUnsigned m.toNat),
      field "memarg" (encodeMemArg a), field "laneidx" (encodeUnsigned lane.val)]⟩
  | .vecStore m a => ⟨"VSTORE", [field "vectype" (encodeVecType .v128),
      field "memidx" (encodeUnsigned m.toNat), field "memarg" (encodeMemArg a)]⟩
  | .vecStoreLane size m a lane => ⟨"VSTORE_LANE", [field "vectype" (encodeVecType .v128),
      field "sz" (encodePackSize size), field "memidx" (encodeUnsigned m.toNat),
      field "memarg" (encodeMemArg a), field "laneidx" (encodeUnsigned lane.val)]⟩
  | .memorySize i => ⟨"MEMORY.SIZE", [field "memidx" (encodeUnsigned i.toNat)]⟩
  | .memoryGrow i => ⟨"MEMORY.GROW", [field "memidx" (encodeUnsigned i.toNat)]⟩
  | .memoryFill i => ⟨"MEMORY.FILL", [field "memidx" (encodeUnsigned i.toNat)]⟩
  | .memoryCopy d s => ⟨"MEMORY.COPY", [field "memidx" (encodeUnsigned d.toNat), field "memidx" (encodeUnsigned s.toNat)]⟩
  | .memoryInit m d => ⟨"MEMORY.INIT", [field "memidx" (encodeUnsigned m.toNat), field "dataidx" (encodeUnsigned d.toNat)]⟩
  | .dataDrop i => ⟨"DATA.DROP", [field "dataidx" (encodeUnsigned i.toNat)]⟩
  | .refNull t => ⟨"REF.NULL", [field "heaptype" (encodeHeapType t)]⟩
  | .refIsNull => ⟨"REF.IS_NULL", []⟩
  | .refAsNonNull => ⟨"REF.AS_NON_NULL", []⟩
  | .refEq => ⟨"REF.EQ", []⟩
  | .refTest t => ⟨"REF.TEST", [field "reftype" (encodeRefType t)]⟩
  | .refCast t => ⟨"REF.CAST", [field "reftype" (encodeRefType t)]⟩
  | .refFunc i => ⟨"REF.FUNC", [field "funcidx" (encodeUnsigned i.toNat)]⟩
  | .refI31 => ⟨"REF.I31", []⟩
  | .i31Get s => ⟨"I31.GET", [field "sx" (encodeSignedness s)]⟩
  | .structNew i => ⟨"STRUCT.NEW", [field "typeidx" (encodeUnsigned i.toNat)]⟩
  | .structNewDefault i => ⟨"STRUCT.NEW_DEFAULT", [field "typeidx" (encodeUnsigned i.toNat)]⟩
  | .structGet s t f => ⟨"STRUCT.GET", [optionalField "sx" (option encodeSignedness s),
      field "typeidx" (encodeUnsigned t.toNat), field "fieldidx" (encodeUnsigned f.toNat)]⟩
  | .structSet t f => ⟨"STRUCT.SET", [field "typeidx" (encodeUnsigned t.toNat), field "fieldidx" (encodeUnsigned f.toNat)]⟩
  | .arrayNew i => ⟨"ARRAY.NEW", [field "typeidx" (encodeUnsigned i.toNat)]⟩
  | .arrayNewDefault i => ⟨"ARRAY.NEW_DEFAULT", [field "typeidx" (encodeUnsigned i.toNat)]⟩
  | .arrayNewFixed t n => ⟨"ARRAY.NEW_FIXED", [field "typeidx" (encodeUnsigned t.toNat), field "u32" (encodeUnsigned n.val)]⟩
  | .arrayNewData t d => ⟨"ARRAY.NEW_DATA", [field "typeidx" (encodeUnsigned t.toNat), field "dataidx" (encodeUnsigned d.toNat)]⟩
  | .arrayNewElem t e => ⟨"ARRAY.NEW_ELEM", [field "typeidx" (encodeUnsigned t.toNat), field "elemidx" (encodeUnsigned e.toNat)]⟩
  | .arrayGet s t => ⟨"ARRAY.GET", [optionalField "sx" (option encodeSignedness s),
      field "typeidx" (encodeUnsigned t.toNat)]⟩
  | .arraySet i => ⟨"ARRAY.SET", [field "typeidx" (encodeUnsigned i.toNat)]⟩
  | .arrayLen => ⟨"ARRAY.LEN", []⟩
  | .arrayFill i => ⟨"ARRAY.FILL", [field "typeidx" (encodeUnsigned i.toNat)]⟩
  | .arrayCopy d s => ⟨"ARRAY.COPY", [field "typeidx" (encodeUnsigned d.toNat), field "typeidx" (encodeUnsigned s.toNat)]⟩
  | .arrayInitData t d => ⟨"ARRAY.INIT_DATA", [field "typeidx" (encodeUnsigned t.toNat), field "dataidx" (encodeUnsigned d.toNat)]⟩
  | .arrayInitElem t e => ⟨"ARRAY.INIT_ELEM", [field "typeidx" (encodeUnsigned t.toNat), field "elemidx" (encodeUnsigned e.toNat)]⟩
  | .externConvertAny => ⟨"EXTERN.CONVERT_ANY", []⟩
  | .anyConvertExtern => ⟨"ANY.CONVERT_EXTERN", []⟩
  | .intConst t bits => ⟨"CONST", [field "numtype" (encodeIntType t),
      dependentField "num_" [0] (encodeUnsigned bits.toNat)]⟩
  | .floatConst t bits => ⟨"CONST", [field "numtype" (encodeFloatType t),
      dependentField "num_" [0] (floatBits t bits)]⟩
  | .intUnOp t op => ⟨"UNOP", [field "numtype" (encodeIntType t), dependentField "unop_" [0] (encodeIntUnOp op)]⟩
  | .floatUnOp t op => ⟨"UNOP", [field "numtype" (encodeFloatType t), dependentField "unop_" [0] (encodeFloatUnOp op)]⟩
  | .intBinOp t op => ⟨"BINOP", [field "numtype" (encodeIntType t), dependentField "binop_" [0] (encodeIntBinOp op)]⟩
  | .floatBinOp t op => ⟨"BINOP", [field "numtype" (encodeFloatType t), dependentField "binop_" [0] (encodeFloatBinOp op)]⟩
  | .intTestOp t op => ⟨"TESTOP", [field "numtype" (encodeIntType t), dependentField "testop_" [0] (encodeIntTestOp op)]⟩
  | .intRelOp t op => ⟨"RELOP", [field "numtype" (encodeIntType t), dependentField "relop_" [0] (encodeIntRelOp op)]⟩
  | .floatRelOp t op => ⟨"RELOP", [field "numtype" (encodeFloatType t), dependentField "relop_" [0] (encodeFloatRelOp op)]⟩
  | .convert op => ⟨"CVTOP", [field "numtype" (encodeNumType op.target),
      field "numtype" (encodeNumType op.source), dependentField "cvtop__" [1, 0] (encodeConvertOp op)]⟩
  | .vecConst bits => ⟨"VCONST", [field "vectype" (encodeVecType .v128), dependentField "vec_" [0] (encodeUnsigned bits.toNat)]⟩
  | .vecUnOp op => ⟨"VVUNOP", [field "vectype" (encodeVecType .v128), field "vvunop" (encodeVecUnOp op)]⟩
  | .vecBinOp op => ⟨"VVBINOP", [field "vectype" (encodeVecType .v128), field "vvbinop" (encodeVecBinOp op)]⟩
  | .vecTernOp op => ⟨"VVTERNOP", [field "vectype" (encodeVecType .v128), field "vvternop" (encodeVecTernOp op)]⟩
  | .vecTestOp op => ⟨"VVTESTOP", [field "vectype" (encodeVecType .v128), field "vvtestop" (encodeVecTestOp op)]⟩
  | .vecIntUnOp s op => ⟨"VUNOP", [field "shape" (encodeIntShape s), dependentField "vunop_" [0] (encodeVecIntUnOp op)]⟩
  | .vecFloatUnOp s op => ⟨"VUNOP", [field "shape" (encodeFloatShape s), dependentField "vunop_" [0] (encodeFloatUnOp op)]⟩
  | .vecIntBinOp s op => ⟨"VBINOP", [field "shape" (encodeIntShape s), dependentField "vbinop_" [0] (encodeVecIntBinOp op)]⟩
  | .vecFloatBinOp s op => ⟨"VBINOP", [field "shape" (encodeFloatShape s), dependentField "vbinop_" [0] (encodeVecFloatBinOp op)]⟩
  | .vecIntTernOp s op => ⟨"VTERNOP", [field "shape" (encodeIntShape s), dependentField "vternop_" [0] (encodeVecIntTernOp op)]⟩
  | .vecFloatTernOp s op => ⟨"VTERNOP", [field "shape" (encodeFloatShape s), dependentField "vternop_" [0] (encodeVecFloatTernOp op)]⟩
  | .vecAllTrue s => ⟨"VTESTOP", [field "shape" (encodeIntShape s), dependentField "vtestop_" [0] (node "ALL_TRUE" [])]⟩
  | .vecIntRelOp s op => ⟨"VRELOP", [field "shape" (encodeIntShape s), dependentField "vrelop_" [0] (encodeIntRelOp op)]⟩
  | .vecFloatRelOp s op => ⟨"VRELOP", [field "shape" (encodeFloatShape s), dependentField "vrelop_" [0] (encodeFloatRelOp op)]⟩
  | .vecShiftOp s op => ⟨"VSHIFTOP", [field "ishape" (encodeIShape s), dependentField "vshiftop_" [0] (encodeVecShiftOp op)]⟩
  | .vecBitmask s => ⟨"VBITMASK", [field "ishape" (encodeIShape s)]⟩
  | .vecSwizzle op => ⟨"VSWIZZLOP", [field "bshape" encodeBShape, dependentField "vswizzlop_" [0] (encodeVecSwizzleOp op)]⟩
  | .vecShuffle lanes => ⟨"VSHUFFLE", [field "bshape" encodeBShape, sequenceField "laneidx" (lanes.map (fun i => encodeUnsigned i.val))]⟩
  | .vecExtUnOp s t op => ⟨"VEXTUNOP", [field "ishape" (encodeIShape t), field "ishape" (encodeIShape s),
      dependentField "vextunop__" [1, 0] (encodeVecExtUnOp op)]⟩
  | .vecExtBinOp s t op => ⟨"VEXTBINOP", [field "ishape" (encodeIShape t), field "ishape" (encodeIShape s),
      dependentField "vextbinop__" [1, 0] (encodeVecExtBinOp op)]⟩
  | .vecExtTernOp s t op => ⟨"VEXTTERNOP", [field "ishape" (encodeIShape t), field "ishape" (encodeIShape s),
      dependentField "vextternop__" [1, 0] (encodeVecExtTernOp op)]⟩
  | .vecNarrow s t sign => ⟨"VNARROW", [field "ishape" (encodeIShape t), field "ishape" (encodeIShape s), field "sx" (encodeSignedness sign)]⟩
  | .vecConvert s t op => ⟨"VCVTOP", [field "shape" (encodeShape t), field "shape" (encodeShape s),
      dependentField "vcvtop__" [1, 0] (encodeVecConvertOp op)]⟩
  | .vecSplat s => ⟨"VSPLAT", [field "shape" (encodeShape s)]⟩
  | .vecExtractLane s sign lane => ⟨"VEXTRACT_LANE", [field "shape" (encodeShape s),
      optionalField "sx" (option encodeSignedness sign), field "laneidx" (encodeUnsigned lane.val)]⟩
  | .vecReplaceLane s lane => ⟨"VREPLACE_LANE", [field "shape" (encodeShape s), field "laneidx" (encodeUnsigned lane.val)]⟩
termination_by instruction => sizeOf instruction
decreasing_by
  all_goals simp_wf
  all_goals have h := List.sizeOf_lt_of_mem i.property
  all_goals omega

/-- Every encoded instruction has an official constructor tag and the same ordered
payload-family annotations. This does not validate the annotated payload values. -/
theorem encodeInstruction_hasShape (i : Instr) :
    ∃ s ∈ instructionSchemas, (encodeInstruction i).hasShape s := by
  cases i
  all_goals
    simp only [encodeInstruction, Constructor.hasShape, field, dependentField,
      optionalField, sequenceField, List.map_cons, List.map_nil]; decide

end Silmaril.Wasm.SpecTec
