module

public import Silmaril.Wasm.Models.Features.Defs
public import Silmaril.Wasm.Modules
public import Silmaril.Wasm.Validation.Modules

/-!
# Feature-restricted Core 3.0 syntax

Every restricted language is a subset of **Core 3.0 syntax**, so it embeds in Core 3.0 by
definition (as the `Silmaril.Wasm.Det` subsets do). All checks are Boolean (kernel-evaluable);
the `Prop` forms are `… = true`.

* `ValType.inFeatB S`, `RefType.inFeatB S`, `BlockType.inFeatB S`, `FuncType.inFeatB S`;
* `Instr.headB S i`: the capabilities the instruction itself (not its bodies) needs;
  `Instr.inFeatB`/`Instr.insInFeatB`: recursively through `block`, `loop`, `if` and
  `try_table` bodies; `Instr.InFeat S i`;
* `Module.inFeatB S m` (types, imports, globals, memories, tables, functions, element
  segments, start; constant expressions included) and `Module.InFeat S m`;
* `ValidIn S m := ModuleValid m ∧ m.InFeat S`.

## The capability table

* `control`: `nop`, `unreachable`, `drop`, `select`, blocks, branches, `return`, locals;
  every branching instruction (`br_on_null`, `br_on_cast`, …) also needs it, since it reduces
  to `br`;
* `intNum`/`floatNum`: the integer/float numeric instructions; a conversion needs the sides it
  touches (`trunc_sat` needs `satConv`, sign-extension operators `signExt`); every memory
  instruction needs `intNum` (its address operand, and the byte loads/stores bulk operations
  reduce to);
* `memory` and, for an index other than 0, `multiMemory`; `table` and, for an index other than
  0, `refTypes` (several tables arrived with reference types);
* `directCall`: `call`; `callIndirect`: `call_indirect`; `tailCall`: the `return_call*`;
  `typedFuncRef`: `call_ref`, `ref.as_non_null`, `br_on_null`, non-nullable and concrete
  reference types;
* `globals`: `global.get`; `mutGlobal`: `global.set` and mutable global declarations;
* `refTypes`: `ref.null`, `ref.is_null`, `ref.func`, `table.get/set/size/grow/fill`, typed
  `select`; `bulkMemory`: `table.copy/init`, `elem.drop`, `memory.init`, `data.drop`;
  `bulkMemoryOpt`: `memory.copy/fill`;
* `gcImm`: `ref.eq`, `ref.test`, `ref.cast`, `br_on_cast*`, `i31`, struct/array allocation
  and reads, `extern.convert_any`/`any.convert_extern`, the abstract GC heap types;
  `gcMut`: `struct.set`, `array.set/fill/copy/init_*`, mutable fields;
* `exn`: `throw`, `throw_ref`, `try_table`, tags, `exnref`;
* `simd`: vector instructions; `relaxedSimd`: the relaxed ones;
* `multiValue`: block types given by a type index and function types with several results;
  `extConst`: constant expressions other than a single constant, `ref.null`, `ref.func` or
  `global.get`; `memory64`: 64-bit memories and tables.

Wide arithmetic, custom page sizes and stack switching have no Core 3.0 syntax, so no Core
3.0 instruction needs them.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open Silmaril.Wasm FeatureSet

/-! ## Types -/

/-- An abstract heap type of `S`. -/
def AbsHeapType.inFeatB (S : FeatureSet) : AbsHeapType → Bool
  | .func | .extern => S.has .refTypes
  | .nofunc | .noextern | .any | .eq | .i31 | .struct | .array | .none => S.has .gcImm
  | .exn | .noexn => S.has .exn

/-- A heap type of `S`: a concrete one needs typed function references. -/
def HeapType.inFeatB (S : FeatureSet) : HeapType → Bool
  | .abstract t => AbsHeapType.inFeatB S t
  | .typeIdx _ => S.has .typedFuncRef

/-- A reference type of `S`: non-nullable ones need typed function references. -/
def RefType.inFeatB (S : FeatureSet) (rt : RefType) : Bool :=
  S.has .refTypes && HeapType.inFeatB S rt.heap && (rt.nullable || S.has .typedFuncRef)

/-- A value type of `S`. -/
def ValType.inFeatB (S : FeatureSet) : ValType → Bool
  | .num (.int _) => S.has .intNum
  | .num (.float _) => S.has .floatNum
  | .vec _ => S.has .simd
  | .ref rt => RefType.inFeatB S rt

/-- A block type of `S`: a type index needs multi-value. -/
def BlockType.inFeatB (S : FeatureSet) : BlockType → Bool
  | .empty => true
  | .value t => ValType.inFeatB S t
  | .typeIdx _ => S.has .multiValue

/-- A function type of `S`: several results need multi-value. -/
def FuncType.inFeatB (S : FeatureSet) (ft : FuncType) : Bool :=
  ft.params.all (ValType.inFeatB S) && ft.results.all (ValType.inFeatB S) &&
    (decide (ft.results.length ≤ 1) || S.has .multiValue)

/-- A storage type of `S`. -/
def StorageType.inFeatB (S : FeatureSet) : StorageType → Bool
  | .val t => ValType.inFeatB S t
  | .packed _ => true

/-- A field type of `S`: mutable fields need mutable GC. -/
def FieldType.inFeatB (S : FeatureSet) (ft : FieldType) : Bool :=
  StorageType.inFeatB S ft.storage && (ft.mutability == .const || S.has .gcMut)

/-- A sub type of `S`: structs, arrays and subtyping need GC. -/
def SubType.inFeatB (S : FeatureSet) (st : SubType) : Bool :=
  (st.supertypes.isEmpty || S.has .gcImm) &&
  match st.body with
  | .func ft => FuncType.inFeatB S ft
  | .struct fs => S.has .gcImm && fs.all (FieldType.inFeatB S)
  | .array f => S.has .gcImm && FieldType.inFeatB S f

/-- A recursion group of `S`: several types in a group need GC. -/
def RecType.inFeatB (S : FeatureSet) (rt : RecType) : Bool :=
  (decide (rt.types.length ≤ 1) || S.has .gcImm) && rt.types.all (SubType.inFeatB S)

/-! ## Instructions -/

/-- A memory index of `S`: memory, and multi-memory for an index other than 0. -/
def memIdxB (S : FeatureSet) (x : MemIdx) : Bool :=
  S.has .intNum && S.has .memory && (x.toNat == 0 || S.has .multiMemory)

/-- A table index of `S`: tables, and reference types for an index other than 0. -/
def tblIdxB (S : FeatureSet) (x : TableIdx) : Bool :=
  S.has .table && (x.toNat == 0 || S.has .refTypes)

/-- A conversion of `S`. -/
def ConvertOp.inFeatB (S : FeatureSet) : ConvertOp → Bool
  | .wrap | .extend _ => S.has .intNum
  | .trunc _ _ _ | .convert _ _ _ | .reinterpretInt _ | .reinterpretFloat _ =>
      S.has .intNum && S.has .floatNum
  | .truncSat _ _ _ => S.has .satConv
  | .demote | .promote => S.has .floatNum

/-- Is a vector operation relaxed? -/
def Instr.isRelaxed : Instr → Bool
  | .vecIntBinOp _ .relaxedQ15mulrS | .vecFloatBinOp _ .relaxedMin
  | .vecFloatBinOp _ .relaxedMax | .vecIntTernOp _ _ | .vecFloatTernOp _ _
  | .vecSwizzle .relaxedSwizzle | .vecExtBinOp _ _ .relaxedDotS | .vecExtTernOp _ _ _
  | .vecConvert _ _ (.relaxedTrunc _ _) => true
  | _ => false

/-- An integer unary operator of `S`: the sign-extension operators need `signExt`. -/
def IntUnOp.inFeatB (S : FeatureSet) : IntUnOp → Bool
  | .extend _ => S.has .signExt
  | _ => S.has .intNum

/-- A vector instruction of `S`: SIMD, and relaxed SIMD for the relaxed ones. -/
def vecB (S : FeatureSet) (i : Instr) : Bool :=
  S.has .simd && (!Instr.isRelaxed i || S.has .relaxedSimd)

/-- The capabilities an instruction itself needs (not those of its bodies). -/
def Instr.headB (S : FeatureSet) : Instr → Bool
  | .nop | .unreachable | .drop | .br _ | .brIf _ | .brTable _ _ | .return_
  | .localGet _ | .localSet _ | .localTee _ => S.has .control
  | .select none => S.has .control
  | .select (some ts) => S.has .control && S.has .refTypes && ts.all (ValType.inFeatB S)
  | .block bt _ | .loop bt _ | .if_ bt _ _ => S.has .control && BlockType.inFeatB S bt
  | .brOnNull _ | .brOnNonNull _ => S.has .control && S.has .typedFuncRef
  | .brOnCast _ r₁ r₂ | .brOnCastFail _ r₁ r₂ =>
      S.has .control && S.has .gcImm && RefType.inFeatB S r₁ && RefType.inFeatB S r₂
  | .call _ => S.has .directCall
  | .callRef _ => S.has .typedFuncRef
  | .callIndirect x _ => S.has .callIndirect && tblIdxB S x
  | .returnCall _ => S.has .tailCall
  | .returnCallRef _ => S.has .tailCall && S.has .typedFuncRef
  | .returnCallIndirect x _ => S.has .tailCall && S.has .callIndirect && tblIdxB S x
  | .throw _ | .throwRef => S.has .exn
  | .tryTable bt _ _ => S.has .exn && S.has .control && BlockType.inFeatB S bt
  | .globalGet _ => S.has .globals
  | .globalSet _ => S.has .mutGlobal
  | .tableGet x | .tableSet x | .tableSize x | .tableGrow x | .tableFill x =>
      S.has .refTypes && tblIdxB S x
  | .tableCopy x y => S.has .bulkMemory && tblIdxB S x && tblIdxB S y
  | .tableInit x _ => S.has .bulkMemory && tblIdxB S x
  | .elemDrop _ => S.has .bulkMemory
  | .intLoad _ _ x _ | .intStore _ _ x _ | .memorySize x | .memoryGrow x => memIdxB S x
  | .floatLoad _ x _ | .floatStore _ x _ => S.has .floatNum && memIdxB S x
  | .vecLoad _ x _ | .vecLoadLane _ x _ _ | .vecStore x _ | .vecStoreLane _ x _ _ =>
      S.has .simd && memIdxB S x
  | .memoryFill x => S.has .bulkMemoryOpt && memIdxB S x
  | .memoryCopy x y => S.has .bulkMemoryOpt && memIdxB S x && memIdxB S y
  | .memoryInit x _ => S.has .bulkMemory && memIdxB S x
  | .dataDrop _ => S.has .bulkMemory
  | .refNull ht => S.has .refTypes && HeapType.inFeatB S ht
  | .refIsNull | .refFunc _ => S.has .refTypes
  | .refAsNonNull => S.has .typedFuncRef
  | .refTest rt | .refCast rt => S.has .gcImm && RefType.inFeatB S rt
  | .refEq | .refI31 | .i31Get _ | .structNew _ | .structNewDefault _ | .structGet _ _ _
  | .arrayNew _ | .arrayNewDefault _ | .arrayNewFixed _ _ | .arrayNewData _ _
  | .arrayNewElem _ _ | .arrayGet _ _ | .arrayLen | .externConvertAny | .anyConvertExtern =>
      S.has .gcImm
  | .structSet _ _ | .arraySet _ | .arrayFill _ | .arrayCopy _ _ | .arrayInitData _ _
  | .arrayInitElem _ _ => S.has .gcMut
  | .intConst _ _ | .intBinOp _ _ | .intTestOp _ _ | .intRelOp _ _ => S.has .intNum
  | .intUnOp _ op => IntUnOp.inFeatB S op
  | .floatConst _ _ | .floatUnOp _ _ | .floatBinOp _ _ | .floatRelOp _ _ => S.has .floatNum
  | .convert op => ConvertOp.inFeatB S op
  | i => vecB S i

mutual
/-- An instruction of `S`, recursively through its bodies. -/
def Instr.inFeatB (S : FeatureSet) : Instr → Bool
  | .block bt b => Instr.headB S (.block bt []) && Instr.insInFeatB S b
  | .loop bt b => Instr.headB S (.loop bt []) && Instr.insInFeatB S b
  | .if_ bt b₁ b₂ =>
      Instr.headB S (.if_ bt [] []) && Instr.insInFeatB S b₁ && Instr.insInFeatB S b₂
  | .tryTable bt cs b => Instr.headB S (.tryTable bt cs []) && Instr.insInFeatB S b
  | i => Instr.headB S i

/-- A sequence of instructions of `S`. -/
def Instr.insInFeatB (S : FeatureSet) : List Instr → Bool
  | [] => true
  | i :: is => Instr.inFeatB S i && Instr.insInFeatB S is
end

/-- An instruction of `S`. -/
def Instr.InFeat (S : FeatureSet) (i : Instr) : Prop := Instr.inFeatB S i = true

instance (S : FeatureSet) (i : Instr) : Decidable (Instr.InFeat S i) :=
  inferInstanceAs (Decidable (_ = true))

/-- A value type of `S`. -/
def ValType.InFeat (S : FeatureSet) (t : ValType) : Prop := ValType.inFeatB S t = true

/-- A function type of `S`. -/
def FuncType.InFeat (S : FeatureSet) (t : FuncType) : Prop := FuncType.inFeatB S t = true

/-! ## Modules -/

/-- A constant expression of Wasm 1.0/2.0: empty, a single constant, `ref.null`, `ref.func` or
`global.get`. -/
def simpleConst : Expr → Bool
  | [.intConst _ _] | [.floatConst _ _] | [.vecConst _] | [.refNull _] | [.refFunc _]
  | [.globalGet _] | [] => true
  | _ => false

/-- A constant expression of `S`: anything but a single constant, `ref.null`, `ref.func` or
`global.get` needs extended constants. -/
def constExprB (S : FeatureSet) (e : Expr) : Bool :=
  Instr.insInFeatB S e && (simpleConst e || S.has .extConst)

/-- A global type of `S`. -/
def GlobalType.inFeatB (S : FeatureSet) (g : GlobalType) : Bool :=
  S.has .globals && ValType.inFeatB S g.value && (g.mutability == .const || S.has .mutGlobal)

/-- A memory type of `S`. -/
def MemoryType.inFeatB (S : FeatureSet) (m : MemoryType) : Bool :=
  S.has .memory && (m.address == .i32 || S.has .memory64)

/-- A table type of `S`. -/
def TableType.inFeatB (S : FeatureSet) (t : TableType) : Bool :=
  S.has .table && (t.address == .i32 || S.has .memory64) &&
    (t.element == ⟨true, .abstract .func⟩ || RefType.inFeatB S t.element)

/-- An external type of `S`. -/
def ExternType.inFeatB (S : FeatureSet) : ExternType → Bool
  | .tag _ => S.has .exn
  | .global g => GlobalType.inFeatB S g
  | .memory m => MemoryType.inFeatB S m
  | .table t => TableType.inFeatB S t
  | .func _ => true

/-- A global of `S`. -/
def Global.inFeatB (S : FeatureSet) (g : Global) : Bool :=
  GlobalType.inFeatB S g.type && constExprB S g.init

/-- A table of `S`. -/
def Table.inFeatB (S : FeatureSet) (t : Table) : Bool :=
  TableType.inFeatB S t.type && constExprB S t.init

/-- A function of `S`: locals and body. -/
def Func.inFeatB (S : FeatureSet) (f : Func) : Bool :=
  f.locals.all (ValType.inFeatB S) && Instr.insInFeatB S f.body

/-- An element segment mode of `S`: passive and declarative segments need bulk memory. -/
def ElemMode.inFeatB (S : FeatureSet) : ElemMode → Bool
  | .active _ off => constExprB S off
  | _ => S.has .bulkMemory

/-- An element segment of `S`. -/
def Elem.inFeatB (S : FeatureSet) (e : Elem) : Bool :=
  (e.type == ⟨true, .abstract .func⟩ || RefType.inFeatB S e.type) &&
    e.init.all (constExprB S) && ElemMode.inFeatB S e.mode

/-- A data segment mode of `S`: passive segments need bulk memory. -/
def DataMode.inFeatB (S : FeatureSet) : DataMode → Bool
  | .active x off => memIdxB S x && constExprB S off
  | .passive => S.has .bulkMemory

/-- A data segment of `S`. -/
def Data.inFeatB (S : FeatureSet) (d : Data) : Bool := DataMode.inFeatB S d.mode

/-- Is an import a memory (a table)? -/
def Import.isMemory (i : Import) : Bool := match i.type with | .memory _ => true | _ => false
def Import.isTable (i : Import) : Bool := match i.type with | .table _ => true | _ => false

/-- A module of `S`: its types, imports, tags, globals, memories, tables, functions (locals and
bodies), element and data segments, and the number of its memories (several need
multi-memory) and tables (several need reference types). -/
def Module.inFeatB (S : FeatureSet) (m : Module) : Bool :=
  m.types.all (RecType.inFeatB S) &&
  m.imports.all (fun i => ExternType.inFeatB S i.type) &&
  (m.tags.isEmpty || S.has .exn) &&
  m.globals.all (Global.inFeatB S) &&
  m.memories.all (MemoryType.inFeatB S) &&
  m.tables.all (Table.inFeatB S) &&
  m.funcs.all (Func.inFeatB S) &&
  m.elems.all (Elem.inFeatB S) &&
  m.data.all (Data.inFeatB S) &&
  (decide (m.memories.length + (m.imports.filter Import.isMemory).length ≤ 1) ||
    S.has .multiMemory) &&
  (decide (m.tables.length + (m.imports.filter Import.isTable).length ≤ 1) ||
    S.has .refTypes)

/-- A module of `S`. -/
def Module.InFeat (S : FeatureSet) (m : Module) : Prop := Module.inFeatB S m = true

instance (S : FeatureSet) (m : Module) : Decidable (Module.InFeat S m) :=
  inferInstanceAs (Decidable (_ = true))

/-- A **valid module of `S`**: Core 3.0 valid, and in `S`. -/
def ValidIn (S : FeatureSet) (m : Module) : Prop :=
  Silmaril.Wasm.Validation.ModuleValid m ∧ Module.InFeat S m

end Silmaril.Wasm.Models
