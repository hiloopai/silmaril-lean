module

public import Silmaril.Wasm.SpecTec.Sim.Defs
public import Silmaril.Wasm.V2.Execution.Step

/-!
# SpecTec 2.0 ↔ silmaril-lean V2: the encoding of configurations

`Sim20.configV hn c` is the SpecTec wasm-2.0 IL value of a V2 configuration `c`
(`Silmaril.Wasm.V2.Execution.Config H`), written against the IL types of
`Scripts.Wasm20.fixed` (`config = state; admininstr*`, `state = store; frame`, the six-field
`store`, the two-field `frame`, …). It is the 2.0 counterpart of the Core 3.0 encoding
`Sim.configV` (`Silmaril.Wasm.SpecTec.Sim.Defs`), and reuses its float encoding `Sim.floatV`
(the wasm-2.0 `fN`/`fNmag` are the wasm-3.0 ones).

How 2.0 differs from 3.0, as the encoding sees it:

* administrative instructions are a separate IL type `admininstr ⊇ instr`, with `REF.FUNC_ADDR`,
  `REF.HOST_ADDR`, `CALL_ADDR`, `LABEL_`, `FRAME_`, `TRAP` (`adminToV`);
* `valtype` is flat (`I32 … V128 FUNCREF EXTERNREF`) and `reftype` is `FUNCREF | EXTERNREF`;
* `resulttype = list(valtype)` is wrapped, `%(valtype*)`;
* frames hold plain values, not `val?`; the store has six fields and function instances hold a
  `functype` and a `func`;
* `UNOP (EXTEND n)` carries a bare `nat` and `CVTOP nt_1 nt_2 cvtop` a flat `cvtop`;
* no memory index on `LOAD`/`STORE`/`MEMORY.*`, no address type.

**Host functions.** wasm-2.0 has none (`Basic.lean` of V2, deviation 3). A host function
instance is encoded with `CODE = _HOSTFUNC (hn h)`, which is not a value of the 2.0 type
`func`; a configuration whose store holds one is therefore not typed (`Typed20`), and the
rule-level theorems, which assume typing, say nothing about it. With `H = Empty` this is
vacuous.

The encoding is checked against the IL types by `Sim20.Encode.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)

/-! ## Types -/

/-- `numtype`. -/
def numTypeV : NumType → Value
  | .int .i32 => caseNilV "I32"
  | .int .i64 => caseNilV "I64"
  | .float .f32 => caseNilV "F32"
  | .float .f64 => caseNilV "F64"

/-- `reftype = FUNCREF | EXTERNREF`. -/
def refTypeV : V2.RefType → Value
  | .funcref => caseNilV "FUNCREF"
  | .externref => caseNilV "EXTERNREF"

/-- `valtype`, the flat 2.0 enumeration. -/
def valTypeV : V2.ValType → Value
  | .num t => numTypeV t
  | .vec .v128 => caseNilV "V128"
  | .ref t => refTypeV t

/-- `resulttype = list(valtype)`, i.e. `%(valtype*)`. -/
def resultTypeV (ts : List V2.ValType) : Value := .case "%" (.tuple [.list (ts.map valTypeV)])

/-- `functype = resulttype -> resulttype`. -/
def funcTypeV (ft : V2.FuncType) : Value :=
  .case "%->%" (.tuple [resultTypeV ft.params, resultTypeV ft.results])

/-- `limits = [u32 .. u32?]`. -/
def limitsV (l : V2.Limits) : Value :=
  .case "[%..%]" (.tuple [pctV l.min.val, .opt (l.max.map fun m => pctV m.val)])

/-- `mut = MUT?`. -/
def mutV : Mutability → Value
  | .var => .opt (some (caseNilV "MUT"))
  | .const => .opt none

/-- `globaltype = mut valtype`. -/
def globalTypeV (g : V2.GlobalType) : Value :=
  .case "%%" (.tuple [mutV g.mutability, valTypeV g.value])

/-- `tabletype = limits reftype`. -/
def tableTypeV (t : V2.TableType) : Value :=
  .case "%%" (.tuple [limitsV t.limits, refTypeV t.element])

/-- `memtype = limits PAGE`. -/
def memTypeV (m : V2.MemoryType) : Value := .case "%PAGE" (limitsV m.limits)

/-- An index `idx = u32 = uN(32)`, i.e. `%(i)`. -/
def idxV {k : IndexKind} (x : Idx k) : Value := pctV x.toNat

/-- `blocktype = _RESULT valtype? | _IDX typeidx`. -/
def blockTypeV : V2.BlockType → Value
  | .result t => .case "_RESULT" (.opt (t.map valTypeV))
  | .typeIdx x => .case "_IDX" (idxV x)

/-! ## Values -/

/-- `num_(nt)`: `%(i)` for an integer, SpecTec's `fN` for a float. -/
def numV : NumVal → Value
  | ⟨.int _, b⟩ => pctV b.toNat
  | ⟨.float t, b⟩ => Sim.floatV t b

/-- `ref = REF.NULL reftype | REF.FUNC_ADDR funcaddr | REF.HOST_ADDR hostaddr`. -/
def refV : Ref → Value
  | .null t => .case "REF.NULL" (refTypeV t)
  | .funcAddr a => .case "REF.FUNC_ADDR" (.num (.natN a))
  | .hostAddr a => .case "REF.HOST_ADDR" (.num (.natN a))

/-- `val = CONST numtype num_(numtype) | VCONST vectype vec_(vectype) | ref`. -/
def valV : Val → Value
  | .num n => .case "CONST" (.tuple [numTypeV n.type, numV n])
  | .vec b => .case "VCONST" (.tuple [caseNilV "V128", pctV b.toNat])
  | .ref r => refV r

/-! ## Operators -/

/-- `sx = U | S`. -/
def sxV : Signedness → Value
  | .unsigned => caseNilV "U"
  | .signed => caseNilV "S"

/-- `unop_(Inn) = CLZ | CTZ | POPCNT | EXTEND n` (2.0: `n` is a bare `nat`). -/
def intUnOpV : IntUnOp → Value
  | .clz => caseNilV "CLZ"
  | .ctz => caseNilV "CTZ"
  | .popcnt => caseNilV "POPCNT"
  | .extend sz => .case "EXTEND" (.num (.natN sz.width))

/-- `unop_(Fnn)`. -/
def floatUnOpV : FloatUnOp → Value
  | .abs => caseNilV "ABS"
  | .neg => caseNilV "NEG"
  | .sqrt => caseNilV "SQRT"
  | .ceil => caseNilV "CEIL"
  | .floor => caseNilV "FLOOR"
  | .trunc => caseNilV "TRUNC"
  | .nearest => caseNilV "NEAREST"

/-- `binop_(Inn)`. -/
def intBinOpV : IntBinOp → Value
  | .add => caseNilV "ADD"
  | .sub => caseNilV "SUB"
  | .mul => caseNilV "MUL"
  | .div s => .case "DIV" (sxV s)
  | .rem s => .case "REM" (sxV s)
  | .and => caseNilV "AND"
  | .or => caseNilV "OR"
  | .xor => caseNilV "XOR"
  | .shl => caseNilV "SHL"
  | .shr s => .case "SHR" (sxV s)
  | .rotl => caseNilV "ROTL"
  | .rotr => caseNilV "ROTR"

/-- `binop_(Fnn)`. -/
def floatBinOpV : FloatBinOp → Value
  | .add => caseNilV "ADD"
  | .sub => caseNilV "SUB"
  | .mul => caseNilV "MUL"
  | .div => caseNilV "DIV"
  | .min => caseNilV "MIN"
  | .max => caseNilV "MAX"
  | .copysign => caseNilV "COPYSIGN"

/-- `testop_(Inn) = EQZ`. -/
def intTestOpV : IntTestOp → Value
  | .eqz => caseNilV "EQZ"

/-- `relop_(Inn)`. -/
def intRelOpV : IntRelOp → Value
  | .eq => caseNilV "EQ"
  | .ne => caseNilV "NE"
  | .lt s => .case "LT" (sxV s)
  | .gt s => .case "GT" (sxV s)
  | .le s => .case "LE" (sxV s)
  | .ge s => .case "GE" (sxV s)

/-- `relop_(Fnn)`. -/
def floatRelOpV : FloatRelOp → Value
  | .eq => caseNilV "EQ"
  | .ne => caseNilV "NE"
  | .lt => caseNilV "LT"
  | .gt => caseNilV "GT"
  | .le => caseNilV "LE"
  | .ge => caseNilV "GE"

/-- `cvtop`, the flat 2.0 conversion operator. -/
def cvtOpV : V2.CvtOp → Value
  | .extend s => .case "EXTEND" (sxV s)
  | .wrap => caseNilV "WRAP"
  | .convert s => .case "CONVERT" (sxV s)
  | .trunc s => .case "TRUNC" (sxV s)
  | .truncSat s => .case "TRUNC_SAT" (sxV s)
  | .promote => caseNilV "PROMOTE"
  | .demote => caseNilV "DEMOTE"
  | .reinterpret => caseNilV "REINTERPRET"

/-! ## Vector operators -/

/-- `dim = %(i)`. -/
def dimV (n : Nat) : Value := pctV n

/-- The lane type of an integer shape, as `Jnn`. -/
def jnnV : IntShape → Value
  | .i8x16 => caseNilV "I8"
  | .i16x8 => caseNilV "I16"
  | .i32x4 => caseNilV "I32"
  | .i64x2 => caseNilV "I64"

/-- The lane type of a float shape, as `Fnn`. -/
def fnnV : FloatShape → Value
  | .f32x4 => caseNilV "F32"
  | .f64x2 => caseNilV "F64"

/-- `ishape = Jnn X dim`. -/
def ishapeV (s : IntShape) : Value := .case "%X%" (.tuple [jnnV s, dimV s.lanes])

/-- `shape = lanetype X dim`. -/
def shapeV : Shape → Value
  | .int s => ishapeV s
  | .float s => .case "%X%" (.tuple [fnnV s, dimV s.lanes])

/-- `half = LOW | HIGH`. -/
def halfV : Half → Value
  | .low => caseNilV "LOW"
  | .high => caseNilV "HIGH"

/-- `vunop_(Jnn X M)`. -/
def vecIntUnOpV : VecIntUnOp → Value
  | .abs => caseNilV "ABS"
  | .neg => caseNilV "NEG"
  | .popcnt => caseNilV "POPCNT"

/-- `vbinop_(Jnn X M)`. -/
def vecIntBinOpV : V2.VecIntBinOp → Value
  | .add => caseNilV "ADD"
  | .sub => caseNilV "SUB"
  | .mul => caseNilV "MUL"
  | .addSat s => .case "ADD_SAT" (sxV s)
  | .subSat s => .case "SUB_SAT" (sxV s)
  | .avgrU => caseNilV "AVGRU"
  | .q15mulrSatS => caseNilV "Q15MULR_SATS"
  | .min s => .case "MIN" (sxV s)
  | .max s => .case "MAX" (sxV s)

/-- `vbinop_(Fnn X M)`. -/
def vecFloatBinOpV : V2.VecFloatBinOp → Value
  | .add => caseNilV "ADD"
  | .sub => caseNilV "SUB"
  | .mul => caseNilV "MUL"
  | .div => caseNilV "DIV"
  | .min => caseNilV "MIN"
  | .max => caseNilV "MAX"
  | .pmin => caseNilV "PMIN"
  | .pmax => caseNilV "PMAX"

/-- `vrelop_(Jnn X M)`: the signed comparisons carry a one-field tuple. -/
def vecIntRelOpV : IntRelOp → Value
  | .eq => caseNilV "EQ"
  | .ne => caseNilV "NE"
  | .lt s => .case "LT" (.tuple [sxV s])
  | .gt s => .case "GT" (.tuple [sxV s])
  | .le s => .case "LE" (.tuple [sxV s])
  | .ge s => .case "GE" (.tuple [sxV s])

/-- `vshiftop_(Jnn X M) = SHL | SHR sx`. -/
def vecShiftOpV : VecShiftOp → Value
  | .shl => caseNilV "SHL"
  | .shr s => .case "SHR" (sxV s)

/-- `vextunop_ = EXTADD_PAIRWISE sx`. -/
def vecExtUnOpV : VecExtUnOp → Value
  | .extaddPairwise s => .case "EXTADD_PAIRWISE" (sxV s)

/-- `vextbinop_ = EXTMUL half sx | DOTS`. -/
def vecExtBinOpV : V2.VecExtBinOp → Value
  | .extmul h s => .case "EXTMUL" (.tuple [halfV h, sxV s])
  | .dotS => caseNilV "DOTS"

/-- `vcvtop`. -/
def vecCvtOpV : V2.VecCvtOp → Value
  | .extend h s => .case "EXTEND" (.tuple [halfV h, sxV s])
  | .truncSat s z => .case "TRUNC_SAT" (.tuple [sxV s, .opt (if z then some (caseNilV "ZERO") else none)])
  | .convert h s => .case "CONVERT" (.tuple [.opt (h.map halfV), sxV s])
  | .demoteZero => .case "DEMOTE" (caseNilV "ZERO")
  | .promoteLow => caseNilV "PROMOTELOW"

/-- `vloadop`. -/
def vecLoadOpV : V2.VecLoadOp → Value
  | .shape8x8 s => .case "SHAPE%X%_%" (.tuple [.num (.natN 8), .num (.natN 8), sxV s])
  | .shape16x4 s => .case "SHAPE%X%_%" (.tuple [.num (.natN 16), .num (.natN 4), sxV s])
  | .shape32x2 s => .case "SHAPE%X%_%" (.tuple [.num (.natN 32), .num (.natN 2), sxV s])
  | .splat sz => .case "SPLAT" (.num (.natN sz.width))
  | .zero32 => .case "ZERO" (.num (.natN 32))
  | .zero64 => .case "ZERO" (.num (.natN 64))

/-- `memarg = {ALIGN u32, OFFSET u32}`. -/
def memargV (a : V2.MemArg) : Value :=
  .struct [("ALIGN", pctV a.align.val), ("OFFSET", pctV a.offset.val)]

/-- `sz = %(i)`. -/
def szV (p : PackSize) : Value := pctV p.width

/-! ## Instructions -/

mutual
/-- A V2 instruction as a value of the wasm-2.0 IL type `instr`. -/
def instrToV : V2.Instr → Value
  | .nop => caseNilV "NOP"
  | .unreachable => caseNilV "UNREACHABLE"
  | .drop => caseNilV "DROP"
  | .select ts => .case "SELECT" (.opt (ts.map fun ts => .list (ts.map valTypeV)))
  | .block bt body => .case "BLOCK" (.tuple [blockTypeV bt, .list (instrsToV body)])
  | .loop bt body => .case "LOOP" (.tuple [blockTypeV bt, .list (instrsToV body)])
  | .if_ bt b₁ b₂ =>
      .case "IF%%ELSE%" (.tuple [blockTypeV bt, .list (instrsToV b₁), .list (instrsToV b₂)])
  | .br l => .case "BR" (idxV l)
  | .brIf l => .case "BR_IF" (idxV l)
  | .brTable ls l => .case "BR_TABLE" (.tuple [.list (ls.map idxV), idxV l])
  | .call x => .case "CALL" (idxV x)
  | .callIndirect x y => .case "CALL_INDIRECT" (.tuple [idxV x, idxV y])
  | .return_ => caseNilV "RETURN"
  | .intConst t b => valV (.num ⟨.int t, b⟩)
  | .floatConst t b => valV (.num ⟨.float t, b⟩)
  | .intUnOp t op => .case "UNOP" (.tuple [numTypeV (.int t), intUnOpV op])
  | .floatUnOp t op => .case "UNOP" (.tuple [numTypeV (.float t), floatUnOpV op])
  | .intBinOp t op => .case "BINOP" (.tuple [numTypeV (.int t), intBinOpV op])
  | .floatBinOp t op => .case "BINOP" (.tuple [numTypeV (.float t), floatBinOpV op])
  | .intTestOp t op => .case "TESTOP" (.tuple [numTypeV (.int t), intTestOpV op])
  | .intRelOp t op => .case "RELOP" (.tuple [numTypeV (.int t), intRelOpV op])
  | .floatRelOp t op => .case "RELOP" (.tuple [numTypeV (.float t), floatRelOpV op])
  | .cvtOp t₁ t₂ op => .case "CVTOP" (.tuple [numTypeV t₁, numTypeV t₂, cvtOpV op])
  | .vecConst b => valV (.vec b)
  | .vvUnOp .not => .case "VVUNOP" (.tuple [caseNilV "V128", caseNilV "NOT"])
  | .vvBinOp op => .case "VVBINOP" (.tuple [caseNilV "V128", match op with
      | .and => caseNilV "AND" | .andnot => caseNilV "ANDNOT"
      | .or => caseNilV "OR" | .xor => caseNilV "XOR"])
  | .vvTernOp .bitselect => .case "VVTERNOP" (.tuple [caseNilV "V128", caseNilV "BITSELECT"])
  | .vvTestOp .anyTrue => .case "VVTESTOP" (.tuple [caseNilV "V128", caseNilV "ANY_TRUE"])
  | .vecIntUnOp s op => .case "VUNOP" (.tuple [shapeV (.int s), vecIntUnOpV op])
  | .vecFloatUnOp s op => .case "VUNOP" (.tuple [shapeV (.float s), floatUnOpV op])
  | .vecIntBinOp s op => .case "VBINOP" (.tuple [shapeV (.int s), vecIntBinOpV op])
  | .vecFloatBinOp s op => .case "VBINOP" (.tuple [shapeV (.float s), vecFloatBinOpV op])
  | .vecAllTrue s => .case "VTESTOP" (.tuple [shapeV (.int s), caseNilV "ALL_TRUE"])
  | .vecIntRelOp s op => .case "VRELOP" (.tuple [shapeV (.int s), vecIntRelOpV op])
  | .vecFloatRelOp s op => .case "VRELOP" (.tuple [shapeV (.float s), floatRelOpV op])
  | .vecShiftOp s op => .case "VSHIFTOP" (.tuple [ishapeV s, vecShiftOpV op])
  | .vecBitmask s => .case "VBITMASK" (ishapeV s)
  | .vecSwizzle => .case "VSWIZZLE" (.tuple [ishapeV .i8x16])
  | .vecShuffle ls => .case "VSHUFFLE" (.tuple [ishapeV .i8x16, .list (ls.map fun l => pctV l.val)])
  | .vecSplat s => .case "VSPLAT" (shapeV s)
  | .vecExtractLane s sx l =>
      .case "VEXTRACT_LANE" (.tuple [shapeV s, .opt (sx.map sxV), pctV l.val])
  | .vecReplaceLane s l => .case "VREPLACE_LANE" (.tuple [shapeV s, pctV l.val])
  | .vecExtUnOp t s op => .case "VEXTUNOP" (.tuple [ishapeV t, ishapeV s, vecExtUnOpV op])
  | .vecExtBinOp t s op => .case "VEXTBINOP" (.tuple [ishapeV t, ishapeV s, vecExtBinOpV op])
  | .vecNarrow t s sx => .case "VNARROW" (.tuple [ishapeV t, ishapeV s, sxV sx])
  | .vecCvtOp t s op => .case "VCVTOP" (.tuple [shapeV t, shapeV s, vecCvtOpV op])
  | .refNull t => .case "REF.NULL" (refTypeV t)
  | .refFunc x => .case "REF.FUNC" (idxV x)
  | .refIsNull => caseNilV "REF.IS_NULL"
  | .localGet x => .case "LOCAL.GET" (idxV x)
  | .localSet x => .case "LOCAL.SET" (idxV x)
  | .localTee x => .case "LOCAL.TEE" (idxV x)
  | .globalGet x => .case "GLOBAL.GET" (idxV x)
  | .globalSet x => .case "GLOBAL.SET" (idxV x)
  | .tableGet x => .case "TABLE.GET" (idxV x)
  | .tableSet x => .case "TABLE.SET" (idxV x)
  | .tableSize x => .case "TABLE.SIZE" (idxV x)
  | .tableGrow x => .case "TABLE.GROW" (idxV x)
  | .tableFill x => .case "TABLE.FILL" (idxV x)
  | .tableCopy x y => .case "TABLE.COPY" (.tuple [idxV x, idxV y])
  | .tableInit x y => .case "TABLE.INIT" (.tuple [idxV x, idxV y])
  | .elemDrop x => .case "ELEM.DROP" (idxV x)
  | .intLoad t p a => .case "LOAD" (.tuple [numTypeV (.int t),
      .opt (p.map fun q => .case "%_%" (.tuple [szV q.1, sxV q.2])), memargV a])
  | .floatLoad t a => .case "LOAD" (.tuple [numTypeV (.float t), .opt none, memargV a])
  | .intStore t p a => .case "STORE" (.tuple [numTypeV (.int t), .opt (p.map szV), memargV a])
  | .floatStore t a => .case "STORE" (.tuple [numTypeV (.float t), .opt none, memargV a])
  | .vecLoad op a => .case "VLOAD" (.tuple [caseNilV "V128", .opt (op.map vecLoadOpV), memargV a])
  | .vecLoadLane sz a l =>
      .case "VLOAD_LANE" (.tuple [caseNilV "V128", szV sz, memargV a, pctV l.val])
  | .vecStore a => .case "VSTORE" (.tuple [caseNilV "V128", memargV a])
  | .vecStoreLane sz a l =>
      .case "VSTORE_LANE" (.tuple [caseNilV "V128", szV sz, memargV a, pctV l.val])
  | .memorySize => caseNilV "MEMORY.SIZE"
  | .memoryGrow => caseNilV "MEMORY.GROW"
  | .memoryFill => caseNilV "MEMORY.FILL"
  | .memoryCopy => caseNilV "MEMORY.COPY"
  | .memoryInit x => .case "MEMORY.INIT" (idxV x)
  | .dataDrop x => .case "DATA.DROP" (idxV x)

/-- `instrToV` on a sequence. -/
def instrsToV : List V2.Instr → List Value
  | [] => []
  | i :: is => instrToV i :: instrsToV is
end

/-! ## Runtime structure -/

/-- `byte = %(i)`. -/
def bytesV (b : ByteArray) : Value := .list (b.toList.map fun x => pctV x.toNat)

/-- `name = %(char*)`. -/
def nameV (s : String) : Value := .case "%" (.tuple [.list (s.toList.map fun c => pctV c.toNat)])

/-- `externaddr`. -/
def externAddrV : ExternAddr → Value
  | .func a => .case "FUNC" (.num (.natN a))
  | .global a => .case "GLOBAL" (.num (.natN a))
  | .table a => .case "TABLE" (.num (.natN a))
  | .mem a => .case "MEM" (.num (.natN a))

/-- An address list. -/
def addrsV (xs : List Nat) : Value := .list (xs.map fun a => .num (.natN a))

/-- `moduleinst`, eight fields. -/
def moduleInstV (m : ModuleInst) : Value :=
  .struct [("TYPES", .list (m.types.map funcTypeV)), ("FUNCS", addrsV m.funcs),
    ("GLOBALS", addrsV m.globals), ("TABLES", addrsV m.tables), ("MEMS", addrsV m.mems),
    ("ELEMS", addrsV m.elems), ("DATAS", addrsV m.datas),
    ("EXPORTS", .list (m.exports.map fun e =>
      .struct [("NAME", nameV e.name), ("ADDR", externAddrV e.addr)]))]

/-- `frame = {LOCALS val*, MODULE moduleinst}`. -/
def frameV (f : Frame) : Value :=
  .struct [("LOCALS", .list (f.locals.map valV)), ("MODULE", moduleInstV f.module)]

mutual
/-- A V2 administrative instruction as a value of the wasm-2.0 IL type `admininstr`. -/
def adminToV : Admin → Value
  | .plain i => instrToV i
  | .refFuncAddr a => .case "REF.FUNC_ADDR" (.num (.natN a))
  | .refHostAddr a => .case "REF.HOST_ADDR" (.num (.natN a))
  | .callAddr a => .case "CALL_ADDR" (.num (.natN a))
  | .label n cont body =>
      .case "LABEL_%{%}%" (.tuple [.num (.natN n), .list (instrsToV cont), .list (adminsToV body)])
  | .frame n f body => .case "FRAME_%{%}%" (.tuple [.num (.natN n), frameV f, .list (adminsToV body)])
  | .trap => caseNilV "TRAP"

/-- `adminToV` on a sequence. -/
def adminsToV : List Admin → List Value
  | [] => []
  | a :: rest => adminToV a :: adminsToV rest
end

variable {H : Type}

/-- `funcinst = {TYPE functype, MODULE moduleinst, CODE func}`, with
`func = FUNC typeidx local* expr`; a host function is `_HOSTFUNC (hn h)` (not a 2.0 `func`). -/
def funcInstV (hn : H → String) (fi : FuncInst H) : Value :=
  .struct [("TYPE", funcTypeV fi.type), ("MODULE", moduleInstV fi.module),
    ("CODE", match fi.code with
      | .wasm fn => .case "FUNC" (.tuple [idxV fn.type,
          .list (fn.locals.map fun t => .case "LOCAL" (valTypeV t)), .list (instrsToV fn.body)])
      | .host h => .case "_HOSTFUNC" (.text (hn h)))]

/-- `globalinst = {TYPE globaltype, VALUE val}`. -/
def globalInstV (g : GlobalInst) : Value :=
  .struct [("TYPE", globalTypeV g.type), ("VALUE", valV g.value)]

/-- `tableinst = {TYPE tabletype, REFS ref*}`. -/
def tableInstV (t : TableInst) : Value :=
  .struct [("TYPE", tableTypeV t.type), ("REFS", .list (t.refs.map refV))]

/-- `meminst = {TYPE memtype, BYTES byte*}`. -/
def memInstV (m : MemInst) : Value :=
  .struct [("TYPE", memTypeV m.type), ("BYTES", bytesV m.bytes)]

/-- `eleminst = {TYPE elemtype, REFS ref*}`. -/
def elemInstV (e : ElemInst) : Value :=
  .struct [("TYPE", refTypeV e.type), ("REFS", .list (e.refs.map refV))]

/-- `datainst = {BYTES byte*}`. -/
def dataInstV (d : DataInst) : Value := .struct [("BYTES", bytesV d.bytes)]

/-- `store`, six fields in the order of `4-runtime.spectec:104`. -/
def storeV (hn : H → String) (s : Store H) : Value :=
  .struct [("FUNCS", .list (s.funcs.map (funcInstV hn))),
    ("GLOBALS", .list (s.globals.map globalInstV)), ("TABLES", .list (s.tables.map tableInstV)),
    ("MEMS", .list (s.mems.map memInstV)), ("ELEMS", .list (s.elems.map elemInstV)),
    ("DATAS", .list (s.datas.map dataInstV))]

/-- `state = store; frame`. -/
def stateV (hn : H → String) (s : Store H) (f : Frame) : Value :=
  .case "%;%" (.tuple [storeV hn s, frameV f])

/-- **The encoding of V2 configurations**: `config = state; admininstr*`. -/
def configV (hn : H → String) (c : Config H) : Value :=
  .case "%;%" (.tuple [stateV hn c.store c.frame, .list (adminsToV c.code)])

/-! ## The environment and typing -/

/-- The fixed wasm-2.0 script as an environment, with no primitives interpreted. -/
noncomputable def baseEnv20 : Env := envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed

/-- `baseEnv20` with the primitives `B` installed: the 2.0 counterpart of `Sim.simEnv`. -/
noncomputable def simEnv20 (B : Builtins) : Env := baseEnv20.withBuiltins B

/-- `c`'s image is a value of the wasm-2.0 IL type `config`. -/
def Typed20 (env : Env) (hn : H → String) (c : Config H) : Prop :=
  HasTyp env VarEnv.empty (.varT "config" []) (configV hn c)

end Silmaril.Wasm.SpecTec.Sim20
