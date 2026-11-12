module

public import Silmaril.Wasm.SpecTec.Sim20.Encode.Defs
public import Silmaril.Wasm.V1.Execution.Step

/-!
# SpecTec 1.0 ↔ silmaril-lean V1: the encoding of configurations

`Sim10.configV hn c` is the SpecTec wasm-1.0 IL value of a V1 configuration `c`
(`Silmaril.Wasm.V1.Execution.Config H`), written against the IL types of
`Scripts.Wasm10.fixed` (`specs/spectec/src/specification/wasm-1.0`). It is the 1.0 counterpart of
`Sim20.configV`, and reuses its encodings of the operators 1.0 and 2.0 share (`Sim20.numTypeV`,
`Sim20.intBinOpV`, …) and the float encoding `Sim.floatV`.

How 1.0 differs from 2.0, as the encoding sees it:

* `valtype` is `I32 | I64 | F32 | F64` (2.0's `numtype`) and a value is `CONST valtype val_(valtype)`;
* `blocktype = valtype?`, `SELECT` has no annotation and `CALL_INDIRECT` names no table;
* `functype = valtype* -> valtype*` with no `resulttype` wrapper;
* `tabletype = memtype = limits`; a table holds `funcaddr?`, not references;
* the store has four fields (`FUNCS GLOBALS TABLES MEMS`) and a module instance six;
* `UNOP` has no `EXTEND`, `cvtop` has no `TRUNC_SAT`, and `LOAD`'s pack is `sz _ sx`.

V1 table and memory instances record only their maximum, so their `TYPE` is rebuilt with the
current size as minimum (`tableInstV`, `memInstV`). A V1 value is a constant instruction
(`V1.Execution.value`), as in the script, where `val` is a subtype of `instr`.

**Host functions.** wasm-1.0 has none in its IL. A host function instance is encoded with
`CODE = _HOSTFUNC (hn h)`, which is not a 1.0 `func`, so a store holding one is not `Typed10`.

The encoding is checked against the IL types by `Sim10.Encode.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Runtime (FuncInst GlobalInst TableInst MemInst ModuleInst Frame
  ExternVal Addr AddrKind)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim20 (numTypeV sxV intBinOpV floatUnOpV floatBinOpV intTestOpV
  intRelOpV floatRelOpV)

/-! ## Types -/

/-- `valtype = I32 | I64 | F32 | F64`, 2.0's `numtype`. -/
abbrev valTypeV (t : V1.ValType) : Value := numTypeV t

/-- `functype = valtype* -> valtype*`. -/
def funcTypeV (ft : V1.FuncType) : Value :=
  .case "%->%" (.tuple [.list (ft.params.map valTypeV), .list (ft.results.map valTypeV)])

/-- `limits = [u32 .. u32?]`. -/
def limitsV (min : Nat) (max : Option Nat) : Value :=
  .case "[%..%]" (.tuple [pctV min, .opt (max.map pctV)])

/-- `mut = MUT?`. -/
def mutV : Mutability → Value
  | .var => .opt (some (caseNilV "MUT"))
  | .const => .opt none

/-- `globaltype = mut valtype`. -/
def globalTypeV (m : Mutability) (t : V1.ValType) : Value :=
  .case "%%" (.tuple [mutV m, valTypeV t])

/-- An index `idx = u32 = uN(32)`, i.e. `%(i)`. -/
def idxV {k : IndexKind} (x : Idx k) : Value := pctV x.toNat

/-- `blocktype = valtype?`. -/
def blockTypeV (bt : V1.BlockType) : Value := .opt (bt.map valTypeV)

/-! ## Values -/

/-- `val_(t)`: `%(i)` for an integer, SpecTec's `fN` for a float. -/
def numV : Execution.Runtime.Value → Sem.Value
  | ⟨.int _, b⟩ => pctV b.toNat
  | ⟨.float t, b⟩ => Sim.floatV t b

/-- `val = CONST valtype val_(valtype)`. -/
def valV (v : Execution.Runtime.Value) : Sem.Value := .case "CONST" (.tuple [valTypeV v.type, numV v])

/-! ## Operators -/

/-- `unop_(Inn) = CLZ | CTZ | POPCNT`. -/
def intUnOpV : V1.IntUnOp → Sem.Value
  | .clz => caseNilV "CLZ"
  | .ctz => caseNilV "CTZ"
  | .popcnt => caseNilV "POPCNT"

/-- `cvtop = EXTEND sx | WRAP | CONVERT sx | TRUNC sx | PROMOTE | DEMOTE | REINTERPRET`. -/
def cvtOpV : V1.ConvertOp → Sem.Value
  | .wrap => caseNilV "WRAP"
  | .extend s => .case "EXTEND" (sxV s)
  | .trunc _ _ s => .case "TRUNC" (sxV s)
  | .convert _ _ s => .case "CONVERT" (sxV s)
  | .demote => caseNilV "DEMOTE"
  | .promote => caseNilV "PROMOTE"
  | .reinterpretInt _ => caseNilV "REINTERPRET"
  | .reinterpretFloat _ => caseNilV "REINTERPRET"

/-- `memarg = {ALIGN u32, OFFSET u32}`. -/
def memargV (a : V1.MemArg) : Sem.Value :=
  .struct [("ALIGN", pctV a.align.val), ("OFFSET", pctV a.offset.val)]

/-- `sz = 8 | 16 | 32 | 64`, i.e. `%(i)`. -/
def szV (p : V1.PackSize) : Sem.Value := pctV p.width

/-! ## Instructions -/

mutual
/-- A V1 instruction as a value of the wasm-1.0 IL type `instr`. -/
def instrToV : V1.Instr → Sem.Value
  | .nop => caseNilV "NOP"
  | .unreachable => caseNilV "UNREACHABLE"
  | .drop => caseNilV "DROP"
  | .select => caseNilV "SELECT"
  | .block bt body => .case "BLOCK" (.tuple [blockTypeV bt, .list (instrsToV body)])
  | .loop bt body => .case "LOOP" (.tuple [blockTypeV bt, .list (instrsToV body)])
  | .if_ bt b₁ b₂ =>
      .case "IF%%ELSE%" (.tuple [blockTypeV bt, .list (instrsToV b₁), .list (instrsToV b₂)])
  | .br l => .case "BR" (idxV l)
  | .brIf l => .case "BR_IF" (idxV l)
  | .brTable ls l => .case "BR_TABLE" (.tuple [.list (ls.map idxV), idxV l])
  | .call x => .case "CALL" (idxV x)
  | .callIndirect x => .case "CALL_INDIRECT" (idxV x)
  | .return_ => caseNilV "RETURN"
  | .localGet x => .case "LOCAL.GET" (idxV x)
  | .localSet x => .case "LOCAL.SET" (idxV x)
  | .localTee x => .case "LOCAL.TEE" (idxV x)
  | .globalGet x => .case "GLOBAL.GET" (idxV x)
  | .globalSet x => .case "GLOBAL.SET" (idxV x)
  | .intLoad t p a => .case "LOAD" (.tuple [valTypeV (.int t),
      .opt (p.map fun q => .case "%_%" (.tuple [szV q.1, sxV q.2])), memargV a])
  | .floatLoad t a => .case "LOAD" (.tuple [valTypeV (.float t), .opt none, memargV a])
  | .intStore t p a => .case "STORE" (.tuple [valTypeV (.int t), .opt (p.map szV), memargV a])
  | .floatStore t a => .case "STORE" (.tuple [valTypeV (.float t), .opt none, memargV a])
  | .memorySize => caseNilV "MEMORY.SIZE"
  | .memoryGrow => caseNilV "MEMORY.GROW"
  | .intConst t b => valV ⟨.int t, b⟩
  | .floatConst t b => valV ⟨.float t, b⟩
  | .intUnOp t op => .case "UNOP" (.tuple [valTypeV (.int t), intUnOpV op])
  | .intBinOp t op => .case "BINOP" (.tuple [valTypeV (.int t), intBinOpV op])
  | .intTestOp t op => .case "TESTOP" (.tuple [valTypeV (.int t), intTestOpV op])
  | .intRelOp t op => .case "RELOP" (.tuple [valTypeV (.int t), intRelOpV op])
  | .floatUnOp t op => .case "UNOP" (.tuple [valTypeV (.float t), floatUnOpV op])
  | .floatBinOp t op => .case "BINOP" (.tuple [valTypeV (.float t), floatBinOpV op])
  | .floatRelOp t op => .case "RELOP" (.tuple [valTypeV (.float t), floatRelOpV op])
  | .convert op => .case "CVTOP"
      (.tuple [valTypeV op.toCore.target, valTypeV op.toCore.source, cvtOpV op])

/-- `instrToV` on a sequence. -/
def instrsToV : List V1.Instr → List Sem.Value
  | [] => []
  | i :: is => instrToV i :: instrsToV is
end

/-! ## Runtime structure -/

/-- `byte = %(i)`. -/
def bytesV (b : ByteArray) : Sem.Value := .list (b.toList.map fun x => pctV x.toNat)

/-- `externaddr = FUNC funcaddr | GLOBAL globaladdr | TABLE tableaddr | MEM memaddr`. -/
def externAddrV : ExternVal → Sem.Value
  | .func a => .case "FUNC" (.num (.natN a.value))
  | .global a => .case "GLOBAL" (.num (.natN a.value))
  | .table a => .case "TABLE" (.num (.natN a.value))
  | .memory a => .case "MEM" (.num (.natN a.value))

/-- An address list. -/
def addrsV {k : AddrKind} (xs : List (Addr k)) : Sem.Value :=
  .list (xs.map fun a => .num (.natN a.value))

/-- `moduleinst`, six fields. -/
def moduleInstV (m : ModuleInst) : Sem.Value :=
  .struct [("TYPES", .list (m.types.map funcTypeV)), ("FUNCS", addrsV m.funcs),
    ("GLOBALS", addrsV m.globals), ("TABLES", addrsV m.tables), ("MEMS", addrsV m.memories),
    ("EXPORTS", .list (m.exports.map fun e =>
      .struct [("NAME", Sim20.nameV e.name), ("ADDR", externAddrV e.value)]))]

/-- `frame = {LOCALS val*, MODULE moduleinst}`. -/
def frameV (f : Frame) : Sem.Value :=
  .struct [("LOCALS", .list (f.locals.map valV)), ("MODULE", moduleInstV f.module)]

mutual
/-- A V1 administrative instruction as a value of the wasm-1.0 IL type `admininstr`. -/
def adminToV : V1.Execution.Admin → Sem.Value
  | .source i => instrToV i
  | .invoke a => .case "CALL_ADDR" (.num (.natN a.value))
  | .label n cont body =>
      .case "LABEL_%{%}%" (.tuple [.num (.natN n), .list (instrsToV cont), .list (adminsToV body)])
  | .frame n f body => .case "FRAME_%{%}%" (.tuple [.num (.natN n), frameV f, .list (adminsToV body)])
  | .trap => caseNilV "TRAP"

/-- `adminToV` on a sequence. -/
def adminsToV : List V1.Execution.Admin → List Sem.Value
  | [] => []
  | a :: rest => adminToV a :: adminsToV rest
end

variable {H : Type}

/-- `func = FUNC typeidx local* expr`. -/
def funcV (fn : V1.Func) : Sem.Value :=
  .case "FUNC" (.tuple [idxV fn.type, .list (fn.locals.map fun t => .case "LOCAL" (valTypeV t)),
    .list (instrsToV fn.body)])

/-- `funcinst = {TYPE functype, MODULE moduleinst, CODE func}`; a host function is
`_HOSTFUNC (hn h)` with an empty module instance (not a 1.0 `func`). -/
def funcInstV (hn : H → String) : FuncInst V1.Func H → Sem.Value
  | .wasm t m fn => .struct [("TYPE", funcTypeV t), ("MODULE", moduleInstV m), ("CODE", funcV fn)]
  | .host t h => .struct [("TYPE", funcTypeV t), ("MODULE", moduleInstV {}),
      ("CODE", .case "_HOSTFUNC" (.text (hn h)))]

/-- `globalinst = {TYPE globaltype, VALUE val}`. -/
def globalInstV (g : GlobalInst) : Sem.Value :=
  .struct [("TYPE", globalTypeV g.mutability g.value.type), ("VALUE", valV g.value)]

/-- `tableinst = {TYPE tabletype, REFS (funcaddr?)*}`, with the current size as minimum. -/
def tableInstV (t : TableInst) : Sem.Value :=
  .struct [("TYPE", limitsV t.refs.length t.max),
    ("REFS", .list (t.refs.map fun r => .opt (r.map fun a => .num (.natN a.value))))]

/-- `meminst = {TYPE memtype, BYTES byte*}`, with the current page count as minimum. -/
def memInstV (m : MemInst) : Sem.Value :=
  .struct [("TYPE", limitsV (Execution.Memory.size m.data) m.max), ("BYTES", bytesV m.data)]

/-- `store`, four fields in the order of `4-runtime.spectec:83`. -/
def storeV (hn : H → String) (s : V1.Execution.Store H) : Sem.Value :=
  .struct [("FUNCS", .list (s.funcs.map (funcInstV hn))),
    ("GLOBALS", .list (s.globals.map globalInstV)), ("TABLES", .list (s.tables.map tableInstV)),
    ("MEMS", .list (s.memories.map memInstV))]

/-- `state = store; frame`. -/
def stateV (hn : H → String) (s : V1.Execution.Store H) (f : Frame) : Sem.Value :=
  .case "%;%" (.tuple [storeV hn s, frameV f])

/-- **The encoding of V1 configurations**: `config = state; admininstr*`. -/
def configV (hn : H → String) (c : V1.Execution.Config H) : Sem.Value :=
  .case "%;%" (.tuple [stateV hn c.store c.frame, .list (adminsToV c.code)])

/-! ## The environment and typing -/

/-- The fixed wasm-1.0 script as an environment, with no primitives interpreted. -/
noncomputable def baseEnv10 : Env := envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm10.fixed

/-- `baseEnv10` with the primitives `B` installed: the 1.0 counterpart of `Sim20.simEnv20`. -/
noncomputable def simEnv10 (B : Builtins) : Env := baseEnv10.withBuiltins B

/-- `c`'s image is a value of the wasm-1.0 IL type `config`. -/
def Typed10 (env : Env) (hn : H → String) (c : V1.Execution.Config H) : Prop :=
  HasTyp env VarEnv.empty (.varT "config" []) (configV hn c)

end Silmaril.Wasm.SpecTec.Sim10
