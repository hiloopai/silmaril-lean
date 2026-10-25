module

public import Silmaril.Wasm.Validation.Modules
public import Silmaril.Wasm.Execution.Memory
public import Silmaril.Wasm.Execution.Host

@[expose] public section

/-! # Core 3.0 runtime structure (§4.0)

Namespace `Silmaril.Wasm.Execution.Core`, parallel to (and independent of) the
V1/Lime1 runtime `Silmaril.Wasm.Execution.Runtime`, which is untouched.

Carriers transcribe `4.0-execution.configurations.spectec`:

* addresses are `Nat` (`addr = nat`);
* `Ref` has all eight reference forms, including `REF.NULL_ADDR` (`Ref.null`)
  and `REF.EXTERN ref`;
* `Val = num | vec | ref`; `FieldVal = val | PACK packtype iN`;
* every instance kind, the store, frames (`LOCALS (val?)*`, `MODULE`);
* `Admin`: source instructions (`plain`), reference values, the four
  administrative forms `LABEL_n{instr*}`, `FRAME_n{frame}`,
  `HANDLER_n{catch*}`, `TRAP`, and `CALL_REF`/`RETURN_CALL_REF` annotated with a
  *defined* type (the spec's runtime `typeuse` may be a `deftype`, as produced by
  `Step_read/call` and `$invoke`; source syntax only has indices).

**Values are instructions.** A value is not a separate administrative form:
numbers and vectors are the constant *source* instructions, references are
`Admin.ref`. `Val.toAdmin` is the spec's inclusion `val ⊆ instr`. V1/Lime1
values (`.source (.intConst …)`) therefore map to Core values by the instruction
map, with no extra case.

**Host functions.** Function code is `FuncCode H = wasm (Wasm.Func) | host H`;
`H : Type` is the embedder's host-function type (the component model instantiates
it). `HostSemantics H` is a *relation*: a host call may return a new store and a
result (values, exception, or trap) or diverge — the spec's `$hostcall` result set.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

/-- `num = CONST numtype num_(numtype)`. Same shape as the V1/Lime1 `Runtime.Value`. -/
structure NumVal where
  type : NumType
  bits : BitVec type.width
  deriving DecidableEq, Repr

/-- `ref`: runtime references. -/
inductive Ref where
  | i31 (bits : BitVec 31)
  | null
  | struct (a : Nat)
  | array (a : Nat)
  | func (a : Nat)
  | exn (a : Nat)
  | host (a : Nat)
  | extern (r : Ref)
  deriving DecidableEq, Repr

/-- `val = num | vec | ref`. -/
inductive Val where
  | num (v : NumVal)
  | vec (bits : BitVec 128)
  | ref (r : Ref)
  deriving DecidableEq, Repr

def Val.i32 (b : BitVec 32) : Val := .num ⟨.int .i32, b⟩
def Val.i64 (b : BitVec 64) : Val := .num ⟨.int .i64, b⟩

/-- `fieldval = val | PACK packtype iN`. -/
inductive FieldVal where
  | val (v : Val)
  | pack (p : PackType) (bits : BitVec p.width)
  deriving DecidableEq, Repr

inductive ExternAddr where
  | tag (a : Nat)
  | global (a : Nat)
  | mem (a : Nat)
  | table (a : Nat)
  | func (a : Nat)
  deriving DecidableEq, Repr

structure ExportInst where
  name : String
  addr : ExternAddr
  deriving DecidableEq, Repr

structure ModuleInst where
  types : List DefType := []
  tags : List Nat := []
  globals : List Nat := []
  mems : List Nat := []
  tables : List Nat := []
  funcs : List Nat := []
  datas : List Nat := []
  elems : List Nat := []
  exports : List ExportInst := []
  deriving DecidableEq, Repr

structure TagInst where
  type : DefType
  deriving DecidableEq, Repr

structure GlobalInst where
  type : CGlobalType
  value : Val
  deriving DecidableEq, Repr

structure MemInst where
  type : MemoryType
  bytes : ByteArray
  deriving DecidableEq, Repr

structure TableInst where
  type : CTableType
  refs : List Ref
  deriving DecidableEq, Repr

/-- `funccode = func | hostfunc`. -/
inductive FuncCode (H : Type) where
  | wasm (f : Func)
  | host (h : H)
  deriving Repr

structure FuncInst (H : Type) where
  type : DefType
  module : ModuleInst
  code : FuncCode H
  deriving Repr

structure DataInst where
  bytes : ByteArray
  deriving DecidableEq, Repr

structure ElemInst where
  type : CRefType
  refs : List Ref
  deriving DecidableEq, Repr

structure StructInst where
  type : DefType
  fields : List FieldVal
  deriving DecidableEq, Repr

structure ArrayInst where
  type : DefType
  fields : List FieldVal
  deriving DecidableEq, Repr

structure ExnInst where
  tag : Nat
  fields : List Val
  deriving DecidableEq, Repr

/-- `store`. The GC heap (`structs`, `arrays`, `exns`) only grows. -/
structure Store (H : Type) where
  tags : List TagInst := []
  globals : List GlobalInst := []
  mems : List MemInst := []
  tables : List TableInst := []
  funcs : List (FuncInst H) := []
  datas : List DataInst := []
  elems : List ElemInst := []
  structs : List StructInst := []
  arrays : List ArrayInst := []
  exns : List ExnInst := []
  deriving Repr

/-- `frame = {LOCALS (val?)*, MODULE moduleinst}`; unset non-defaultable locals are `none`. -/
structure Frame where
  locals : List (Option Val) := []
  module : ModuleInst := {}
  deriving DecidableEq, Repr

/-- Administrative instructions (`instr/admin`). -/
inductive Admin where
  /-- A source instruction (including the constant instructions that are values). -/
  | plain (i : Instr)
  /-- A reference value. -/
  | ref (r : Ref)
  /-- `CALL_REF dt` with a runtime defined type. -/
  | callRefType (d : DefType)
  /-- `RETURN_CALL_REF dt` with a runtime defined type. -/
  | returnCallRefType (d : DefType)
  /-- `LABEL_n{instr*} instr*`. -/
  | label (n : Nat) (cont : List Instr) (body : List Admin)
  /-- `HANDLER_n{catch*} instr*`. -/
  | handler (n : Nat) (catches : List Catch) (body : List Admin)
  /-- `FRAME_n{frame} instr*`. -/
  | frame (n : Nat) (f : Frame) (body : List Admin)
  | trap
  deriving Repr

/-- `config = store; frame; instr*`. -/
structure Config (H : Type) where
  store : Store H
  frame : Frame
  code : List Admin
  deriving Repr

/-- `result = _VALS val* | (REF.EXN_ADDR a) THROW_REF | TRAP`. -/
inductive Result where
  | values (vs : List Val)
  | throw (a : Nat)
  | trap
  deriving DecidableEq, Repr

/-- `hostcallresult = RES store result | BOT`, as the shared
`Silmaril.Wasm.Execution.Host.Outcome`. -/
abbrev HostOutcome (H : Type) :=
  Silmaril.Wasm.Execution.Host.Outcome (Store H) Result

/-- `$hostcall(hostfunc, store, val*)` as a relation, as the shared
`Silmaril.Wasm.Execution.Host.Semantics`. -/
abbrev HostSemantics (H : Type) :=
  Silmaril.Wasm.Execution.Host.Semantics H (Store H) Val Result

/-! ## Values as instructions -/

/-- The inclusion `val ⊆ instr`. -/
def Val.toAdmin : Val → Admin
  | .num ⟨.int t, b⟩ => .plain (.intConst t b)
  | .num ⟨.float t, b⟩ => .plain (.floatConst t b)
  | .vec b => .plain (.vecConst b)
  | .ref r => .ref r

/-- Recognise a value instruction. -/
def Admin.val? : Admin → Option Val
  | .plain (.intConst t b) => some (.num ⟨.int t, b⟩)
  | .plain (.floatConst t b) => some (.num ⟨.float t, b⟩)
  | .plain (.vecConst b) => some (.vec b)
  | .ref r => some (.ref r)
  | _ => none

@[simp] theorem Admin.val?_toAdmin (v : Val) : v.toAdmin.val? = some v := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

def vals (vs : List Val) : List Admin := vs.map Val.toAdmin

@[simp] theorem vals_append (xs ys : List Val) : vals (xs ++ ys) = vals xs ++ vals ys :=
  List.map_append

@[simp] theorem vals_length (xs : List Val) : (vals xs).length = xs.length := List.length_map _

def expression (es : Expr) : List Admin := es.map .plain

/-- `$lift_result(result)`. -/
def Result.toAdmin : Result → List Admin
  | .values vs => vals vs
  | .throw a => [.ref (.exn a), .plain .throwRef]
  | .trap => [.trap]

/-- `CONST I32 c` as an instruction. -/
def constI32 (b : BitVec 32) : Admin := (Val.i32 b).toAdmin

/-- `CONST at n` for an address type. -/
def constAddr (a : AddrType) (n : Nat) : Admin :=
  match a with
  | .i32 => .plain (.intConst .i32 (BitVec.ofNat 32 n))
  | .i64 => .plain (.intConst .i64 (BitVec.ofNat 64 n))

/-! ## Default values (§4.1 `$default_`) -/

def defaultVal? : CValType → Option Val
  | .num (.int t) => some (.num ⟨.int t, 0⟩)
  | .num (.float t) => some (.num ⟨.float t, 0⟩)
  | .vec _ => some (.vec 0)
  | .refv (.ref true _) => some (.ref .null)
  | .refv (.ref false _) => none
  | .botv => none

theorem defaultVal?_isSome_iff (t : CValType) : (defaultVal? t).isSome ↔ Defaultable t := by
  unfold defaultVal?
  split <;> simp [Defaultable]

/-! ## Invoking a function under the spec's calling convention -/

/-- The locals of a new frame: arguments, then the defaults of the declared
locals (`val^n ($default_(t))*`); non-defaultable locals are unset. -/
def Frame.forCall (module : ModuleInst) (args : List Val) (locals : List ValType) : Frame :=
  ⟨args.map some ++ locals.map (fun t => defaultVal? ((liftVal t).substAll (module.types.map .dt))),
    module⟩

end Silmaril.Wasm.Execution.Core
