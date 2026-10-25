module

public import Silmaril.Wasm.V2.Modules
public import Silmaril.Wasm.Execution.Memory
public import Silmaril.Wasm.Execution.Host

/-!
# WebAssembly 2.0 runtime structure

Transcribed from the official SpecTec sources
`specification/wasm-2.0/4-runtime.spectec` and
`specification/wasm-2.0/5-runtime-aux.spectec` at WebAssembly/spec revision
`608711107b7f1edb13efd57b7d79b49477462d36` (see `specs/wasm/core-2.0.json`).
Line references of the form `4-runtime:NN` and `5-runtime-aux:NN` point into
those files.

The layout follows `Silmaril.Wasm.Execution.Core.Runtime` and
`Silmaril.Wasm.Execution.Core.Store`, which do the same job for Core 3.0:
addresses are `Nat`, every instance kind is a structure with exactly the fields
of `4-runtime:60-110`, and the state accessors of `5-runtime-aux:74-90` are
`Option`-valued.

**Partiality.** SpecTec writes `$table(z, x) = s.TABLES[f.MODULE.TABLES[x]]`,
where both list indexings are partial. We return `Option`; a reduction rule that
needs the lookup carries `$table(z, x) = some ti` as a premise, so the machine is
*stuck* (not trapped) on an out-of-range index, exactly where SpecTec's rule has
no instance. A type-soundness proof would rule this out for well-typed
configurations; that development is not included here. The two
updates whose partiality SpecTec's rules do *not* guard — `$with_local`
(`8-reduction:380-381` has no bound premise) and the inner `REFS[i] = r` of
`$with_table` (`8-reduction:410-412` bounds `i` but the array update itself is
total) — use `List.set`, which is the identity out of range.

**Deviation: host functions.** SpecTec 2.0's `funcinst` (`4-runtime:60`) has only
`CODE func`: there is no host-function alternative anywhere in the 2.0 SpecTec,
even though the W3C 2.0 text has `funcinst ::= … | {type functype, hostcode hostfunc}`
and the embedder interface is defined in terms of it. We parameterise the runtime
by a host type `H` and give `funcinst` a `code : FuncCode H` with
`FuncCode H ::= wasm Func | host H`, exactly as
`Silmaril.Wasm.Execution.Core.Runtime` does for 3.0, because the embedder
interface and the V1/V2/Core subset theorems need it. With `H = Empty` the
extension is vacuous: `FuncCode Empty` is isomorphic to `Func`. Other modelling
differences are unchanged; see `docs/projects/wasm-semantics.md`.

**On `$growmemory`'s bound.** `5-runtime-aux:130` requires `i' <= 2^16`
(non-strict) while `5-runtime-aux:123` requires `i' < 2^32` (strict) for
`$growtable`. We transcribe both literally. They agree with the reference
interpreter's *validation* bounds (`interpreter/valid/valid.ml:206,216`:
`0x1_0000` pages for an i32 memory, `0xffff_ffff` entries for an i32 table). The
interpreter's `runtime/memory.ml:27-30` additionally refuses to *allocate* more
than `0xffff` pages, one page below the spec bound; since growth is allowed to
fail for any reason (`8-reduction:604-605` is a `-1` rule with no premise), that is
an allocation limit and not a different bound, and `test/core/memory_grow.wast:11`
only observes that growing to `0x10000` pages may fail.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.Execution.Memory (Bytes pageSize writeBytes)

/-! ## Addresses (`4-runtime:5-20`) -/

/-- `addr = nat` (`4-runtime:5`). -/
abbrev Addr := Nat

/-- `funcaddr = addr` (`4-runtime:6`). -/
abbrev FuncAddr := Addr
/-- `globaladdr = addr` (`4-runtime:7`). -/
abbrev GlobalAddr := Addr
/-- `tableaddr = addr` (`4-runtime:8`). -/
abbrev TableAddr := Addr
/-- `memaddr = addr` (`4-runtime:9`). -/
abbrev MemAddr := Addr
/-- `elemaddr = addr` (`4-runtime:10`). -/
abbrev ElemAddr := Addr
/-- `dataaddr = addr` (`4-runtime:11`). -/
abbrev DataAddr := Addr
/-- `hostaddr = addr` (`4-runtime:12`). -/
abbrev HostAddr := Addr

/-- `externaddr ::= FUNC funcaddr | GLOBAL globaladdr | TABLE tableaddr | MEM memaddr`
(`4-runtime:25`). -/
inductive ExternAddr where
  | func (a : FuncAddr)
  | global (a : GlobalAddr)
  | table (a : TableAddr)
  | mem (a : MemAddr)
  deriving DecidableEq, Repr

namespace ExternAddr

/-- `$funcsxa(externaddr*)` (`5-runtime-aux:25`). -/
def funcs (xs : List ExternAddr) : List FuncAddr :=
  xs.filterMap fun | .func a => some a | _ => none

/-- `$globalsxa(externaddr*)` (`5-runtime-aux:29`). -/
def globals (xs : List ExternAddr) : List GlobalAddr :=
  xs.filterMap fun | .global a => some a | _ => none

/-- `$tablesxa(externaddr*)` (`5-runtime-aux:33`). -/
def tables (xs : List ExternAddr) : List TableAddr :=
  xs.filterMap fun | .table a => some a | _ => none

/-- `$memsxa(externaddr*)` (`5-runtime-aux:37`). -/
def mems (xs : List ExternAddr) : List MemAddr :=
  xs.filterMap fun | .mem a => some a | _ => none

end ExternAddr

/-! ## Values (`4-runtime:37-51`) -/

/-- `num ::= CONST numtype num_(numtype)` (`4-runtime:37`): a number type
together with the bits of a value of that type. -/
structure NumVal where
  type : NumType
  bits : BitVec type.width
  deriving DecidableEq, Repr

/-- `vec ::= VCONST vectype vec_(vectype)` (`4-runtime:39`). The only `vectype`
is `V128`, so the payload is the whole content. -/
abbrev VecVal := BitVec 128

/-- `ref ::= REF.NULL reftype | REF.FUNC_ADDR funcaddr | REF.HOST_ADDR hostaddr`
(`4-runtime:41`). -/
inductive Ref where
  | null (t : RefType)
  | funcAddr (a : FuncAddr)
  | hostAddr (a : HostAddr)
  deriving DecidableEq, Repr

/-- `val ::= num | vec | ref` (`4-runtime:43`). -/
inductive Val where
  | num (v : NumVal)
  | vec (b : VecVal)
  | ref (r : Ref)
  deriving DecidableEq, Repr

namespace Val

def i32 (b : BitVec 32) : Val := .num ⟨.int .i32, b⟩
def i64 (b : BitVec 64) : Val := .num ⟨.int .i64, b⟩
def f32 (b : BitVec 32) : Val := .num ⟨.float .f32, b⟩
def f64 (b : BitVec 64) : Val := .num ⟨.float .f64, b⟩

/-- The value type of a runtime value. Wasm 2.0 has no concrete reference types
and no subtyping, so this is total and store-independent: a function address is a
`funcref` and a host address is an `externref`. -/
def type : Val → ValType
  | .num v => .num v.type
  | .vec _ => .vec .v128
  | .ref (.null t) => .ref t
  | .ref (.funcAddr _) => .ref .funcref
  | .ref (.hostAddr _) => .ref .externref

end Val

/-- `result ::= _VALS val* | TRAP` (`4-runtime:46`). -/
inductive Result where
  | values (vs : List Val)
  | trap
  deriving DecidableEq, Repr

/-! ## Instances (`4-runtime:60-99`) -/

/-- `exportinst ::= { NAME name, ADDR externaddr }` (`4-runtime:78`). -/
structure ExportInst where
  name : String
  addr : ExternAddr
  deriving DecidableEq, Repr

/-- `moduleinst ::= { TYPES functype*, FUNCS funcaddr*, GLOBALS globaladdr*,
TABLES tableaddr*, MEMS memaddr*, ELEMS elemaddr*, DATAS dataaddr*,
EXPORTS exportinst* }` (`4-runtime:82`). -/
structure ModuleInst where
  types : List FuncType := []
  funcs : List FuncAddr := []
  globals : List GlobalAddr := []
  tables : List TableAddr := []
  mems : List MemAddr := []
  elems : List ElemAddr := []
  datas : List DataAddr := []
  exports : List ExportInst := []
  deriving DecidableEq, Repr

/-- The code of a function instance. SpecTec 2.0 has only `CODE func`; `host` is
the host-function extension described in the module docstring. -/
inductive FuncCode (H : Type) where
  | wasm (f : Func)
  | host (h : H)
  deriving Repr

/-- `funcinst ::= { TYPE functype, MODULE moduleinst, CODE func }`
(`4-runtime:60`), with `CODE` extended to `FuncCode H`. -/
structure FuncInst (H : Type) where
  type : FuncType
  module : ModuleInst
  code : FuncCode H
  deriving Repr

/-- `globalinst ::= { TYPE globaltype, VALUE val }` (`4-runtime:64`). -/
structure GlobalInst where
  type : GlobalType
  value : Val
  deriving DecidableEq, Repr

/-- `tableinst ::= { TYPE tabletype, REFS ref* }` (`4-runtime:67`). -/
structure TableInst where
  type : TableType
  refs : List Ref
  deriving DecidableEq, Repr

/-- `meminst ::= { TYPE memtype, BYTES byte* }` (`4-runtime:70`). -/
structure MemInst where
  type : MemoryType
  bytes : Bytes
  deriving DecidableEq, Repr

/-- `eleminst ::= { TYPE elemtype, REFS ref* }` (`4-runtime:73`); `elemtype` is
`reftype` (`1-syntax:175-176`). -/
structure ElemInst where
  type : ElemType
  refs : List Ref
  deriving DecidableEq, Repr

/-- `datainst ::= { BYTES byte* }` (`4-runtime:76`). -/
structure DataInst where
  bytes : Bytes
  deriving DecidableEq, Repr

/-! ## Configurations (`4-runtime:104-121`) -/

/-- `store ::= { FUNCS funcinst*, GLOBALS globalinst*, TABLES tableinst*,
MEMS meminst*, ELEMS eleminst*, DATAS datainst* }` (`4-runtime:104`). -/
structure Store (H : Type) where
  funcs : List (FuncInst H) := []
  globals : List GlobalInst := []
  tables : List TableInst := []
  mems : List MemInst := []
  elems : List ElemInst := []
  datas : List DataInst := []
  deriving Repr

/-- `frame ::= { LOCALS val*, MODULE moduleinst }` (`4-runtime:112`). Unlike Core
3.0 every 2.0 local is defaultable, so locals are plain values, not `Option`s. -/
structure Frame where
  locals : List Val := []
  module : ModuleInst := {}
  deriving DecidableEq, Repr

/-- `state ::= store; frame` (`4-runtime:116`). -/
structure State (H : Type) where
  store : Store H
  frame : Frame
  deriving Repr

/-! ## Administrative instructions (`4-runtime:128-135`) -/

/-- `admininstr ::= instr | REF.FUNC_ADDR funcaddr | REF.HOST_ADDR hostaddr |
CALL_ADDR funcaddr | LABEL_ n {instr*} admininstr* | FRAME_ n {frame} admininstr*
| TRAP` (`4-runtime:128`). -/
inductive Admin where
  /-- `instr`: a source instruction (`4-runtime:129`). -/
  | plain (i : Instr)
  /-- `REF.FUNC_ADDR funcaddr` (`4-runtime:130`). -/
  | refFuncAddr (a : FuncAddr)
  /-- `REF.HOST_ADDR hostaddr` (`4-runtime:131`). -/
  | refHostAddr (a : HostAddr)
  /-- `CALL_ADDR funcaddr` (`4-runtime:132`). -/
  | callAddr (a : FuncAddr)
  /-- `LABEL_ n {instr*} admininstr*` (`4-runtime:133`). -/
  | label (n : Nat) (cont : List Instr) (body : List Admin)
  /-- `FRAME_ n {frame} admininstr*` (`4-runtime:134`). -/
  | frame (n : Nat) (f : Frame) (body : List Admin)
  /-- `TRAP` (`4-runtime:135`). -/
  | trap
  deriving Repr

/-- `config ::= state; admininstr*` (`4-runtime:117`), with `state = store; frame`
spelled out as two fields. -/
structure Config (H : Type) where
  store : Store H
  frame : Frame
  code : List Admin
  deriving Repr

variable {H : Type}

/-- The `state` part of a configuration (`$store`/`$frame`, `5-runtime-aux:48-52`). -/
def Config.state (c : Config H) : State H := ⟨c.store, c.frame⟩

/-- `z; admininstr*`. -/
def State.config (z : State H) (code : List Admin) : Config H := ⟨z.store, z.frame, code⟩

@[simp] theorem State.store_config (z : State H) (code : List Admin) :
    (z.config code).store = z.store := rfl

@[simp] theorem State.frame_config (z : State H) (code : List Admin) :
    (z.config code).frame = z.frame := rfl

@[simp] theorem State.code_config (z : State H) (code : List Admin) :
    (z.config code).code = code := rfl

@[simp] theorem Config.state_config (c : Config H) : c.state.config c.code = c := rfl

/-! ## Host functions

`HostOutcome` and `HostSemantics` instantiate the shared
`Silmaril.Wasm.Execution.Host.Outcome` and `.Semantics`, also used by Core 3.0
and V1/Lime1. -/

/-- The outcome of a host call: a new store together with a result, or divergence,
as the shared `Silmaril.Wasm.Execution.Host.Outcome`. -/
abbrev HostOutcome (H : Type) :=
  Silmaril.Wasm.Execution.Host.Outcome (Store H) Result

/-- `$hostcall(hostfunc, store, val*)` as a relation: a host function may be
non-deterministic and may diverge. The shared
`Silmaril.Wasm.Execution.Host.Semantics`. -/
abbrev HostSemantics (H : Type) :=
  Silmaril.Wasm.Execution.Host.Semantics H (Store H) Val Result

/-! ## Values as administrative instructions

`4-runtime:43` makes `val` a subset of `admininstr` by way of
`num | vec | ref ⊆ instr | REF.FUNC_ADDR _ | REF.HOST_ADDR _`: `CONST`, `VCONST`
and `REF.NULL` are *source* instructions, while `REF.FUNC_ADDR` and
`REF.HOST_ADDR` are administrative. -/

/-- The inclusion `val ⊆ admininstr`. -/
def Val.toAdmin : Val → Admin
  | .num ⟨.int t, b⟩ => .plain (.intConst t b)
  | .num ⟨.float t, b⟩ => .plain (.floatConst t b)
  | .vec b => .plain (.vecConst b)
  | .ref (.null t) => .plain (.refNull t)
  | .ref (.funcAddr a) => .refFuncAddr a
  | .ref (.hostAddr a) => .refHostAddr a

/-- Recognise an administrative instruction that is a value. -/
def Admin.val? : Admin → Option Val
  | .plain (.intConst t b) => some (.num ⟨.int t, b⟩)
  | .plain (.floatConst t b) => some (.num ⟨.float t, b⟩)
  | .plain (.vecConst b) => some (.vec b)
  | .plain (.refNull t) => some (.ref (.null t))
  | .refFuncAddr a => some (.ref (.funcAddr a))
  | .refHostAddr a => some (.ref (.hostAddr a))
  | _ => none

/-- `val` as a side condition on an administrative instruction. -/
def Admin.isVal (a : Admin) : Bool := a.val?.isSome

/-- The sequence `val*` as `admininstr*`. -/
def vals (vs : List Val) : List Admin := vs.map Val.toAdmin

/-- `expr = instr*` as `admininstr*`. -/
def expression (es : Expr) : List Admin := es.map .plain

/-- `result` as `admininstr*`: `_VALS val*` is `val*` and `TRAP` is `TRAP`
(`4-runtime:46`; used by the embedder and by `Eval_expr`). -/
def Result.toAdmin : Result → List Admin
  | .values vs => vals vs
  | .trap => [.trap]

@[simp] theorem Admin.val?_toAdmin (v : Val) : v.toAdmin.val? = some v := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> rfl

@[simp] theorem Admin.isVal_toAdmin (v : Val) : v.toAdmin.isVal = true := by
  simp [Admin.isVal]

/-- `Admin.val?` is the partial inverse of `Val.toAdmin`. -/
theorem Admin.toAdmin_of_val? {a : Admin} {v : Val} (h : a.val? = some v) :
    v.toAdmin = a := by
  unfold Admin.val? at h
  split at h <;> first
    | (injection h with h; subst h; rfl)
    | exact absurd h (by simp)

theorem Admin.val?_eq_some_iff (a : Admin) (v : Val) : a.val? = some v ↔ v.toAdmin = a :=
  ⟨Admin.toAdmin_of_val?, fun h => h ▸ Admin.val?_toAdmin v⟩

theorem Val.toAdmin_injective : Function.Injective Val.toAdmin := by
  intro a b h
  have hb := Admin.val?_toAdmin a
  rw [h, Admin.val?_toAdmin] at hb
  exact (Option.some.inj hb).symm

theorem vals_injective : Function.Injective vals :=
  fun _ _ h => List.map_injective_iff.mpr Val.toAdmin_injective h

@[simp] theorem vals_append (xs ys : List Val) : vals (xs ++ ys) = vals xs ++ vals ys :=
  List.map_append

@[simp] theorem vals_length (xs : List Val) : (vals xs).length = xs.length := List.length_map _

@[simp] theorem vals_nil : vals [] = [] := rfl

@[simp] theorem vals_cons (v : Val) (vs : List Val) : vals (v :: vs) = v.toAdmin :: vals vs := rfl

@[simp] theorem expression_append (xs ys : Expr) :
    expression (xs ++ ys) = expression xs ++ expression ys :=
  List.map_append

@[simp] theorem expression_length (xs : Expr) : (expression xs).length = xs.length :=
  List.length_map _

/-! ## Default values (`5-runtime-aux:7-15`)

Every 2.0 value type has a default: `$default_` is total, unlike the 3.0
`$default_` which is undefined on non-nullable reference types. -/

/-- `$default_(valtype)` (`5-runtime-aux:7`). `$fzero(N) = POS (SUBNORM 0)`
(`1-syntax:69`) is the all-zero bit pattern. -/
def defaultVal : ValType → Val
  | .num (.int t) => .num ⟨.int t, 0⟩
  | .num (.float t) => .num ⟨.float t, 0⟩
  | .vec _ => .vec 0
  | .ref t => .ref (.null t)

@[simp] theorem Val.type_defaultVal (t : ValType) : (defaultVal t).type = t := by
  rcases t with (_ | _) | _ | _ <;> rfl

/-! ## Module instance lookups

The `f.MODULE.XS[x]` half of the accessors of `5-runtime-aux:83-89`. -/

namespace ModuleInst

/-- `f.MODULE.TYPES[x]`. -/
def type? (m : ModuleInst) (x : TypeIdx) : Option FuncType := m.types[x.toNat]?
/-- `f.MODULE.FUNCS[x]`. -/
def funcAddr? (m : ModuleInst) (x : FuncIdx) : Option FuncAddr := m.funcs[x.toNat]?
/-- `f.MODULE.GLOBALS[x]`. -/
def globalAddr? (m : ModuleInst) (x : GlobalIdx) : Option GlobalAddr := m.globals[x.toNat]?
/-- `f.MODULE.TABLES[x]`. -/
def tableAddr? (m : ModuleInst) (x : TableIdx) : Option TableAddr := m.tables[x.toNat]?
/-- `f.MODULE.MEMS[x]`. -/
def memAddr? (m : ModuleInst) (x : MemIdx) : Option MemAddr := m.mems[x.toNat]?
/-- `f.MODULE.ELEMS[x]`. -/
def elemAddr? (m : ModuleInst) (x : ElemIdx) : Option ElemAddr := m.elems[x.toNat]?
/-- `f.MODULE.DATAS[x]`. -/
def dataAddr? (m : ModuleInst) (x : DataIdx) : Option DataAddr := m.datas[x.toNat]?

end ModuleInst

/-! ## Store lookups and updates (address-indexed)

These are the total, address-indexed primitives; the index-indexed spec functions
`$func`, `$global`, … and `$with_global`, … are built from them below. -/

namespace Store

/-- `s.FUNCS[a]`. -/
def funcInst? (s : Store H) (a : FuncAddr) : Option (FuncInst H) := s.funcs[a]?
/-- `s.GLOBALS[a]`. -/
def globalInst? (s : Store H) (a : GlobalAddr) : Option GlobalInst := s.globals[a]?
/-- `s.TABLES[a]`. -/
def tableInst? (s : Store H) (a : TableAddr) : Option TableInst := s.tables[a]?
/-- `s.MEMS[a]`. -/
def memInst? (s : Store H) (a : MemAddr) : Option MemInst := s.mems[a]?
/-- `s.ELEMS[a]`. -/
def elemInst? (s : Store H) (a : ElemAddr) : Option ElemInst := s.elems[a]?
/-- `s.DATAS[a]`. -/
def dataInst? (s : Store H) (a : DataAddr) : Option DataInst := s.datas[a]?

/-- `s[.FUNCS[a] = fi]`. -/
def setFuncInst (s : Store H) (a : FuncAddr) (fi : FuncInst H) : Store H :=
  { s with funcs := s.funcs.set a fi }

/-- `s[.GLOBALS[a] = gi]`. -/
def setGlobalInst (s : Store H) (a : GlobalAddr) (gi : GlobalInst) : Store H :=
  { s with globals := s.globals.set a gi }

/-- `s[.TABLES[a] = ti]`. -/
def setTableInst (s : Store H) (a : TableAddr) (ti : TableInst) : Store H :=
  { s with tables := s.tables.set a ti }

/-- `s[.MEMS[a] = mi]`. -/
def setMemInst (s : Store H) (a : MemAddr) (mi : MemInst) : Store H :=
  { s with mems := s.mems.set a mi }

/-- `s[.ELEMS[a] = ei]`. -/
def setElemInst (s : Store H) (a : ElemAddr) (ei : ElemInst) : Store H :=
  { s with elems := s.elems.set a ei }

/-- `s[.DATAS[a] = di]`. -/
def setDataInst (s : Store H) (a : DataAddr) (di : DataInst) : Store H :=
  { s with datas := s.datas.set a di }

end Store

/-- `ti[.REFS[i] = r]`. SpecTec's array update is partial; `List.set` is the
identity out of range, and `Step/table.set-val` (`8-reduction:410-412`) carries
`i < |$table(z, x).REFS|`. -/
def TableInst.setRef (ti : TableInst) (i : Nat) (r : Ref) : TableInst :=
  { ti with refs := ti.refs.set i r }

/-- `mi[.BYTES[i : j] = b*]`, defined exactly when `|b*| = j` and the range
`[i, i+j)` is inside the memory. -/
def MemInst.writeBytes? (mi : MemInst) (i j : Nat) (bs : Bytes) : Option MemInst :=
  if bs.size = j then (writeBytes mi.bytes i bs).map fun b => { mi with bytes := b }
  else none

/-! ## Frame lookups and updates -/

namespace Frame

/-- `f.LOCALS[x]`, the frame half of `$local` (`5-runtime-aux:90`). -/
def local? (f : Frame) (x : LocalIdx) : Option Val := f.locals[x.toNat]?

/-- `f[.LOCALS[x] = v]`, the frame half of `$with_local` (`5-runtime-aux:104`). -/
def setLocal (f : Frame) (x : LocalIdx) (v : Val) : Frame :=
  { f with locals := f.locals.set x.toNat v }

/-- The frame built by `Step_read/call_addr` (`8-reduction:131-135`):
`{LOCALS val^k ($default_(t))*, MODULE mm}`. -/
def forCall (m : ModuleInst) (args : List Val) (locals : List ValType) : Frame :=
  ⟨args ++ locals.map defaultVal, m⟩

@[simp] theorem locals_forCall (m : ModuleInst) (args : List Val) (locals : List ValType) :
    (forCall m args locals).locals = args ++ locals.map defaultVal := rfl

@[simp] theorem module_forCall (m : ModuleInst) (args : List Val) (locals : List ValType) :
    (forCall m args locals).module = m := rfl

end Frame

/-- The memory index `0`: every memory rule of `8-reduction` writes `$mem(z, 0)`,
since 2.0 allows at most one memory. -/
def memIdx0 : MemIdx := ⟨⟨0, Nat.two_pow_pos 32⟩⟩

/-! ## State accessors (`5-runtime-aux:55-90`) -/

namespace State

/-- `$moduleinst(z) = f.MODULE` (`5-runtime-aux:72`). -/
def moduleInst (z : State H) : ModuleInst := z.frame.module

/-- `$funcaddr(z) = f.MODULE.FUNCS` (`5-runtime-aux:56`). -/
def funcAddrs (z : State H) : List FuncAddr := z.frame.module.funcs

/-- `$funcinst(z) = s.FUNCS` (`5-runtime-aux:66`). -/
def funcInsts (z : State H) : List (FuncInst H) := z.store.funcs
/-- `$globalinst(z) = s.GLOBALS` (`5-runtime-aux:67`). -/
def globalInsts (z : State H) : List GlobalInst := z.store.globals
/-- `$tableinst(z) = s.TABLES` (`5-runtime-aux:68`). -/
def tableInsts (z : State H) : List TableInst := z.store.tables
/-- `$meminst(z) = s.MEMS` (`5-runtime-aux:69`). -/
def memInsts (z : State H) : List MemInst := z.store.mems
/-- `$eleminst(z) = s.ELEMS` (`5-runtime-aux:70`). -/
def elemInsts (z : State H) : List ElemInst := z.store.elems
/-- `$datainst(z) = s.DATAS` (`5-runtime-aux:71`). -/
def dataInsts (z : State H) : List DataInst := z.store.datas

/-- `$type(z, x) = f.MODULE.TYPES[x]` (`5-runtime-aux:83`). -/
def type? (z : State H) (x : TypeIdx) : Option FuncType := z.frame.module.type? x

/-- `$local(z, x) = f.LOCALS[x]` (`5-runtime-aux:90`). -/
def local? (z : State H) (x : LocalIdx) : Option Val := z.frame.local? x

/-- `$func(z, x) = s.FUNCS[f.MODULE.FUNCS[x]]` (`5-runtime-aux:84`). -/
def func? (z : State H) (x : FuncIdx) : Option (FuncInst H) := do
  z.store.funcInst? (← z.frame.module.funcAddr? x)

/-- `$global(z, x) = s.GLOBALS[f.MODULE.GLOBALS[x]]` (`5-runtime-aux:85`). -/
def global? (z : State H) (x : GlobalIdx) : Option GlobalInst := do
  z.store.globalInst? (← z.frame.module.globalAddr? x)

/-- `$table(z, x) = s.TABLES[f.MODULE.TABLES[x]]` (`5-runtime-aux:86`). -/
def table? (z : State H) (x : TableIdx) : Option TableInst := do
  z.store.tableInst? (← z.frame.module.tableAddr? x)

/-- `$mem(z, x) = s.MEMS[f.MODULE.MEMS[x]]` (`5-runtime-aux:87`). -/
def mem? (z : State H) (x : MemIdx) : Option MemInst := do
  z.store.memInst? (← z.frame.module.memAddr? x)

/-- `$elem(z, x) = s.ELEMS[f.MODULE.ELEMS[x]]` (`5-runtime-aux:88`). -/
def elem? (z : State H) (x : ElemIdx) : Option ElemInst := do
  z.store.elemInst? (← z.frame.module.elemAddr? x)

/-- `$data(z, x) = s.DATAS[f.MODULE.DATAS[x]]` (`5-runtime-aux:89`). -/
def data? (z : State H) (x : DataIdx) : Option DataInst := do
  z.store.dataInst? (← z.frame.module.dataAddr? x)

/-! ## State updates (`5-runtime-aux:95-111`)

Each update is `Option`-valued exactly where SpecTec's is partial: both the
index resolution `f.MODULE.XS[x]` and the store indexing `s.XS[a]` must succeed.
`$with_local` is the one exception: `8-reduction:380-381` guards nothing, and
`List.set` is the identity out of range, so the update is total. -/

/-- `$with_local(z, x, v) = s; f[.LOCALS[x] = v]` (`5-runtime-aux:104`). -/
def withLocal (z : State H) (x : LocalIdx) (v : Val) : State H :=
  { z with frame := z.frame.setLocal x v }

/-- `$with_global(z, x, v) = s[.GLOBALS[f.MODULE.GLOBALS[x]].VALUE = v]; f`
(`5-runtime-aux:105`). -/
def withGlobal (z : State H) (x : GlobalIdx) (v : Val) : Option (State H) := do
  let a ← z.frame.module.globalAddr? x
  let gi ← z.store.globalInst? a
  return { z with store := z.store.setGlobalInst a { gi with value := v } }

/-- `$with_table(z, x, i, r) = s[.TABLES[f.MODULE.TABLES[x]].REFS[i] = r]; f`
(`5-runtime-aux:106`). -/
def withTable (z : State H) (x : TableIdx) (i : Nat) (r : Ref) : Option (State H) := do
  let a ← z.frame.module.tableAddr? x
  let ti ← z.store.tableInst? a
  return { z with store := z.store.setTableInst a (ti.setRef i r) }

/-- `$with_tableinst(z, x, ti) = s[.TABLES[f.MODULE.TABLES[x]] = ti]; f`
(`5-runtime-aux:107`). -/
def withTableInst (z : State H) (x : TableIdx) (ti : TableInst) : Option (State H) := do
  let a ← z.frame.module.tableAddr? x
  let _ ← z.store.tableInst? a
  return { z with store := z.store.setTableInst a ti }

/-- `$with_mem(z, x, i, j, b*) = s[.MEMS[f.MODULE.MEMS[x]].BYTES[i : j] = b*]; f`
(`5-runtime-aux:108`). `j` is the length of `b*`; the update is undefined unless
`|b*| = j` and `[i, i+j)` lies inside the memory. -/
def withMem (z : State H) (x : MemIdx) (i j : Nat) (bs : Bytes) : Option (State H) := do
  let a ← z.frame.module.memAddr? x
  let mi ← z.store.memInst? a
  let mi' ← mi.writeBytes? i j bs
  return { z with store := z.store.setMemInst a mi' }

/-- `$with_meminst(z, x, mi) = s[.MEMS[f.MODULE.MEMS[x]] = mi]; f`
(`5-runtime-aux:109`). -/
def withMemInst (z : State H) (x : MemIdx) (mi : MemInst) : Option (State H) := do
  let a ← z.frame.module.memAddr? x
  let _ ← z.store.memInst? a
  return { z with store := z.store.setMemInst a mi }

/-- `$with_elem(z, x, r*) = s[.ELEMS[f.MODULE.ELEMS[x]].REFS = r*]; f`
(`5-runtime-aux:110`). -/
def withElem (z : State H) (x : ElemIdx) (rs : List Ref) : Option (State H) := do
  let a ← z.frame.module.elemAddr? x
  let ei ← z.store.elemInst? a
  return { z with store := z.store.setElemInst a { ei with refs := rs } }

/-- `$with_data(z, x, b*) = s[.DATAS[f.MODULE.DATAS[x]].BYTES = b*]; f`
(`5-runtime-aux:111`). -/
def withData (z : State H) (x : DataIdx) (bs : Bytes) : Option (State H) := do
  let a ← z.frame.module.dataAddr? x
  let _ ← z.store.dataInst? a
  return { z with store := z.store.setDataInst a ⟨bs⟩ }

end State

/-! ## Growing (`5-runtime-aux:116-131`)

Both functions are `hint(partial)`. Note the asymmetry, transcribed literally:
`$growtable` needs `i' < 2^32` (**strict**) while `$growmemory` needs
`i' <= 2^16` (**non-strict**); both also replace the type's *minimum* by the new
size `i'`. -/

/-- `$growtable(ti, n, r)` (`5-runtime-aux:119`). -/
def TableInst.grow? (ti : TableInst) (n : Nat) (r : Ref) : Option TableInst :=
  if h : ti.refs.length + n < 2 ^ 32 ∧
      ti.type.limits.max.all (fun j => ti.refs.length + n ≤ j.val) = true then
    some { type := { ti.type with
             limits := { ti.type.limits with min := ⟨ti.refs.length + n, h.1⟩ } },
           refs := ti.refs ++ List.replicate n r }
  else none

/-- `$growmemory(mi, n)` (`5-runtime-aux:126`), in pages of `64 * $Ki` bytes. -/
def MemInst.grow? (mi : MemInst) (n : Nat) : Option MemInst :=
  if h : mi.bytes.size / pageSize + n ≤ 2 ^ 16 ∧
      mi.type.limits.max.all (fun j => mi.bytes.size / pageSize + n ≤ j.val) = true then
    some { type := { limits := { mi.type.limits with
             min := ⟨mi.bytes.size / pageSize + n, Nat.lt_of_le_of_lt h.1 (by decide)⟩ } },
           bytes := mi.bytes ++ ⟨Array.replicate (n * pageSize) 0⟩ }
  else none

/-- The size of a memory instance in pages. -/
def MemInst.pages (mi : MemInst) : Nat := mi.bytes.size / pageSize

/-! ## Properties -/

@[simp] theorem State.store_withLocal (z : State H) (x : LocalIdx) (v : Val) :
    (z.withLocal x v).store = z.store := rfl

@[simp] theorem State.moduleInst_withLocal (z : State H) (x : LocalIdx) (v : Val) :
    (z.withLocal x v).moduleInst = z.moduleInst := rfl

/-- `$with_local` writes the local it is given, provided the index is in range. -/
theorem State.local?_withLocal (z : State H) (x : LocalIdx) (v : Val)
    (h : x.toNat < z.frame.locals.length) : (z.withLocal x v).local? x = some v := by
  simp [State.withLocal, State.local?, Frame.setLocal, Frame.local?, h]

/-- `$with_local` leaves every other local alone. -/
theorem State.local?_withLocal_ne (z : State H) (x y : LocalIdx) (v : Val) (h : y ≠ x) :
    (z.withLocal x v).local? y = z.local? y := by
  have hne : y.toNat ≠ x.toNat := fun hh => h (Silmaril.Wasm.Idx.toNat_injective hh)
  simp only [State.withLocal, State.local?, Frame.setLocal, Frame.local?]
  exact List.getElem?_set_ne (Ne.symm hne)

/-- `$with_global` writes the global it is given. -/
theorem State.global?_withGlobal {z z' : State H} {x : GlobalIdx} {v : Val}
    (h : z.withGlobal x v = some z') :
    ∃ gi, z.global? x = some gi ∧ z'.global? x = some { gi with value := v } := by
  unfold State.withGlobal at h
  cases ha : z.frame.module.globalAddr? x with
  | none => simp [ha] at h
  | some a =>
    cases hi : z.store.globalInst? a with
    | none => simp [ha, hi] at h
    | some gi =>
      simp [ha, hi] at h
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
      subst h
      exact ⟨gi, by simp [State.global?, ha, hi],
        by simp [State.global?, ha, Store.globalInst?, Store.setGlobalInst,
          List.getElem?_set_self hlt]⟩

@[simp] theorem State.frame_withGlobal {z z' : State H} {x : GlobalIdx} {v : Val}
    (h : z.withGlobal x v = some z') : z'.frame = z.frame := by
  unfold State.withGlobal at h
  cases ha : z.frame.module.globalAddr? x with
  | none => simp [ha] at h
  | some a =>
    cases hi : z.store.globalInst? a with
    | none => simp [ha, hi] at h
    | some gi =>
      simp [ha, hi] at h
      subst h
      rfl

/-- `$with_global` does not disturb the frame, hence neither `$type` nor `$local`. -/
theorem State.type?_withGlobal {z z' : State H} {x : GlobalIdx} {v : Val}
    (h : z.withGlobal x v = some z') (y : TypeIdx) : z'.type? y = z.type? y := by
  simp [State.type?, State.frame_withGlobal h]

/-- `$with_tableinst` installs the table instance it is given. -/
theorem State.table?_withTableInst {z z' : State H} {x : TableIdx} {ti : TableInst}
    (h : z.withTableInst x ti = some z') : z'.table? x = some ti := by
  unfold State.withTableInst at h
  cases ha : z.frame.module.tableAddr? x with
  | none => simp [ha] at h
  | some a =>
    cases hi : z.store.tableInst? a with
    | none => simp [ha, hi] at h
    | some ti0 =>
      simp [ha, hi] at h
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
      subst h
      simp [State.table?, ha, Store.tableInst?, Store.setTableInst,
        List.getElem?_set_self hlt]

/-- `$with_table` updates one entry of the addressed table. -/
theorem State.table?_withTable {z z' : State H} {x : TableIdx} {i : Nat} {r : Ref}
    (h : z.withTable x i r = some z') :
    ∃ ti, z.table? x = some ti ∧ z'.table? x = some (ti.setRef i r) := by
  unfold State.withTable at h
  cases ha : z.frame.module.tableAddr? x with
  | none => simp [ha] at h
  | some a =>
    cases hi : z.store.tableInst? a with
    | none => simp [ha, hi] at h
    | some ti =>
      simp [ha, hi] at h
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
      subst h
      exact ⟨ti, by simp [State.table?, ha, hi],
        by simp [State.table?, ha, Store.tableInst?, Store.setTableInst,
          List.getElem?_set_self hlt]⟩

/-- `$with_meminst` installs the memory instance it is given. -/
theorem State.mem?_withMemInst {z z' : State H} {x : MemIdx} {mi : MemInst}
    (h : z.withMemInst x mi = some z') : z'.mem? x = some mi := by
  unfold State.withMemInst at h
  cases ha : z.frame.module.memAddr? x with
  | none => simp [ha] at h
  | some a =>
    cases hi : z.store.memInst? a with
    | none => simp [ha, hi] at h
    | some mi0 =>
      simp [ha, hi] at h
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
      subst h
      simp [State.mem?, ha, Store.memInst?, Store.setMemInst,
        List.getElem?_set_self hlt]

/-- `$with_mem` writes within the memory, so it preserves the memory's type and
size. -/
theorem State.mem?_withMem {z z' : State H} {x : MemIdx} {i j : Nat} {bs : Bytes}
    (h : z.withMem x i j bs = some z') :
    ∃ mi mi', z.mem? x = some mi ∧ z'.mem? x = some mi' ∧ mi'.type = mi.type ∧
      mi'.bytes.size = mi.bytes.size := by
  unfold State.withMem at h
  cases ha : z.frame.module.memAddr? x with
  | none => simp [ha] at h
  | some a =>
    cases hi : z.store.memInst? a with
    | none => simp [ha, hi] at h
    | some mi =>
      cases hw : mi.writeBytes? i j bs with
      | none => simp [ha, hi, hw] at h
      | some mi' =>
        simp [ha, hi, hw] at h
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
        subst h
        refine ⟨mi, mi', by simp [State.mem?, ha, hi],
          by simp [State.mem?, ha, Store.memInst?, Store.setMemInst,
            List.getElem?_set_self hlt], ?_, ?_⟩
        · unfold MemInst.writeBytes? at hw
          split at hw
          · cases hb : writeBytes mi.bytes i bs with
            | none => simp [hb] at hw
            | some b => simp only [hb, Option.map_some, Option.some.injEq] at hw; subst hw; rfl
          · exact absurd hw (by simp)
        · unfold MemInst.writeBytes? at hw
          split at hw
          · cases hb : writeBytes mi.bytes i bs with
            | none => simp [hb] at hw
            | some b =>
              simp only [hb, Option.map_some, Option.some.injEq] at hw
              subst hw
              exact Silmaril.Wasm.Execution.Memory.writeBytes_size mi.bytes bs b i hb
          · exact absurd hw (by simp)

/-- `$with_elem` installs the references it is given. -/
theorem State.elem?_withElem {z z' : State H} {x : ElemIdx} {rs : List Ref}
    (h : z.withElem x rs = some z') :
    ∃ ei, z.elem? x = some ei ∧ z'.elem? x = some { ei with refs := rs } := by
  unfold State.withElem at h
  cases ha : z.frame.module.elemAddr? x with
  | none => simp [ha] at h
  | some a =>
    cases hi : z.store.elemInst? a with
    | none => simp [ha, hi] at h
    | some ei =>
      simp [ha, hi] at h
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
      subst h
      exact ⟨ei, by simp [State.elem?, ha, hi],
        by simp [State.elem?, ha, Store.elemInst?, Store.setElemInst,
          List.getElem?_set_self hlt]⟩

/-- `$with_data` installs the bytes it is given. -/
theorem State.data?_withData {z z' : State H} {x : DataIdx} {bs : Bytes}
    (h : z.withData x bs = some z') : z'.data? x = some ⟨bs⟩ := by
  unfold State.withData at h
  cases ha : z.frame.module.dataAddr? x with
  | none => simp [ha] at h
  | some a =>
    cases hi : z.store.dataInst? a with
    | none => simp [ha, hi] at h
    | some di =>
      simp [ha, hi] at h
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
      subst h
      simp [State.data?, ha, Store.dataInst?, Store.setDataInst,
        List.getElem?_set_self hlt]

theorem TableInst.grow?_refs_length {ti ti' : TableInst} {n : Nat} {r : Ref}
    (h : ti.grow? n r = some ti') : ti'.refs.length = ti.refs.length + n := by
  unfold TableInst.grow? at h
  split at h
  · injection h with h; subst h; simp
  · simp at h

/-- `$growtable` sets the new minimum to the new size, which is `< 2^32`
(`5-runtime-aux:123`, a **strict** inequality). -/
theorem TableInst.grow?_min {ti ti' : TableInst} {n : Nat} {r : Ref}
    (h : ti.grow? n r = some ti') :
    ti'.type.limits.min.val = ti.refs.length + n ∧ ti.refs.length + n < 2 ^ 32 := by
  unfold TableInst.grow? at h
  split at h
  next hc => injection h with h; subst h; exact ⟨rfl, hc.1⟩
  next => simp at h

/-- `$growtable` preserves the element type and the maximum. -/
theorem TableInst.grow?_type {ti ti' : TableInst} {n : Nat} {r : Ref}
    (h : ti.grow? n r = some ti') :
    ti'.type.element = ti.type.element ∧ ti'.type.limits.max = ti.type.limits.max := by
  unfold TableInst.grow? at h
  split at h
  · injection h with h; subst h; exact ⟨rfl, rfl⟩
  · simp at h

/-- `$growtable` respects the declared maximum when there is one. -/
theorem TableInst.grow?_le_max {ti ti' : TableInst} {n : Nat} {r : Ref} {j : Fin (2 ^ 32)}
    (h : ti.grow? n r = some ti') (hmax : ti.type.limits.max = some j) :
    ti.refs.length + n ≤ j.val := by
  unfold TableInst.grow? at h
  split at h
  next hc => rw [hmax] at hc; simpa using hc.2
  next => simp at h

/-- `$growtable` appends `r^n`. -/
theorem TableInst.grow?_refs {ti ti' : TableInst} {n : Nat} {r : Ref}
    (h : ti.grow? n r = some ti') : ti'.refs = ti.refs ++ List.replicate n r := by
  unfold TableInst.grow? at h
  split at h
  · injection h with h; subst h; rfl
  · simp at h

theorem MemInst.grow?_size {mi mi' : MemInst} {n : Nat} (h : mi.grow? n = some mi') :
    mi'.bytes.size = mi.bytes.size + n * pageSize := by
  unfold MemInst.grow? at h
  split at h
  · injection h with h
    subst h
    simp only [ByteArray.size_append]
    change mi.bytes.size + (Array.replicate (n * pageSize) (0 : UInt8)).size = _
    rw [Array.size_replicate]
  · simp at h

/-- `$growmemory` sets the new minimum to the new page count, which is `≤ 2^16`
(`5-runtime-aux:130`, a **non-strict** inequality). -/
theorem MemInst.grow?_min {mi mi' : MemInst} {n : Nat} (h : mi.grow? n = some mi') :
    mi'.type.limits.min.val = mi.bytes.size / pageSize + n ∧
      mi.bytes.size / pageSize + n ≤ 2 ^ 16 := by
  unfold MemInst.grow? at h
  split at h
  next hc => injection h with h; subst h; exact ⟨rfl, hc.1⟩
  next => simp at h

/-- `$growmemory` preserves the maximum. -/
theorem MemInst.grow?_max {mi mi' : MemInst} {n : Nat} (h : mi.grow? n = some mi') :
    mi'.type.limits.max = mi.type.limits.max := by
  unfold MemInst.grow? at h
  split at h
  · injection h with h; subst h; rfl
  · simp at h

/-- `$growmemory` respects the declared maximum when there is one. -/
theorem MemInst.grow?_le_max {mi mi' : MemInst} {n : Nat} {j : Fin (2 ^ 32)}
    (h : mi.grow? n = some mi') (hmax : mi.type.limits.max = some j) :
    mi.bytes.size / pageSize + n ≤ j.val := by
  unfold MemInst.grow? at h
  split at h
  next hc => rw [hmax] at hc; simpa using hc.2
  next => simp at h

/-- On a page-aligned memory, `$growmemory` agrees with the shared byte-array
growth `Silmaril.Wasm.Execution.Memory.grow?`: the bound `i' ≤ 2^16` of
`5-runtime-aux:130` and that function's `maxPages = 2^16` coincide, and so do the
two maximum checks. `Memory.grow?` additionally demands page alignment (SpecTec
instead truncates in `|b*| / (64 * $Ki)`) and does not touch the memory *type*,
which is why `$growmemory` is transcribed directly rather than defined through
it. -/
theorem MemInst.grow?_bytes {mi mi' : MemInst} {n : Nat}
    (align : mi.bytes.size % pageSize = 0) (h : mi.grow? n = some mi') :
    Silmaril.Wasm.Execution.Memory.grow? mi.bytes (mi.type.limits.max.map Fin.val) n
      = some mi'.bytes := by
  have hle := (MemInst.grow?_min h).2
  unfold MemInst.grow? at h
  split at h
  next hc =>
    injection h with h
    subst h
    have hmax : (mi.type.limits.max.map Fin.val).isNone = true ∨
        mi.bytes.size / pageSize + n ≤ (mi.type.limits.max.map Fin.val).getD 0 := by
      cases hm : mi.type.limits.max with
      | none => exact Or.inl (by simp)
      | some j =>
        refine Or.inr ?_
        rw [hm] at hc
        simpa using hc.2
    unfold Silmaril.Wasm.Execution.Memory.grow?
    split
    · rfl
    · next hcon => exact absurd ⟨align, hle, hmax⟩ hcon
  next => simp at h

end Silmaril.Wasm.V2.Execution
