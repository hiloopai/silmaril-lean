module

public import Silmaril.Wasm.Component.Conformance.DecodeP3.Defs
public import Silmaril.Wasm.Component.Reference.Defs

/-!
# Host instances for root imports: wasmtime's `.wast` host on the reference machine

wasmtime's `.wast` runner (`crates/wast` at tag `v50.0.0`, `spectest.rs`
`link_component_spectest`, `wast.rs` `register_wasmtime` and `WastContext::module`) links
every root component against one `Linker` holding

* root functions `host-return-two: func() -> u32` (returns 2) and
  `host-echo-u32: func(u32) -> u32` (concurrent, returns its argument);
* an instance `host` with `return-three` (3), a nested instance `nested` with
  `return-four` (4), a core module `simple-module` (global `g = 100`, function `f() = 101`),
  host resources `resource1` (also exported as `resource1-again`, the same type) and
  `resource2`, `[constructor]resource1: func(u32) -> own<resource1>`,
  `[static]resource1.assert: func(own<resource1>, u32)` (asserts the rep),
  `[static]resource1.last-drop`, `[static]resource1.drops: func() -> u32` (the resource1
  destructor's counters), `[method]resource1.simple: func(borrow<resource1>, u32)`,
  `[method]resource1.take-borrow: func(borrow, borrow)`,
  `[method]resource1.take-own: func(borrow, own)`, the concurrent `never-return: func()`,
  `return-two-slowly: func() -> s32`, `echo-slowly: func(u32) -> u32` (both resolve after
  a `yield_now`), `[method]resource1.never-return: func(borrow<resource1>)`, and
  `return-hi: func() -> string`;
* an instance `wasmtime` with `set-max-table-capacity: func(u32)` and `gc: func()`;
* for every *named* root component instance of the script (`(component $foo …)`), an
  instance `foo` with the core modules and resources it exports (wasmtime reflects only
  those; its functions are not reachable through the linker).

wasmtime does not require empty instance imports to be supplied ("empty instances don't need
to be supplied by the host, even recursively", `import.wast`).

## The model

`linkArgs` builds the root arguments (`Instantiate.Exports`) of a component from its
validated type (`Reference.ComponentType`): each root import, walked against the host tree
(`HostItem`), becomes an item of the store:

* a host function becomes a host function value `CFuncInst.host ft fn` (`storeHostFunc`).
  The host's own signature (`HostFn.sig`) is compared with the expected function type with
  parameter names erased and the `async` flag ignored (as wasmtime's `func_wrap`, which has
  no parameter names); on a match the value gets the *expected* type, otherwise its own
  type, which the machine's import check (`Instantiate.importTypeCheck`) then rejects;
* a host resource becomes a fresh host resource type (`ResourceType` with `impl = none`), one
  per host resource identity and link; the resource variable the import binds is mapped to it,
  so the function types after it mention it;
* a non-resource type export is supplied at the expected type (wasmtime's linker does not
  define value types; they are checked structurally);
* host instances are supplied export by export as the expected type asks; a missing export
  is left out (the import check reports it); an instance the host lacks is synthesized when
  it needs nothing from the host (only value types, equalities with resources bound earlier,
  and such instances: wasmtime's "empty instances need not be supplied");
* an item of another sort than the expected one is supplied at its own type, so the
  machine's import check rejects it.

wasmtime's `Linker` also compares the types of supplied core modules, which the copied
machine checks by sort only: `moduleCheck` does that comparison, and a mismatch traps
`hostTrap "link error: …"` before instantiation starts. Otherwise nothing about the import
check is trusted to `linkArgs`: the root arguments go through the
copied `Instantiate.instantiateRootCall` with its pre-check and per-import `importTypeCheck`.
A missing or ill-typed import is the model's `hostTrap` (wasmtime: a link error; the copied
`InstantiateTraps` documents the deviation).

`hostImpl` answers the host functions as REF run_tests' `mk_host_func` with a synchronous body
(`on_start`, then `on_resolve`), except:

* `never-return` and `[method]resource1.never-return` never resolve; their `on_cancel`
  (`CancelRef.host n`, `n` the caller record) resolves them with `on_resolve(None)`
  (wasmtime drops the host future and reports `RETURN_CANCELLED`);
* `return-two-slowly` and `echo-slowly` resolve later: the result is queued in the host
  state (`HostSt.pending`) and the runner resolves the oldest queued call by a host program
  (`resolvePending`, a `HostEvent.run`) when no guest step or tick is possible; cancelling a
  queued call resolves it with `on_resolve(None)`;
* host destructors: wasmtime registers a destructor with `resource1` (it counts the
  drops and records the last representation in a state shared by the whole linker) and a no-op
  one with `resource2`. REF's `ResourceType` has none for host types (`impl = None` runs
  nothing), so `hostResource` models a host destructor as a component of its own: a fresh
  instance `impl` holding the host function `dtorResource1` lowered into it as its core
  `dtor`. Dropping an owned handle then takes REF's foreign-type path of
  `canon_resource_drop` (a synchronous `canon_lower` of `canon_lift(impl, dtor)`), which ends
  in the host function; `[static]resource1.drops`/`last-drop` read the counters (`stateful`).
  The runner carries the counters from store to store, as wasmtime's linker shares them;
* `wasmtime.set-max-table-capacity n` records `n`; from then on a host call (and the runner,
  at the end of each top-level call) traps `capacityTrap` when the instances' handle tables
  hold more than `n` entries (`overCapacity`). wasmtime's table is store-wide and checked at
  every insertion; the model checks only at those points, so a short peak above `n` between
  two of them is not seen, while a leak (entries never freed) is;
* a failed host assertion (`assert`, `simple`, `take-borrow`, `take-own`) is a
  `hostTrap` (wasmtime panics, which its runner reports as a trap).

Not claimed: that this host is wasmtime's (it is a transcription of the Rust above, checked
only by the conformance scripts), nor anything about the timing of deferred resolutions
beyond "after the guest has nothing else to do".
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Conformance

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Value

/-- The core engine: Core 3.0 with memory growth never failing. -/
abbrev Eng : CoreEngine := core3 Silmaril.Wasm.SingleThreaded.neverFail

/-- An item of the host's linker namespace. -/
inductive HostItem where
  /-- A host function (index into `HostFn.all`). -/
  | func (fn : Nat)
  /-- A host resource type; items with the same key are the same type. -/
  | resource (key : String)
  | module (m : Silmaril.Wasm.Module)
  | inst (items : List (String × HostItem))

/-- The host functions. -/
inductive HostFn where
  | hostReturnTwo | hostEchoU32 | returnThree | returnFour
  | ctorResource1 | assertResource1 | lastDropResource1 | dropsResource1
  | simpleResource1 | takeBorrow | takeOwn | neverReturn | returnTwoSlowly | echoSlowly
  | neverReturnResource1 | returnHi | setMaxTableCapacity | gc
  /-- The destructors of `resource1` and `resource2` (wasmtime registers them with the
  resource types; here they are host functions, see `hostResource`). -/
  | dtorResource1 | dtorResource2
  deriving DecidableEq, Repr, Inhabited

namespace HostFn

def all : List HostFn :=
  [hostReturnTwo, hostEchoU32, returnThree, returnFour, ctorResource1, assertResource1,
    lastDropResource1, dropsResource1, simpleResource1, takeBorrow, takeOwn, neverReturn,
    returnTwoSlowly, echoSlowly, neverReturnResource1, returnHi, setMaxTableCapacity, gc,
    dtorResource1, dtorResource2]

def toNat (f : HostFn) : Nat := (all.idxOf? f).getD 0

def ofNat? (n : Nat) : Option HostFn := all[n]?

/-- Host function ids name host functions faithfully. -/
theorem ofNat?_toNat (f : HostFn) : ofNat? f.toNat = some f := by cases f <;> rfl

/-- The signature of a host function, given the host's `resource1` type `r` (parameter names
are placeholders: they are not compared). -/
def sig (r : RtId) : HostFn → WIT.FuncType Empty RtId
  | hostReturnTwo | returnThree | returnFour | dropsResource1 | lastDropResource1 =>
    ⟨[], some (.prim .u32), false⟩
  | hostEchoU32 | echoSlowly => ⟨[("a", .prim .u32)], some (.prim .u32), false⟩
  | ctorResource1 => ⟨[("rep", .prim .u32)], some (.own r), false⟩
  | assertResource1 => ⟨[("r", .own r), ("rep", .prim .u32)], none, false⟩
  | simpleResource1 => ⟨[("self", .borrow r), ("rep", .prim .u32)], none, false⟩
  | takeBorrow => ⟨[("self", .borrow r), ("b", .borrow r)], none, false⟩
  | takeOwn => ⟨[("self", .borrow r), ("b", .own r)], none, false⟩
  | neverReturn | gc => ⟨[], none, false⟩
  | returnTwoSlowly => ⟨[], some (.prim .s32), false⟩
  | neverReturnResource1 => ⟨[("self", .borrow r)], none, false⟩
  | returnHi => ⟨[], some (.prim .string), false⟩
  | setMaxTableCapacity => ⟨[("c", .prim .u32)], none, false⟩
  | dtorResource1 | dtorResource2 => ⟨[("rep", .prim .u32)], none, false⟩

end HostFn

/-- The parameter and result types of a function type (names and `async` erased). -/
def shape (ft : WIT.FuncType Empty RtId) :
    List (WIT.ValType Empty RtId) × Option (WIT.ValType Empty RtId) :=
  (ft.params.map (·.2), ft.result)

/-- The core module `simple-module` of wasmtime's `host` instance:
`(module (global (export "g") i32 i32.const 100) (func (export "f") (result i32) i32.const 101))`
(bytes written by `wasm-tools parse` 1.262.0). -/
def simpleModuleBytes : ByteArray := ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f,
  0x03, 0x02, 0x01, 0x00,
  0x06, 0x07, 0x01, 0x7f, 0x00, 0x41, 0xe4, 0x00, 0x0b,
  0x07, 0x09, 0x02, 0x01, 0x67, 0x03, 0x00, 0x01, 0x66, 0x00, 0x00,
  0x0a, 0x07, 0x01, 0x05, 0x00, 0x41, 0xe5, 0x00, 0x0b]⟩

/-- The resource key of wasmtime's `resource1` (also `resource1-again`). -/
def resource1Key : String := "host/resource1"

/-- The fixed part of wasmtime's linker namespace. -/
def baseHost : List (String × HostItem) :=
  let f (x : HostFn) : HostItem := .func x.toNat
  [("host-echo-u32", f .hostEchoU32), ("host-return-two", f .hostReturnTwo),
   ("host", .inst ([
      ("return-three", f .returnThree),
      ("nested", .inst [("return-four", f .returnFour)])] ++
      (match Silmaril.Wasm.Binary.Core.decode? simpleModuleBytes with
        | some m => [("simple-module", .module m)]
        | none => []) ++
      [("resource1", .resource resource1Key), ("resource2", .resource "host/resource2"),
      ("resource1-again", .resource resource1Key),
      ("[constructor]resource1", f .ctorResource1),
      ("[static]resource1.assert", f .assertResource1),
      ("[static]resource1.last-drop", f .lastDropResource1),
      ("[static]resource1.drops", f .dropsResource1),
      ("[method]resource1.simple", f .simpleResource1),
      ("[method]resource1.take-borrow", f .takeBorrow),
      ("[method]resource1.take-own", f .takeOwn),
      ("never-return", f .neverReturn),
      ("return-two-slowly", f .returnTwoSlowly),
      ("echo-slowly", f .echoSlowly),
      ("[method]resource1.never-return", f .neverReturnResource1),
      ("return-hi", f .returnHi)])),
   ("wasmtime", .inst [("set-max-table-capacity", f .setMaxTableCapacity), ("gc", f .gc)])]

/-- The host state of the machine: registered instances, deferred resolutions, calls that
never return, and the export map of the last root instantiation. -/
structure HostSt where
  /-- Named root instances registered so far (modules and resources only). -/
  registered : List (String × HostItem) := []
  /-- Deferred resolutions, oldest first: caller record and results. -/
  pending : List (CallerId × List Val) := []
  /-- Calls that never resolve unless cancelled. -/
  parked : List CallerId := []
  /-- The root exports of the last instantiation run by `instantiateLinkedProg`. -/
  lastExports : List (String × Instantiate.ItemVal Eng) := []
  /-- wasmtime's `resource1` destructor counters (`ResourceState.drops`, `last_drop`, both
  `0` initially; wasmtime keeps them in the linker, so the runner carries them from store to
  store). -/
  drops : Nat := 0
  lastDrop : Nat := 0
  /-- The capacity `wasmtime.set-max-table-capacity` set (`none`: wasmtime's default, no
  bound below the model's `Table.maxLength`). -/
  maxTableCapacity : Option Nat := none

instance : Inhabited HostSt := ⟨{}⟩

/-! ## Linking -/

/-- The state of a link: host resource keys and resource variables bound so far. -/
structure LinkSt where
  rts : List (String × RtId) := []
  vars : List (Nat × RtId) := []
  /-- Link errors found by `moduleCheck` (wasmtime's `Linker` type check of core modules). -/
  errors : List String := []

/-- An `RtId` no store allocates, for resource variables the host does not bind. -/
def unboundRt (v : Nat) : RtId := ⟨1000000000 + v⟩

/-- The `RtId` of a resource variable. -/
def LinkSt.var (ls : LinkSt) (v : Nat) : RtId := (ls.vars.lookup v).getD (unboundRt v)

/-- The destructor of the host resource of key `k`: wasmtime's `resource1` destructor counts
drops, `resource2`'s does nothing; other host resources (registered instances) have none. -/
def dtorOf? (k : String) : Option HostFn :=
  if k = resource1Key then some .dtorResource1
  else if k = "host/resource2" then some .dtorResource2
  else none

/-- A fresh host resource type. REF's `ResourceType` has no host destructor (`impl` is a
component instance, `dtor` a core function, and `destructorCall` runs nothing when `impl` is
`None`), so a host destructor `f` is modelled as a component: a fresh, otherwise unused
instance `impl` whose core function `dtor` is the host function `f` lowered into it (REF
`Store.lower`). Dropping an owned handle then runs REF's `canon_resource_drop` path for a
foreign resource type: a synchronous `canon_lower` of `canon_lift(impl, dtor)`, whose core
code calls `f` with the representation. -/
def hostResource (f? : Option HostFn) : P Eng HostSt RtId := do
  match f? with
  | none => allocObj ArenaField.resourceTypes ({ impl := none } : ResourceType Eng)
  | some f =>
    let impl ← Instantiate.allocInst (E := Eng) (σ := HostSt)
    let r1 : RtId := ⟨0⟩
    let fid ← storeHostFunc (E := Eng) (σ := HostSt) (f.sig r1) ⟨f.toNat⟩
    let a ← storeLower (E := Eng) (σ := HostSt) fid {} impl
    allocObj ArenaField.resourceTypes
      ({ impl := some impl, rep := .i32, dtor := some a } : ResourceType Eng)

/-- The host resource type of key `k`, allocated on first use. -/
def resourceOf (k : String) (ls : LinkSt) : P Eng HostSt (RtId × LinkSt) := do
  match ls.rts.lookup k with
  | some r => pure (r, ls)
  | none =>
    let r ← hostResource (dtorOf? k)
    pure (r, { ls with rts := (k, r) :: ls.rts })

/-! ### wasmtime's `Linker` check of core module imports

The copied machine checks a supplied core module by sort only (`Instantiate.importTypeCheck`);
wasmtime's `Linker` also compares module types (`crates/wasmtime/src/runtime/component/
matching.rs`, `TypeChecker::module`): every expected export exists in the supplied module with
a subtype, and every import of the supplied module is among the expected imports with a
supertype. `moduleCheck` is that comparison over the closed Core 3.0 extern types (subtyping
`Eng.ExternSub`, the core engine's own); its messages follow wasmtime's. -/

/-- The kind of a core extern type, as wasmtime names it. -/
def externKind (x : Validation.Core3Extern) : String :=
  match x.1 with
  | .func _ => "func" | .table _ => "table" | .mem _ => "memory" | .global _ => "global"
  | .tag _ => "tag"

/-- `act` may be used where `exp` is expected. -/
def externSub (act exp : Validation.Core3Extern) : Bool :=
  let inst : ∀ a b : Eng.ExternType, Decidable (Eng.ExternSub a b) := inferInstance
  @decide (Eng.ExternSub act exp) (inst act exp)

/-- wasmtime's module type check of the supplied module `m` against the expected type. -/
def moduleCheck (exp : Types.CoreModuleType Validation.Core3Extern) (m : Silmaril.Wasm.Module) :
    Option String :=
  match Validation.core3ModuleType? m with
  | none => some "supplied core module does not validate"
  | some act =>
    let exportErr := exp.exports.findSome? fun (n, x) =>
      match act.exports.lookup n with
      | none => some s!"module export `{n}` not defined"
      | some y =>
        if externKind y != externKind x then some s!"expected {externKind x} found {externKind y}"
        else if externSub y x then none
        else some s!"export `{n}` has the wrong type"
    match exportErr with
    | some e => some e
    | none => act.imports.findSome? fun ((mn, n), y) =>
      match exp.imports.lookup (mn, n) with
      | none => some s!"module import `{mn}::{n}` not defined"
      | some x => if externSub x y then none else some s!"module import `{mn}::{n}` has the wrong type"

mutual

/-- Supply host item `h` at its own type (no expected type to follow). -/
def natural (ls : LinkSt) : HostItem → P Eng HostSt (Instantiate.ItemVal Eng × LinkSt)
  | .func fn => do
    let (r1, ls) ← resourceOf resource1Key ls
    let f := (HostFn.ofNat? fn).getD .gc
    let id ← storeHostFunc (E := Eng) (σ := HostSt) (f.sig r1) ⟨fn⟩
    pure (.func id, ls)
  | .resource k => do
    let (r, ls) ← resourceOf k ls
    pure (.type (.resource r), ls)
  | .module m => pure (.coreModule m, ls)
  | .inst items => do
    let (es, ls) ← naturalList ls items
    pure (.instance es, ls)

def naturalList (ls : LinkSt) :
    List (String × HostItem) → P Eng HostSt (List (String × Instantiate.ItemVal Eng) × LinkSt)
  | [] => pure ([], ls)
  | (n, h) :: hs => do
    let (v, ls) ← natural ls h
    let (vs, ls) ← naturalList ls hs
    pure ((n, v) :: vs, ls)

end

/-- The run-time form of an expected type definition (resource variables mapped). -/
def typeAt (ls : LinkSt) (t : Types.TypeDef Nat Validation.Core3Extern) :
    Types.TypeDef RtId Validation.Core3Extern :=
  t.map ls.var

mutual

/-- Supply the import (or instance export) `e`, from host item `h?` (`none`: the host has no
item of that name). `none`: nothing is supplied. `fuel` bounds the instance nesting depth
(`linkArgs` passes `linkDepth`; deeper instances are not supplied). -/
def supply (fuel : Nat) (ls : LinkSt) (e : Types.Entity Nat Validation.Core3Extern)
    (h? : Option HostItem) : P Eng HostSt (Option (Instantiate.ItemVal Eng) × LinkSt) :=
  match fuel with
  | 0 => pure (none, ls)
  | fuel + 1 =>
  match e, h? with
  | .type (.resource v), some (.resource k) => do
    let (r, ls) ← resourceOf k ls
    pure (some (.type (.resource r)), { ls with vars := (v, r) :: ls.vars })
  | .type (.resource v), none =>
    -- an equality with a resource bound earlier needs no host item
    pure ((ls.vars.lookup v).map (.type ∘ .resource), ls)
  | .type t, none => pure (some (.type (typeAt ls t)), ls)
  | .func ft, some (.func fn) => do
    let (r1, ls) ← resourceOf resource1Key ls
    let f := (HostFn.ofNat? fn).getD .gc
    let exp := ft.mapResource ls.var
    let ty := if shape exp = shape (f.sig r1) then exp else f.sig r1
    let id ← storeHostFunc (E := Eng) (σ := HostSt) ty ⟨fn⟩
    pure (some (.func id), ls)
  | .module mt, some (.module m) =>
    pure (some (.coreModule m),
      match moduleCheck mt m with
      | some e => { ls with errors := ls.errors ++ [e] }
      | none => ls)
  | .instance it, some (.inst items) => do
    let (es, ls) ← supplyList fuel ls it.exports items
    pure (some (.instance es), ls)
  | .instance it, none => do
    -- an instance that needs nothing from the host (only value types, equalities and such
    -- instances) is synthesized, as wasmtime does not require it to be defined
    let (es, ls) ← supplyList fuel ls it.exports []
    pure (if es.length = it.exports.length then some (.instance es) else none, ls)
  | _, none => pure (none, ls)
  | _, some h => do
    let (v, ls) ← natural ls h
    pure (some v, ls)

/-- Supply the exports `es` of an expected instance type from the host items `items`. -/
def supplyList (fuel : Nat) (ls : LinkSt)
    (es : List (String × Types.Entity Nat Validation.Core3Extern))
    (items : List (String × HostItem)) :
    P Eng HostSt (List (String × Instantiate.ItemVal Eng) × LinkSt) :=
  match es with
  | [] => pure ([], ls)
  | (n, e) :: es => do
    let (v?, ls) ← supply fuel ls e (items.lookup n)
    let (vs, ls) ← supplyList fuel ls es items
    pure ((v?.map fun v => [(n, v)]).getD [] ++ vs, ls)

end

/-- The instance nesting depth `linkArgs` supplies. -/
def linkDepth : Nat := 64

/-- The host namespace: wasmtime's fixed items, then the registered instances (a registered
name shadows a fixed one, as a later `Linker` definition would be rejected anyway). -/
def hostTree (st : HostSt) : List (String × HostItem) := st.registered ++ baseHost

/-- **The root arguments of a component of type `ct`**, and the link errors of
`moduleCheck`. -/
def linkArgs (ct : Reference.ComponentType) :
    P Eng HostSt (Instantiate.Exports Eng × List String) := do
  let st ← hostGet
  let (es, ls) ← supplyList linkDepth {} ct.imports (hostTree st)
  pure (es, ls.errors)

/-! ## Registration of named instances -/

/-- The registered form of a root export map: its core modules and resources. -/
def registerItems (name : String) (es : List (String × Instantiate.ItemVal Eng)) :
    List (String × HostItem) :=
  es.filterMap fun
    | (n, .coreModule m) => some (n, .module m)
    | (n, .type (.resource r)) => some (n, .resource s!"registered/{name}/{r.idx}")
    | _ => none

/-- Register the last root instance under `name` (wasmtime `WastContext::module`). -/
def register (name : String) (st : HostSt) : HostSt :=
  { st with registered :=
      (name, .inst (registerItems name st.lastExports)) :: st.registered.filter (·.1 != name) }

/-! ## Instantiation and deferred resolution as host programs -/

/-- Root instantiation with linked arguments: `linkArgs`, then the copied `instantiateProg`'s
body (`nesting_depth` bracket, `instantiateRootCall`, the instantiation observation), and the
export map kept in the host state. -/
def instantiateLinkedProg (c : Reference.Core3Component) (ct : Reference.ComponentType) :
    P Eng HostSt (Ret Eng) := do
  let (args, errs) ← linkArgs ct
  match errs with
  | e :: _ => trap (.hostTrap s!"link error: {e}")
  | [] => pure ()
  modifyStore DispatchSt.incNestingSt
  let (inst, es) ← Instantiate.instantiateRootCall c args
  modifyStore DispatchSt.decNestingSt
  emit (instantiatedObs inst (funcExports es))
  let st ← hostGet
  hostSet { st with lastExports := es }
  pure .unit

/-- Resolve the oldest deferred host call (REF: the host calls `on_resolve` from its event
loop), bracketed by `nesting_depth` like `Store.tick`. -/
def resolvePending : P Eng HostSt (Ret Eng) := do
  let st ← hostGet
  match st.pending with
  | [] => pure .unit
  | (c, rs) :: rest =>
    hostSet { st with pending := rest }
    modifyStore DispatchSt.incNestingSt
    callUnit (.onResolve c (some rs))
    modifyStore DispatchSt.decNestingSt
    pure .unit

/-! ## Host functions -/

/-- The answer of a host function: resolve now, later, never, or trap. -/
inductive Answer where
  | now (rs : List Val)
  | later (rs : List Val)
  | never
  | fail (msg : String)
  | unmodelled (msg : String)

def u32Val (n : Nat) : Val := .int .u32 n

/-- The behaviour of host function `f` on arguments `args`. -/
def answer : HostFn → List Val → Answer
  | .hostReturnTwo, _ => .now [u32Val 2]
  | .returnThree, _ => .now [u32Val 3]
  | .returnFour, _ => .now [u32Val 4]
  | .hostEchoU32, [v] => .now [v]
  | .ctorResource1, [.int _ n] => .now [.own n.toNat]
  | .assertResource1, [.own r, .int _ n] =>
    if r = n.toNat then .now [] else .fail "resource1.assert: rep mismatch"
  | .simpleResource1, [.borrow r, .int _ n] =>
    if r = n.toNat then .now [] else .fail "resource1.simple: rep mismatch"
  | .takeBorrow, [.borrow _, .borrow _] => .now []
  | .takeOwn, [.borrow _, .own _] => .now []
  | .neverReturn, _ | .neverReturnResource1, _ => .never
  | .returnTwoSlowly, _ => .later [.int .s32 2]
  | .echoSlowly, [v] => .later [v]
  | .returnHi, _ => .now [.string ⟨⟨"hi", .utf8, 2⟩, .i32⟩]
  | .gc, _ => .now []
  | .dtorResource2, [_] => .now []
  | f, _ => .fail s!"host: unexpected arguments for {reprStr f}"

/-- The host functions that read or write the host state: the `resource1` destructor and its
counters (wasmtime's `ResourceState`; `AtomicU32`, so `drops` wraps at `2 ^ 32`) and
`set-max-table-capacity`. -/
def stateful (f : HostFn) (args : List Val) (st : HostSt) : Option (HostSt × List Val) :=
  match f, args with
  | .dropsResource1, [] => some (st, [u32Val st.drops])
  | .lastDropResource1, [] => some (st, [u32Val st.lastDrop])
  | .dtorResource1, [.int _ rep] =>
    some ({ st with drops := (st.drops + 1) % 2 ^ 32, lastDrop := rep.toNat }, [])
  | .setMaxTableCapacity, [.int _ n] => some ({ st with maxTableCapacity := some n.toNat }, [])
  | _, _ => none

/-- The number of entries of the instances' handle tables (resources, waitables, waitable
sets, error contexts): the model's counterpart of wasmtime's store-wide concurrent resource
table, whose capacity `set-max-table-capacity` bounds. -/
def liveHandles (s : CStore Eng) : Nat :=
  s.insts.foldl (fun n i => n + (i.handles.array.toList.filter Option.isSome).length) 0

/-- The store holds more handles than the capacity `set-max-table-capacity` set. -/
def overCapacity (s : CStore Eng) (st : HostSt) : Bool :=
  match st.maxTableCapacity with
  | some n => decide (n < liveHandles s)
  | none => false

/-- The trap of a full table (wasmtime: a `ResourceTableError::Full` error, which its runner
reports as a trap). -/
def capacityTrap : TrapReason := .hostTrap "resource table capacity exceeded"

/-- Host function `fn` called with caller record `c`. -/
def hostFunc (fn : HostFuncId) (c : CallerId) : P Eng HostSt (Ret Eng) := do
  match HostFn.ofNat? fn.idx with
  | none => internal "host: unknown host function"
  | some f =>
    let args ← callVals (.onStart c)
    let st ← hostGet
    let s ← getStore
    if overCapacity s st then trap capacityTrap
    match stateful f args st with
    | some (st', rs) =>
      hostSet st'
      callUnit (.onResolve c (some rs))
      pure (.cancel .none)
    | none =>
    match answer f args with
    | .now rs =>
      callUnit (.onResolve c (some rs))
      pure (.cancel .none)
    | .later rs =>
      let st ← hostGet
      hostSet { st with pending := st.pending ++ [(c, rs)] }
      pure (.cancel (.host c.idx))
    | .never =>
      let st ← hostGet
      hostSet { st with parked := st.parked ++ [c] }
      pure (.cancel (.host c.idx))
    | .fail msg => trap (.hostTrap msg)
    | .unmodelled msg => internal msg

/-- The host's `on_cancel` for caller record `n`: a parked or deferred call resolves with
`on_resolve(None)`; otherwise nothing (it has resolved already). -/
def hostCancel (n : Nat) : P Eng HostSt Unit := do
  let st ← hostGet
  let c : CallerId := ⟨n⟩
  if st.parked.contains c || st.pending.any (·.1 == c) then
    hostSet { st with parked := st.parked.filter (· != c),
                      pending := st.pending.filter (·.1 != c) }
    callUnit (.onResolve c none)

/-- **The host behaviour** of the conformance runner. -/
def hostImpl : HostImpl Eng HostSt :=
  { funcs := hostFunc, cancel := hostCancel }

end Silmaril.Wasm.Component.Conformance
