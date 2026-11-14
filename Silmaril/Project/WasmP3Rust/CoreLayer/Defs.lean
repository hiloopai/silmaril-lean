module

public import Silmaril.Project.WasmP3Rust.Den.Defs
public import Silmaril.Wasm.Component.Engine.Core3.Defs
public import Silmaril.Wasm.Binary.Core.Decode

/-!
# The core layer of a component, run by silmaril's Core 3.0 interpreter

`den Ks c` (`Silmaril.Project.WasmP3Rust.Den`) is parametric in a semantics `Ks c : CoreExec` of
the **core layer** of the component `c`. This module builds one from a real core Wasm
interpreter: silmaril's concrete Core 3.0 engine `core3 neverFail`
(`Silmaril.Wasm.Component.Engine.Core3`), whose instantiation `prepareE?` validates a module,
checks its arguments against its import types and allocates it, and whose internal step is the
computable interpreter step `Exec.stepI neverFail`.

## Instantiation (`layer c`)

`layer c` walks the sections of `c` in order and keeps the **core index spaces** of the
component (modules, instances, functions, tables, memories, globals) and a Core store:

* `core module` sections are decoded with silmaril's `decode?` (the decoder `parseStrict`
  uses);
* `canon` definitions other than `lift` add a core function, numbered as in
  `Den.spaces` (so the index `k` of `CoreExec.callOut` is the index `Den.builtin` reads);
* `alias core export i n` adds the export `n` of core instance `i` to the space of its sort;
* `core instance` sections: inline exports (`exports`), or `instantiate m args`, which
  resolves each import `(module, name)` of module `m` (in the import order of the module)
  through the argument instance named `module` and its export `name`. A core function defined
  by `canon` becomes a **host function** of the store the first time a module imports it
  (`allocHost`, at the type of that import), with host tag `k`, its index: the interpreter
  reports a call of it as a callout with tag `k`. Then `prepareE?` instantiates the module.
  Start functions are not run: `layer` fails on a module with one.

So the shim module, the main module and the fixup module of a `wit-component` output are
instantiated as the Component Model does, in order: the fixup module's active element segment
fills the shim's table with the host functions of the `canon` built-ins that need the main
module's memory (`waitable-set.poll`, `stream.write`, …), and a call from the main module to
a shim export reaches the host function through `call_indirect`.

## The `CoreExec` (`exec L`)

A configuration is the store and the running thread (`none` before the first entry):

* `enter c k args`: a new thread calling the function at index `k` of the core function space
  (an exported core function), with `args` as values of its parameter types (`i32`/`i64`
  values are the arguments modulo `2 ^ 32` / `2 ^ 64`);
* `step`: one interpreter step (`internalC (stepI neverFail)`);
* `callOut c k args`: the thread's status is a callout of the host function with tag `k`, with
  the arguments' bits as natural numbers;
* `resume c vs`: the thread resumes with `vs` as values of the result types of host function
  `k` (a trap if their number differs);
* `ret`, `trap`: the thread's status is a return with values, or a trap (an uncaught exception
  is a trap); a `stuck` status has no transition;
* `load`, `store`: the bytes of memory `0` of the core memory space (the memory the `canon`
  options of `wit-component` output name).

`coreKs c` is `exec` of `layer c` when instantiation succeeds; otherwise a core layer with no
entry (so `den` traps at the start).

## What is not modelled

* `memory.grow` never fails (`neverFail`, the deterministic profile of the engine).
* Start functions (none in the four examples).
* Core instances are instantiated once, before the first `run` (each `run` call of `den`
  starts from `init`, as `CoreExec` requires).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.CoreLayer

open Silmaril.Project.WasmP3Rust.Den
open Silmaril.Wasm.Component.BinaryP3 (Ast Section Canon)
open Silmaril.Wasm.Component.Binary (CoreInstanceExpr CoreSort CoreSortIdx Alias AliasTarget ItemSort
  Import ExternDesc)
open Silmaril.Wasm.Execution.Core (Store ExternAddr ModuleInst)
open Silmaril.Wasm.SingleThreaded (Thread)
open Silmaril.Wasm.Component.Engine (Status CallResult)

/-- The grow oracle of the engine: `memory.grow` never fails. -/
abbrev oracle : Silmaril.Wasm.SingleThreaded.GrowOracle := Silmaril.Wasm.SingleThreaded.neverFail

/-- The host tags of the store: the index of a `canon`-defined core function. -/
abbrev St : Type := Store Nat

/-! ## Core index spaces -/

/-- An entry of a core index space. -/
inductive Item where
  /-- An address of the store. -/
  | addr (x : ExternAddr)
  /-- The core function `k`, defined by `canon` (not yet a host function of the store). -/
  | canon (k : Nat)
  /-- Anything else (unsupported). -/
  | none
  deriving Inhabited

/-- **The core layer during instantiation**: the store and the core index spaces. -/
structure Layer where
  store : St := {}
  /-- Core modules (`none`: not decoded, or not a module of this component). -/
  modules : List (Option Silmaril.Wasm.Module) := []
  /-- Core instances, as their named exports. -/
  insts : List (List (String × Item)) := []
  funcs : List Item := []
  tables : List Item := []
  mems : List Item := []
  globals : List Item := []
  /-- Host functions allocated so far: index `k`, address, flat type. -/
  hosts : List (Nat × Nat × Silmaril.Wasm.V1.FuncType) := []

namespace Layer

/-- The item at `i` of the core space of sort `s`. -/
def item (L : Layer) (s : CoreSort) (i : Nat) : Item :=
  match s with
  | .func => L.funcs.getD i .none
  | .table => L.tables.getD i .none
  | .memory => L.mems.getD i .none
  | .global => L.globals.getD i .none
  | _ => .none

/-- Add an item to the core space of sort `s`. -/
def push (L : Layer) (s : CoreSort) (x : Item) : Layer :=
  match s with
  | .func => { L with funcs := L.funcs ++ [x] }
  | .table => { L with tables := L.tables ++ [x] }
  | .memory => { L with mems := L.mems ++ [x] }
  | .global => { L with globals := L.globals ++ [x] }
  | .module => { L with modules := L.modules ++ [none] }
  | .instance => { L with insts := L.insts ++ [[]] }
  | _ => L

/-- The export `n` of core instance `i`. -/
def instExport (L : Layer) (i : Nat) (n : String) : Item :=
  ((L.insts.getD i []).lookup n).getD .none

/-- The host function of the `canon`-defined core function `k`, allocated at the flat type of
the importing function type `d` the first time. -/
def host (L : Layer) (k : Nat) (d : Silmaril.Wasm.Validation.DefType) :
    Option (Layer × ExternAddr) :=
  match L.hosts.find? (·.1 = k) with
  | some (_, a, _) => some (L, .func a)
  | none =>
    match Silmaril.Wasm.SingleThreaded.flatType? d with
    | some ft =>
      let (s', a) := Silmaril.Wasm.SingleThreaded.allocHost L.store ft k
      some ({ L with store := s', hosts := L.hosts ++ [(k, a, ft)] }, .func a)
    | none => none

/-- Resolve one import `(module, name)` of type `τ` through the instantiation arguments. -/
def resolve (L : Layer) (args : List (String × Nat)) (mn nm : String)
    (τ : Silmaril.Wasm.Validation.CExternType) : Option (Layer × ExternAddr) :=
  match args.lookup mn with
  | some i =>
    match L.instExport i nm, τ with
    | .addr x, _ => some (L, x)
    | .canon k, .func d => L.host k d
    | _, _ => none
  | none => none

/-- Resolve the imports of a module, in order. -/
def resolveAll (args : List (String × Nat)) :
    Layer → List (String × String × Silmaril.Wasm.Component.Engine.Core3.ExtT) →
      Option (Layer × List ExternAddr)
  | L, [] => some (L, [])
  | L, (mn, nm, τ) :: is =>
    match L.resolve args mn nm τ.1 with
    | some (L', x) => (resolveAll args L' is).map fun (L'', xs) => (L'', x :: xs)
    | none => none

/-- `instantiate m args`: resolve the imports, then `prepareE?`; no start function. -/
def instantiate (L : Layer) (m : Nat) (args : List (String × Nat)) : Option Layer :=
  match L.modules.getD m none with
  | some mod =>
    match resolveAll args L (Silmaril.Wasm.Component.Engine.Core3.importTypesE mod) with
    | some (L', xs) =>
      match Silmaril.Wasm.Component.Engine.Core3.prepareE? L'.store mod xs with
      | some (s', inst, none) =>
        some { L' with store := s',
                       insts := L'.insts ++
                         [(Silmaril.Wasm.Component.Engine.Core3.instExports inst).map
                           fun (n, x) => (n, Item.addr x)] }
      | _ => none
    | none => none
  | none => none

/-- A core instance definition. -/
def coreInstance (L : Layer) : CoreInstanceExpr → Option Layer
  | .instantiate m args => L.instantiate m args
  | .exports es => some { L with insts := L.insts ++ [es.map fun (n, si) => (n, L.item si.sort si.idx)] }

/-- A `canon` definition: every one but `lift` defines a core function. -/
def canon (L : Layer) : Canon → Layer
  | .lift .. => L
  | _ => L.push .func (.canon L.funcs.length)

/-- An alias: core exports go to the space of their sort; other aliases of core sorts are
unsupported entries. -/
def addAlias (L : Layer) (a : Alias) : Layer :=
  match a.sort, a.target with
  | .core s, .coreExport i n => L.push s (L.instExport i n)
  | .core s, _ => L.push s .none
  | _, _ => L

/-- An import of a core module adds an (unsupported) module. -/
def import_ (L : Layer) (i : Import) : Layer :=
  match i.desc with
  | .coreModule _ => L.push .module .none
  | _ => L

/-- A section. -/
def section_ (L : Layer) : Section → Option Layer
  | .coreModule b => some { L with modules := L.modules ++ [Silmaril.Wasm.Binary.Core.decode? b] }
  | .coreInstances xs => xs.foldlM coreInstance L
  | .canons xs => some (xs.foldl canon L)
  | .aliases xs => some (xs.foldl addAlias L)
  | .imports xs => some (xs.foldl import_ L)
  | _ => some L

end Layer

/-- **The core layer of a component**, instantiated (`none` when a step fails). -/
def layer (c : Ast) : Option Layer := c.sections.foldlM Layer.section_ {}

/-! ## The `CoreExec` -/

/-- A configuration: the store and the running thread. -/
structure Conf where
  store : St
  thread : Option Thread

/-- A natural number as a value of the numeric type `t` (modulo `2 ^ width`). -/
def toVal (t : Silmaril.Wasm.NumType) (n : Nat) : Silmaril.Wasm.Execution.Runtime.Value :=
  ⟨t, BitVec.ofNat t.width n⟩

/-- The bits of a value. -/
def ofVal (v : Silmaril.Wasm.Execution.Runtime.Value) : Nat := v.bits.toNat

/-- Natural numbers as values of the types `ts`, if there are as many. -/
def vals? (ts : List Silmaril.Wasm.NumType) (ns : List Nat) :
    Option (List Silmaril.Wasm.Execution.Runtime.Value) :=
  if ts.length = ns.length then some (List.zipWith toVal ts ns) else none

/-- The arguments of a call of the function at address `a`. -/
def args? (s : St) (a : Nat) (ns : List Nat) : Option (List Silmaril.Wasm.Execution.Runtime.Value) :=
  match Silmaril.Wasm.Component.Engine.Core3.funcTypeE? s a with
  | some d =>
    match Silmaril.Wasm.SingleThreaded.flatType? d with
    | some ft => vals? ft.params ns
    | none => none
  | none => none

/-- The status of a configuration's thread. -/
def status (c : Conf) : Option (Status Nat) :=
  c.thread.map (Silmaril.Wasm.Component.Engine.Core3.statusE oracle c.store)

variable (L : Layer)

/-- The address of memory `0`. -/
def memAddr : Option Nat :=
  match L.mems.head? with
  | some (.addr (.mem a)) => some a
  | _ => none

/-- The answer `vs` to a callout of host function `k`: values of its result types, or a trap. -/
def answer (k : Nat) (vs : List Nat) : Silmaril.Wasm.SingleThreaded.CallResult :=
  match L.hosts.find? (·.1 = k) with
  | some (_, _, ft) =>
    match vals? ft.results vs with
    | some ws => .values (ws.map Silmaril.Wasm.SingleThreaded.ofFlat)
    | none => .trap
  | none => .trap

/-- Resume a thread parked at a callout. -/
def resume (c : Conf) (vs : List Nat) : Conf :=
  match c.thread, status c with
  | some t, some (.callout k _) =>
    { c with thread := some (Silmaril.Wasm.SingleThreaded.resume c.store t (answer L k vs)) }
  | _, _ => c

/-- **The core layer `L`, run by the Core 3.0 interpreter**, as a `CoreExec`. -/
def exec : CoreExec where
  Conf := Conf
  init := ⟨L.store, none⟩
  enter c k args :=
    match L.funcs.getD k .none with
    | .addr (.func a) =>
      (args? c.store a args).map fun vs => ⟨c.store, some (Thread.invokeFlat a vs)⟩
    | _ => none
  step c c' := ∃ t s' t', c.thread = some t ∧
    Silmaril.Wasm.SingleThreaded.internalC (Silmaril.Wasm.SingleThreaded.Exec.stepI oracle)
      (c.store, t) = some (s', t') ∧ c' = ⟨s', some t'⟩
  callOut c k args := ∃ fs, status c = some (.callout k fs) ∧ args = fs.map ofVal
  resume := resume L
  ret c vs := ∃ fs, status c = some (.returned (.values fs)) ∧ vs = fs.map ofVal
  trap c := status c = some (.returned .trap)
  load c p n :=
    match memAddr L with
    | some a => (Silmaril.Wasm.SingleThreaded.memRead? c.store a p n).map
        fun b => b.data.toList.map UInt8.toBitVec
    | none => none
  store c p bs :=
    match memAddr L with
    | some a => (Silmaril.Wasm.SingleThreaded.memWrite? c.store a p
        ⟨⟨bs.map UInt8.ofBitVec⟩⟩).map fun s => { c with store := s }
    | none => none

/-- A core layer with no entry (instantiation failed): `den` traps at the start. -/
def noCore : CoreExec where
  Conf := Unit
  init := ()
  enter _ _ _ := none
  step _ _ := False
  callOut _ _ _ := False
  resume c _ := c
  ret _ _ := False
  trap _ := False
  load _ _ _ := none
  store _ _ _ := none

/-- **The core semantics of components**: the core layer instantiated by `layer`, run by
silmaril's Core 3.0 interpreter. -/
def coreKs (c : Ast) : CoreExec :=
  match layer c with
  | some L => exec L
  | none => noCore

end Silmaril.Project.WasmP3Rust.CoreLayer

end
