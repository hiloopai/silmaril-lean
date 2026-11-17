module

public import Silmaril.Project.Shapes.WasmWast.Defs
public import Silmaril.Wasm.Execution.Core.Exec.ExternAddrCheck
public import Silmaril.Wasm.Execution.MemRep.Sim.Defs

/-!
# Standard problem shapes: linked WAST scripts with the closed `spectest` environment

The commands of a WAST script with several modules, imports, `register` and the `spectest` module
of the specification test suite, stated over the Core semantics `Step (profile o) Det.noHost`:

| name | statement |
|---|---|
| `silmaril.shapes.wasm.wast.link.returns_only` | `ReturnsOnly o pre act vs`: after the script prefix `pre`, some host-free normal form of the action `act` returns `vs`, and every one does |
| `silmaril.shapes.wasm.wast.link.traps_only` | `TrapsOnly o pre act`: the same with a trap |
| `silmaril.shapes.wasm.wast.link.unlinkable` | `Unlinkable o pre m`: after `pre`, `m` is valid and its imports cannot be linked: some import names no export of a registered instance, or the resolved external addresses do not have the import types (`ExternAddrOk`) |
| `silmaril.shapes.wasm.wast.link.uninstantiable` | `Uninstantiable o pre m`: after `pre`, `m` links and `instantiateOnce?` allocates it, and its start function traps, at every host-free normal form |

**The environment is a closed Wasm module, not a host.** The reference interpreter's `spectest`
(`interpreter/host/spectest.ml` of WebAssembly/spec) is modelled by the instance of the fixed
module `Spectest.module`, allocated once per script in the empty store and registered as
`"spectest"` (`Init`). Its globals, table, memory and limits are those of `spectest.ml`; its seven
print functions are Wasm functions of the same types whose bodies are empty: a call returns no
values and leaves the store unchanged (`Spectest.print_nf`, `….Thms`). What `spectest.ml` prints
is erased: no claim here is about an output trace. No `.host` function instance is ever
allocated, so every claim is about host-free reduction, and nothing here says that a context
cannot distinguish this module from a host implementation of `spectest`. The other difference
from `spectest.ml`: there, each import of a global or a print function allocates a fresh
instance, here every import of one name shares the one instance (the globals are immutable).

**Script state.** A context `Ctx` has the store, the registered names (`register`, most recent
first), the names of named modules (`module $name`) and the current module. `pre` lists the
commands before the claim, in order, from the context `Init`; each one changes the context as
the reference interpreter does when its assertion holds (`CmdRun`):

* `module`: `InstNF … (some (.values [])) …`: the module is valid (`ModuleOk m mt`), every import
  resolves to an export of a registered instance (`resolve?`), the resolved addresses have the
  import types (`ExternAddrOk`, the premise of the specification's `$instantiate`), the module is
  allocated and its segments initialised by `instantiateOnce?` (as in
  `Silmaril.Project.Shapes.WasmWast`), and the start call, if any, runs to a host-free normal form
  that returns no values: the context gets its store, and the instance becomes current (and
  named);
* `register name t`: the instance `t` is registered as `name`;
* an action (`invoke` or `get`, on the current or a named instance), whatever its expectation: it
  runs to a host-free normal form that is a result (`ActNF`), whose store is the next one, so stores
  persist across modules, also after a trap, and also through imported memories, tables and
  globals;
* `assert_unlinkable`: no change;
* `assert_uninstantiable`: the store after the start call's normal form (the instance itself is
  unreachable; what the start function wrote into imported state persists).

`ScriptAt o pre ctx` relates the prefix to every context it can reach; at `profile o` there is at
most one (`ScriptAt.unique`, `….Thms`). As in `Silmaril.Project.Shapes.WasmWast`, a claim is
relative to the actual runs of the earlier commands; their expectations are separate rows.

**Uniqueness claims.** `Only` quantifies over host-free normal forms; `Always` (no infinite run,
every finite run extends to the outcome) follows by `ReturnsOnly.always` (`….Thms`).
`Unlinkable` is relative to the script-level name resolution `resolve?` (that of the reference
interpreter's registry) and to silmaril-lean's transcription `ExternAddrOk`; with `ModuleOk.unique`
it gives `Unlinkable.not_instantiate`: no `Instantiate` derivation exists for the resolved
addresses, under any profile and host. `Uninstantiable` covers start functions that trap; a
segment initialisation that traps makes `instantiateOnce?` fail, and has no shape here.

`Silmaril.Project.Shapes.WasmWastLink.Thms` proves every claim of a script from one kernel
evaluation of `scriptLK` on `KMem` stores (`ScriptHolds.of_kernel`).
-/

@[expose] public section

namespace Silmaril.Project.Shapes.WasmWastLink

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded
open Silmaril.Project.Shapes.WasmWast (Expect exportFunc? invokeOkB importStoreKM)

/-! ## The `spectest` environment -/

namespace Spectest

/-- The function type `ps → []`, as a final type with no supertypes. -/
def printType (ps : List ValType) : RecType := ⟨[⟨true, [], .func ⟨ps, []⟩⟩]⟩

/-- `funcref`. -/
def funcref : RefType := ⟨true, .abstract .func⟩

/-- **The `spectest` module.** The exports of `spectest.ml` at WebAssembly/spec `608711107b`:
`global_i32` = 666, `global_i64` = 666, `global_f32` = 666.6 (bits `0x4426A666`), `global_f64` =
666.6 (bits `0x4084D4CCCCCCCCCD`), all immutable; `table` (i32, 10..20, funcref, null),
`table64` (i64, 10..20, funcref, null), `memory` (i32, 1..2 pages, zero); and the print functions
`print : [] → []`, `print_i32 : [i32] → []`, `print_i64 : [i64] → []`, `print_f32 : [f32] → []`,
`print_f64 : [f64] → []`, `print_i32_f32 : [i32 f32] → []`, `print_f64_f64 : [f64 f64] → []`,
here with empty bodies (no locals, no instructions). -/
def module : Module where
  types := [printType [], printType [.i32], printType [.i64], printType [.f32], printType [.f64],
    printType [.i32, .f32], printType [.f64, .f64]]
  globals := [⟨⟨.const, .i32⟩, [.intConst .i32 666]⟩, ⟨⟨.const, .i64⟩, [.intConst .i64 666]⟩,
    ⟨⟨.const, .f32⟩, [.floatConst .f32 0x4426A666]⟩,
    ⟨⟨.const, .f64⟩, [.floatConst .f64 0x4084D4CCCCCCCCCD]⟩]
  memories := [⟨.i32, ⟨1, some 2⟩⟩]
  tables := [⟨⟨.i32, ⟨10, some 20⟩, funcref⟩, [.refNull (.abstract .func)]⟩,
    ⟨⟨.i64, ⟨10, some 20⟩, funcref⟩, [.refNull (.abstract .func)]⟩]
  funcs := [⟨⟨0⟩, [], []⟩, ⟨⟨1⟩, [], []⟩, ⟨⟨2⟩, [], []⟩, ⟨⟨3⟩, [], []⟩, ⟨⟨4⟩, [], []⟩,
    ⟨⟨5⟩, [], []⟩, ⟨⟨6⟩, [], []⟩]
  exports := [⟨"global_i32", .global ⟨0⟩⟩, ⟨"global_i64", .global ⟨1⟩⟩,
    ⟨"global_f32", .global ⟨2⟩⟩, ⟨"global_f64", .global ⟨3⟩⟩,
    ⟨"table", .table ⟨0⟩⟩, ⟨"table64", .table ⟨1⟩⟩, ⟨"memory", .memory ⟨0⟩⟩,
    ⟨"print", .func ⟨0⟩⟩, ⟨"print_i32", .func ⟨1⟩⟩, ⟨"print_i64", .func ⟨2⟩⟩,
    ⟨"print_f32", .func ⟨3⟩⟩, ⟨"print_f64", .func ⟨4⟩⟩, ⟨"print_i32_f32", .func ⟨5⟩⟩,
    ⟨"print_f64_f64", .func ⟨6⟩⟩]

/-- Every function export of `mi` has, in `s`, an empty body (no locals, no instructions) and
no results. Only the functions of `s` are read, so it is stated over any memory
representation. -/
def printsEmpty {R : Type} (s : Store Nat R) (mi : ModuleInst) : Bool :=
  (Game.exportFuncAddrs mi).all fun a =>
    match s.funcs[a]? with
    | some fi =>
      (match fi.code with
        | .wasm f => f.locals.isEmpty && f.body.isEmpty
        | .host _ => false) &&
      (match fi.type.funcType? with
        | some (_, rs) => rs.isEmpty
        | none => false)
    | none => false

/-- The kernel check behind `Spectest.print_nf` (`….Thms`): the instance of `module` (on `KMem`
stores) has seven function exports, all with empty bodies and no results. -/
noncomputable def printsEmptyB : Bool :=
  match instantiateOnce? importStoreKM module [] with
  | some (s, f, none) => printsEmpty s f.module && (Game.exportFuncAddrs f.module).length == 7
  | _ => false

end Spectest

/-! ## Script contexts -/

/-- A name environment: names to module instances, the most recent binding first. -/
abbrev Names := List (String × ModuleInst)

/-- The instance a name is bound to (the most recent binding). -/
def lookup (l : Names) (n : String) : Option ModuleInst :=
  (l.find? (·.1 == n)).map (·.2)

/-- A script context over the memory representation `R`: the store, the registered names, the
named modules and the current module. -/
structure CtxR (R : Type) where
  store : Store Nat R
  regs : Names := []
  named : Names := []
  cur : Option ModuleInst := none

/-- A script context over the specification's `ByteArray` memories. -/
abbrev Ctx := CtxR ByteArray

/-- A context read through `Store.toBytes` (the specification's memories). -/
def CtxR.toBytes {R : Type} [Silmaril.Wasm.Execution.MemRep R] (ctx : CtxR R) : Ctx :=
  ⟨ctx.store.toBytes, ctx.regs, ctx.named, ctx.cur⟩

/-- The module an action or a `register` refers to: the current one or a named one. -/
inductive Target where
  | cur
  | named (n : String)
  deriving DecidableEq, Repr

/-- The instance of a target. -/
def CtxR.inst? {R : Type} (ctx : CtxR R) : Target → Option ModuleInst
  | .cur => ctx.cur
  | .named n => lookup ctx.named n

/-- Bind the name of a named module. -/
def bindName (name : Option String) (mi : ModuleInst) (l : Names) : Names :=
  match name with
  | some n => (n, mi) :: l
  | none => l

/-- The external address of the export `name` of `mi` (the first export of that name). -/
def exportAddr? (mi : ModuleInst) (name : String) : Option ExternAddr :=
  (mi.exports.find? (·.name == name)).map (·.addr)

/-- Import resolution by the registry, as the reference interpreter links: each import
`(import "M" "x" …)` is the export `x` of the instance registered as `M`. -/
def resolve? (regs : Names) (imps : List Import) : Option (List ExternAddr) :=
  imps.mapM fun i => (lookup regs i.moduleName).bind (exportAddr? · i.name)

/-- A WAST action. -/
inductive Action where
  /-- `(invoke t name args)`. -/
  | invoke (t : Target) (name : String) (args : List Val)
  /-- `(get t name)`: the value of a global export. -/
  | get (t : Target) (name : String)
  deriving DecidableEq, Repr

/-- A command of a linked script. `claim := false` keeps a module assertion whose claim is not
checked as a command for the context only. -/
inductive Cmd where
  /-- `(module $name? …)`. -/
  | module (name : Option String) (m : Module)
  /-- `(register "name" $t?)`. -/
  | register (as : String) (t : Target)
  /-- An action and, for an assertion, its expected outcome (`none`: a bare action, or an
  assertion that is not checked, kept for the context). -/
  | action (act : Action) (expect : Option Expect)
  /-- `(assert_unlinkable …)`. -/
  | unlinkable (m : Module) (claim : Bool)
  /-- `(assert_uninstantiable …)` of a module whose start function traps. -/
  | uninstantiable (m : Module) (claim : Bool)

/-! ## Runs -/

/-- `c'` is a host-free normal form of `c` under `profile o`. -/
def NF (o : GrowOracle) (c c' : Config Nat) : Prop :=
  Steps (profile o) Det.noHost c c' ∧ ∀ x, ¬ Step (profile o) Det.noHost c' x

/-- The host-free normal forms of an action in the context `ctx`: the outcome (`none` for a normal
form that is not a result, such as a stuck configuration) and the store. -/
inductive ActNF (o : GrowOracle) (ctx : Ctx) : Action → Option Result → Store Nat → Prop
  | invoke {t : Target} {name : String} {args : List Val} {mi : ModuleInst} {a : Nat}
      {c : Config Nat} (hm : ctx.inst? t = some mi) (ha : exportFunc? mi name = some a)
      (hc : NF o (invoke ctx.store a args) c) :
      ActNF o ctx (.invoke t name args) c.outcome? c.store
  | get {t : Target} {name : String} {mi : ModuleInst} {a : Nat} {gi : GlobalInst}
      (hm : ctx.inst? t = some mi) (ha : exportAddr? mi name = some (.global a))
      (hg : ctx.store.globals[a]? = some gi) :
      ActNF o ctx (.get t name) (some (.values [gi.value])) ctx.store

/-- Linking and instantiating `m` in `ctx` can end with the outcome `ro` of the start code (`none`
for a normal form that is not a result), the store `s` and the instance `mi`: `m` is valid, its
imports resolve to addresses of the import types, `instantiateOnce?` allocates it and initialises
its segments, and the start call (if any) runs to a host-free normal form. -/
inductive InstNF (o : GrowOracle) (ctx : Ctx) (m : Module) :
    Option Result → Store Nat → ModuleInst → Prop
  | mk {mt : CModuleType} {xas : List ExternAddr} {s : Store Nat} {f : Frame}
      {st : Option FuncIdx} {c : Config Nat} (hm : ModuleOk m mt)
      (hr : resolve? ctx.regs m.imports = some xas)
      (hx : List.Forall₂ (ExternAddrOk ctx.store) xas mt.imports)
      (hi : instantiateOnce? ctx.store m xas = some (s, f, st))
      (hc : NF o ⟨s, f, startCode st⟩ c) : InstNF o ctx m c.outcome? c.store f.module

/-- One command changes the context (see the module docstring). -/
inductive CmdRun (o : GrowOracle) : Ctx → Cmd → Ctx → Prop
  | module {ctx : Ctx} {name : Option String} {m : Module} {s : Store Nat} {mi : ModuleInst}
      (h : InstNF o ctx m (some (.values [])) s mi) :
      CmdRun o ctx (.module name m)
        { ctx with store := s, cur := some mi, named := bindName name mi ctx.named }
  | register {ctx : Ctx} {as : String} {t : Target} {mi : ModuleInst}
      (h : ctx.inst? t = some mi) :
      CmdRun o ctx (.register as t) { ctx with regs := (as, mi) :: ctx.regs }
  | action {ctx : Ctx} {act : Action} {e : Option Expect} {r : Result} {s : Store Nat}
      (h : ActNF o ctx act (some r) s) : CmdRun o ctx (.action act e) { ctx with store := s }
  | unlinkable {ctx : Ctx} {m : Module} {claim : Bool} : CmdRun o ctx (.unlinkable m claim) ctx
  | uninstantiable {ctx : Ctx} {m : Module} {claim : Bool} {r : Result} {s : Store Nat}
      {mi : ModuleInst} (h : InstNF o ctx m (some r) s mi) :
      CmdRun o ctx (.uninstantiable m claim) { ctx with store := s }

/-- The commands run in order. -/
inductive Run (o : GrowOracle) : Ctx → List Cmd → Ctx → Prop
  | nil (ctx : Ctx) : Run o ctx [] ctx
  | cons {ctx ctx' ctx'' : Ctx} {cmd : Cmd} {cmds : List Cmd} (h : CmdRun o ctx cmd ctx')
      (t : Run o ctx' cmds ctx'') : Run o ctx (cmd :: cmds) ctx''

/-- **The initial context**: the instance of `Spectest.module`, allocated in the empty store
`Game.importStore []`, registered as `"spectest"`; no current module. -/
def Init (ctx : Ctx) : Prop :=
  ∃ s f, instantiateOnce? (Game.importStore []) Spectest.module [] = some (s, f, none) ∧
    ctx = { store := s, regs := [("spectest", f.module)] }

/-- The script prefix `pre` can be in the context `ctx`. -/
def ScriptAt (o : GrowOracle) (pre : List Cmd) (ctx : Ctx) : Prop :=
  ∃ ctx₀, Init ctx₀ ∧ Run o ctx₀ pre ctx

/-! ## Claims -/

/-- After `pre`, some host-free normal form of `act` has the outcome `r`. -/
def Reaches (o : GrowOracle) (pre : List Cmd) (act : Action) (r : Result) : Prop :=
  ∃ ctx s, ScriptAt o pre ctx ∧ ActNF o ctx act (some r) s

/-- After `pre`, every host-free normal form of `act` has the outcome `r` (vacuous if there are
none; divergence is excluded by `ReturnsOnly.always`, `….Thms`). -/
def Only (o : GrowOracle) (pre : List Cmd) (act : Action) (r : Result) : Prop :=
  ∀ ctx ro s, ScriptAt o pre ctx → ActNF o ctx act ro s → ro = some r

/-- **`assert_return` in a linked script**: after the commands `pre` (from the context `Init`
with the closed `spectest` module), some host-free run of `act` under `profile o` returns `vs`,
and every host-free normal form of `act` returns `vs`. -/
@[problem "silmaril.shapes.wasm.wast.link.returns_only"
  (title := "A WAST action after a linked script prefix (closed spectest module) returns given values, at every host-free normal form")]
def ReturnsOnly (o : GrowOracle) (pre : List Cmd) (act : Action) (vs : List Val) : Prop :=
  Reaches o pre act (.values vs) ∧ Only o pre act (.values vs)

/-- **`assert_trap` in a linked script**: after `pre`, some host-free run of `act` under
`profile o` traps, and every host-free normal form of `act` is a trap. -/
@[problem "silmaril.shapes.wasm.wast.link.traps_only"
  (title := "A WAST action after a linked script prefix (closed spectest module) traps, at every host-free normal form")]
def TrapsOnly (o : GrowOracle) (pre : List Cmd) (act : Action) : Prop :=
  Reaches o pre act .trap ∧ Only o pre act .trap

/-- **`assert_unlinkable`**: the prefix `pre` reaches a context, and in every context it reaches,
`m` is valid and cannot be linked: if its imports resolve by name to the addresses `xas`, these do
not have the import types of `m` (`ExternAddrOk`, silmaril-lean's transcription of the
specification's `Externaddr_ok`). -/
@[problem "silmaril.shapes.wasm.wast.link.unlinkable"
  (title := "After a linked WAST script prefix (closed spectest module), a valid module's imports do not resolve to addresses of the import types")]
def Unlinkable (o : GrowOracle) (pre : List Cmd) (m : Module) : Prop :=
  (∃ ctx, ScriptAt o pre ctx) ∧
    ∀ ctx, ScriptAt o pre ctx → (∃ mt, ModuleOk m mt) ∧
      ∀ mt xas, ModuleOk m mt → resolve? ctx.regs m.imports = some xas →
        ¬ List.Forall₂ (ExternAddrOk ctx.store) xas mt.imports

/-- **`assert_uninstantiable`, start trap**: after `pre`, `m` links and is allocated by
`instantiateOnce?`, and some host-free run of its start code traps; every host-free normal form
of the start code is a trap. -/
@[problem "silmaril.shapes.wasm.wast.link.uninstantiable"
  (title := "After a linked WAST script prefix (closed spectest module), a module links and its start function traps, at every host-free normal form")]
def Uninstantiable (o : GrowOracle) (pre : List Cmd) (m : Module) : Prop :=
  (∃ ctx s mi, ScriptAt o pre ctx ∧ InstNF o ctx m (some .trap) s mi) ∧
    ∀ ctx ro s mi, ScriptAt o pre ctx → InstNF o ctx m ro s mi → ro = some .trap

/-- The claim of a command after the commands `pre`. -/
def Cmd.Holds (o : GrowOracle) (pre : List Cmd) : Cmd → Prop
  | .action act (some (.values vs)) => ReturnsOnly o pre act vs
  | .action act (some .trap) => TrapsOnly o pre act
  | .unlinkable m true => Unlinkable o pre m
  | .uninstantiable m true => Uninstantiable o pre m
  | _ => True

/-- The first `k` commands. -/
def pre (cmds : List Cmd) (k : Nat) : List Cmd := cmds.take k

/-- Every command of the script holds after the commands before it. -/
def ScriptHolds (o : GrowOracle) (cmds : List Cmd) : Prop :=
  ∀ k (cmd : Cmd), cmds[k]? = some cmd → cmd.Holds o (pre cmds k)

/-- **Termination and determinacy of the outcome** (not a shape; `ReturnsOnly.always`,
`TrapsOnly.always`, `….Thms`): after `pre`, no host-free run of an invoked function is infinite,
and every finite run extends to a normal form with the outcome `r`. -/
def Always (o : GrowOracle) (pre : List Cmd) (act : Action) (r : Result) : Prop :=
  ∀ ctx, ScriptAt o pre ctx → ∀ t name args mi a, act = .invoke t name args →
    ctx.inst? t = some mi → exportFunc? mi name = some a →
    ¬ Diverges (profile o) Det.noHost (invoke ctx.store a args) ∧
    ∀ c', Steps (profile o) Det.noHost (invoke ctx.store a args) c' →
      ∃ c, Steps (profile o) Det.noHost c' c ∧ NF o (invoke ctx.store a args) c ∧
        c.outcome? = some r

/-! ## The kernel checker

`scriptLK o fuel cmds` instantiates `Spectest.module`, then runs every command on `KMem` stores
(`Silmaril.Wasm.Execution.MemRep`) with `fuel` steps of the interpreter head step `interpHead o`
under the structural driver `Verify.Kernel.runK`, checking each expectation. It is stated over
any memory representation (`scriptG`); `ScriptHolds.of_kernel` (`….Thms`) turns
`scriptLK … = true` into `ScriptHolds`, through `scriptG` on `ByteArray` stores. -/

section Checker

variable {R : Type} [Silmaril.Wasm.Execution.MemRep R]

/-- Run a configuration with `fuel` steps: the stopped configuration. -/
noncomputable def runG (o : GrowOracle) (fuel : Nat) (c : Config Nat R) : Option (Config Nat R) :=
  let r := Silmaril.Wasm.Verify.Kernel.runK (Exec.interpHead o) fuel c
  if r.2 then some r.1 else none

/-- Link, instantiate and run the start code of `m`: the stopped configuration and the instance. -/
noncomputable def instG (o : GrowOracle) (fuel : Nat) (ctx : CtxR R) (m : Module) :
    Option (Config Nat R × ModuleInst) :=
  match validate? m with
  | none => none
  | some mt =>
    match resolve? ctx.regs m.imports with
    | none => none
    | some xas =>
      if externAddrsOk? ctx.store xas mt.imports then
        match instantiateOnce? ctx.store m xas with
        | some (s, f, st) => (runG o fuel ⟨s, f, startCode st⟩).map fun c => (c, f.module)
        | none => none
      else none

/-- `m` is valid and its imports do not resolve to addresses of its import types. -/
def unlinkableG (ctx : CtxR R) (m : Module) : Bool :=
  match validate? m with
  | some mt =>
    match resolve? ctx.regs m.imports with
    | none => true
    | some xas => !externAddrsOk? ctx.store xas mt.imports
  | none => false

/-- Run an action: its result and the next store. -/
noncomputable def actG (o : GrowOracle) (fuel : Nat) (ctx : CtxR R) :
    Action → Option (Result × Store Nat R)
  | .invoke t name args =>
    match ctx.inst? t with
    | some mi =>
      match exportFunc? mi name with
      | some a =>
        if invokeOkB ctx.store a args then
          (runG o fuel (invoke ctx.store a args)).bind fun c => c.outcome?.map fun r => (r, c.store)
        else none
      | none => none
    | none => none
  | .get t name =>
    match ctx.inst? t with
    | some mi =>
      match exportAddr? mi name with
      | some (.global a) => ctx.store.globals[a]?.map fun gi => (.values [gi.value], ctx.store)
      | _ => none
    | none => none

/-- Run the commands from `ctx`, checking each claim. -/
noncomputable def cmdsG (o : GrowOracle) (fuel : Nat) : CtxR R → List Cmd → Bool
  | _, [] => true
  | ctx, .module name m :: cmds =>
    match instG o fuel ctx m with
    | some (c, mi) =>
      let ctx' : CtxR R :=
        { ctx with store := c.store, cur := some mi, named := bindName name mi ctx.named }
      decide (c.outcome? = some (.values [])) && cmdsG o fuel ctx' cmds
    | none => false
  | ctx, .register as t :: cmds =>
    match ctx.inst? t with
    | some mi => cmdsG o fuel { ctx with regs := (as, mi) :: ctx.regs } cmds
    | none => false
  | ctx, .action act e :: cmds =>
    match actG o fuel ctx act with
    | some (r, s) =>
      (match e with
        | some e => decide (r = e.result)
        | none => true) && cmdsG o fuel { ctx with store := s } cmds
    | none => false
  | ctx, .unlinkable m claim :: cmds => (!claim || unlinkableG ctx m) && cmdsG o fuel ctx cmds
  | ctx, .uninstantiable m claim :: cmds =>
    match instG o fuel ctx m with
    | some (c, _) =>
      match c.outcome? with
      | some r => (!claim || decide (r = .trap)) && cmdsG o fuel { ctx with store := c.store } cmds
      | none => false
    | none => false

/-- Validate `Spectest.module` (no imports), instantiate it in the empty store `s₀`, register it,
and run the commands. -/
noncomputable def scriptG (o : GrowOracle) (fuel : Nat) (s₀ : Store Nat R) (cmds : List Cmd) :
    Bool :=
  match validate? Spectest.module with
  | some mt =>
    mt.imports.isEmpty &&
      match instantiateOnce? s₀ Spectest.module [] with
      | some (s, f, none) => cmdsG o fuel { store := s, regs := [("spectest", f.module)] } cmds
      | _ => false
  | none => false

end Checker

open Silmaril.Wasm.Execution (KMem) in
/-- **The kernel checker**: `scriptG` on `KMem` stores, from the empty store. -/
noncomputable def scriptLK (o : GrowOracle) (fuel : Nat) (cmds : List Cmd) : Bool :=
  scriptG (R := KMem) o fuel importStoreKM cmds

end Silmaril.Project.Shapes.WasmWastLink

end
