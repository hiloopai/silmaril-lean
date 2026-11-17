module

public import Silmaril.Project.Shapes.WasmWastLink.Defs
public import Silmaril.Wasm.Abstract.HostDet.Defs
public import Silmaril.Wasm.SingleThreaded.Interface

/-!
# Standard problem shapes: linked WAST scripts against the typed `spectest` host

The commands of a WAST script with several modules, imports and `register`, stated over the Core
semantics `Step (profile o) Spectest.host` with a **concrete host**: the `spectest` environment of
the reference interpreter as host functions, host-allocated globals and shared table and memory.

| name | statement |
|---|---|
| `silmaril.shapes.wasm.wast.host.returns_only` | `ReturnsOnly o pre act vs`: after the script prefix `pre`, some normal form of the action `act` under `Spectest.host` returns `vs`, and every one does |
| `silmaril.shapes.wasm.wast.host.traps_only` | `TrapsOnly o pre act`: the same with a trap |
| `silmaril.shapes.wasm.wast.host.unlinkable` | `Unlinkable o pre m`: after `pre`, `m` is valid and its imports cannot be linked: some import names nothing in the registry, or the resolved external addresses do not have the import types (`ExternAddrOk`) |
| `silmaril.shapes.wasm.wast.host.log_is` | `LogIs o cmds l`: the script `cmds` runs, and every context it reaches has the host-call log `l` (its printed values are `Spectest.printed l`) |
| `silmaril.shapes.wasm.wast.host.uninstantiable` | `Uninstantiable o pre m`: after `pre`, `m` links and `instantiateOnce?` allocates it, and its start function traps, at every normal form under `Spectest.host` |

## The environment: host, registry and observation

The reference interpreter of WebAssembly/spec at `608711107b` registers
`interpreter/host/spectest.ml` as the virtual module `"spectest"`
(`interpreter/main/main.ml` l. 11, `Run.register_virtual`). An import `(import "spectest" "x" …)`
calls `Spectest.lookup "x"` once, when the importing module is linked
(`interpreter/script/runner.ml` l. 338–349 `lookup_registry`/`lookup_import`, l. 395–400
`run_instantiation`). `spectest.ml` l. 48–64:

* `print`, `print_i32`, `print_i64`, `print_f32`, `print_f64`, `print_i32_f32`, `print_f64_f64`:
  `func print ts []` (l. 34–36) allocates **a fresh host function at every lookup**
  (`Func.alloc_host`) of type `ts → []` (a final sub type, no supertypes); calling it prints one
  line `"<value> : <type>"` per argument to standard output (l. 38–45) and returns no values. It
  never traps or diverges and does not touch the store.
* `global_i32`, `global_i64`, `global_f32`, `global_f64`: `global (GlobalT (Cons, t))` (l. 10–20)
  allocates **a fresh immutable global at every lookup**, with value 666 or 666.6
  (`F32.of_float 666.6` = `0x4426A666`, `F64.of_float 666.6` = `0x4084D4CCCCCCCCCD`).
* `table`, `table64`, `memory` (l. 22–32) are top-level values, allocated once when the
  interpreter starts: **every lookup returns the same table or memory** (i32 or i64 table of
  10..20 null `funcref`s; i32 memory of 1..2 pages).
* Any other name: no export (an `unknown import` link error). The import type is not consulted
  by the lookup; instantiation checks it (`interpreter/exec/eval.ml` l. 1183–1190
  `init_import`).

This module models that environment exactly in those respects:

* **Host.** `Spectest.host : HostSemantics Nat` answers a call of host code `k < 7` (the `k`-th
  print function) in the store `s` with the unchanged store `s` and no values. Its guard
  `printsTyped s k` (every host function instance with code `k` has no results) makes its
  answers typed in every store (`Spectest.hostTyped`, `….Thms`); in a script it always holds.
  It has at most one outcome per call (`Spectest.hostDet`): **the host is deterministic**.
* **Registry.** A registered name is bound either to a module instance (`Reg.inst`, by
  `register`) or to the `spectest` environment (`Reg.spectest sh`). Resolution (`resolve?`) is
  stateful: in import order, a `spectest` print import allocates a fresh host function
  (`allocHost`, code `k`, type `ofFlatType (ps → [])`), a `spectest` global import allocates a
  fresh global (`allocGlobal`), and `table`, `table64`, `memory` resolve to the exports of the
  one instance `sh` of `Spectest.shared`, allocated in the empty store at the start of the script
  (`Init`). This is the reference interpreter's identity: fresh where it is fresh, shared where it
  is shared (`Spectest.resolve_print_fresh`, `Spectest.resolve_global_fresh`,
  `Spectest.resolve_shared`, `….Thms`). The table and memory are shared within one script; the
  reference interpreter also shares them across the scripts of one process.
* **Observation.** A run is an `LStep` run (`Silmaril.Wasm.Abstract.HostDet`): it records each
  answered host call `(k, args)`. The context keeps the log of the whole script; its projection
  `Spectest.printed log` (the arguments in order) is what the reference interpreter writes to
  standard output, one line per value (the line shows the value and its type, which the value
  carries; a call of `print` with no arguments writes nothing). WAST assertions do not observe
  standard output; the claims below are about results, and the log is determined
  (`ScriptAt.unique`, `….Thms`).

**What is not claimed.** Nothing here is about the `env` virtual module (`main.ml` l. 12), about
standard output as bytes (the text of a value is the reference interpreter's printer), or about a
context distinguishing this host from another implementation of `spectest`. Fresh and shared
identity of globals and functions is a property of the store; Wasm code cannot observe it
(globals of `spectest` are immutable and function references have no equality); tables and memory
are mutable and shared, which is observable (the hand-written rows
`silmaril.wasm_wast.spectest_host.*`).

**Script state.** As in `Silmaril.Project.Shapes.WasmWastLink`, a context `Ctx` has the store,
the registry, the named modules, the current module, and here also the host log. `pre` lists the
commands before the claim; each changes the context as the reference interpreter does when its
assertion holds (`CmdRun`); runs are `LStep` runs to normal forms under `Spectest.host` (`NF`).
`ScriptAt o pre ctx` relates the prefix to every context it can reach; at `profile o` there is at
most one (`ScriptAt.unique`). The commands are those of `Silmaril.Project.Shapes.WasmWastLink`
(`Cmd`, `Action`, `Target`).

`Silmaril.Project.Shapes.WasmWastHost.Thms` proves every claim of a script from one kernel
evaluation of `scriptHK` on `KMem` stores (`ScriptHolds.of_kernel`).
-/

@[expose] public section

namespace Silmaril.Project.Shapes.WasmWastHost

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Abstract
open Silmaril.Project.Shapes.WasmWast (Expect exportFunc? invokeOkB importStoreKM)
open Silmaril.Project.Shapes.WasmWastLink (Names lookup Target bindName exportAddr? Action Cmd)

/-! ## The `spectest` environment -/

namespace Spectest

/-- What a `spectest` name denotes. -/
inductive Entry where
  /-- A print function: its host code and parameter types (no results). -/
  | print (code : Nat) (ps : List NumType)
  /-- An immutable global of a numeric type with the bits of its value. -/
  | global (t : NumType) (b : BitVec t.width)
  /-- The shared table or memory of that name. -/
  | shared

/-- **The names of `spectest.ml`** (`lookup`, l. 48–64), with the host codes `0..6` of the print
functions. -/
def entries : List (String × Entry) :=
  [("print", .print 0 []), ("print_i32", .print 1 [.int .i32]), ("print_i64", .print 2 [.int .i64]),
   ("print_f32", .print 3 [.float .f32]), ("print_f64", .print 4 [.float .f64]),
   ("print_i32_f32", .print 5 [.int .i32, .float .f32]),
   ("print_f64_f64", .print 6 [.float .f64, .float .f64]),
   ("global_i32", .global (.int .i32) 666), ("global_i64", .global (.int .i64) 666),
   ("global_f32", .global (.float .f32) 0x4426A666),
   ("global_f64", .global (.float .f64) 0x4084D4CCCCCCCCCD),
   ("table", .shared), ("table64", .shared), ("memory", .shared)]

/-- The entry of a name. -/
def entry? (name : String) : Option Entry := (entries.find? (·.1 == name)).map (·.2)

/-- The number of print functions: the host codes are `0, …, 6`. -/
def printCount : Nat := 7

/-- **The shared entities of `spectest.ml`**: `table` (i32, 10..20 null `funcref`s), `table64`
(i64, the same) and `memory` (i32, 1..2 pages), allocated once per script. -/
def shared : Module where
  memories := [⟨.i32, ⟨1, some 2⟩⟩]
  tables := [⟨⟨.i32, ⟨10, some 20⟩, WasmWastLink.Spectest.funcref⟩, [.refNull (.abstract .func)]⟩,
    ⟨⟨.i64, ⟨10, some 20⟩, WasmWastLink.Spectest.funcref⟩, [.refNull (.abstract .func)]⟩]
  exports := [⟨"table", .table ⟨0⟩⟩, ⟨"table64", .table ⟨1⟩⟩, ⟨"memory", .memory ⟨0⟩⟩]

/-- The function instances with host code `k` in `s` all have no results. Only the functions of
`s` are read, so it is stated over any memory representation. -/
def printsTyped {R : Type} (s : Store Nat R) (k : Nat) : Bool :=
  s.funcs.all fun fi =>
    match fi.code with
    | .host k' =>
      k' != k || (match fi.type.funcType? with
        | some (_, rs) => rs.isEmpty
        | none => false)
    | .wasm _ => true

/-- The host answers a call of code `k` in `s`. -/
def answers {R : Type} (s : Store Nat R) (k : Nat) : Bool :=
  decide (k < printCount) && printsTyped s k

/-- **The `spectest` host.** A call of host code `k < 7` (a print function) returns no values
and leaves the store unchanged, when every host function of code `k` in the store has no results
(`printsTyped`). The output it prints is the log entry of the call (`LStep`); `printed`. -/
def host : HostSemantics Nat := fun k s _ out => answers s k = true ∧ out = .returned s (.values [])

/-- **The observable projection**: the values the reference interpreter prints for a host-call
log, in order (one line per value). -/
def printed (l : HostLog Nat) : List Val := l.flatMap (·.2)

/-- **Lookup of a `spectest` name** in the store `s`, with the shared instance `sh`: a print
function or a global is allocated fresh; `table`, `table64` and `memory` are the exports of
`sh`. -/
def lookup? {R : Type} (sh : ModuleInst) (s : Store Nat R) (name : String) :
    Option (Store Nat R × ExternAddr) :=
  match entry? name with
  | some (.print k ps) => some ((allocHost s ⟨ps, []⟩ k).1, .func (allocHost s ⟨ps, []⟩ k).2)
  | some (.global t b) => some ((allocGlobal s ⟨.const, .num t⟩ (.num ⟨t, b⟩)).1,
      .global (allocGlobal s ⟨.const, .num t⟩ (.num ⟨t, b⟩)).2)
  | some .shared => (exportAddr? sh name).map fun xa => (s, xa)
  | none => none

end Spectest

/-! ## Registry and script contexts -/

/-- A registered name: a module instance, or the `spectest` environment with its shared
instance. -/
inductive Reg where
  | inst (mi : ModuleInst)
  | spectest (sh : ModuleInst)

/-- The registry: names, the most recent binding first. -/
abbrev Regs := List (String × Reg)

/-- The binding of a registered name (the most recent). -/
def lookupReg (l : Regs) (n : String) : Option Reg := (l.find? (·.1 == n)).map (·.2)

/-- **Import resolution, as the reference interpreter links**: in import order, an import of a
registered instance is its export; an import of `spectest` is `Spectest.lookup?`, which may
allocate. The store after the allocations and the addresses. -/
def resolve? {R : Type} (regs : Regs) : Store Nat R → List Import →
    Option (Store Nat R × List ExternAddr)
  | s, [] => some (s, [])
  | s, i :: is =>
    match lookupReg regs i.moduleName with
    | some (.inst mi) =>
      match exportAddr? mi i.name with
      | some xa => (resolve? regs s is).map fun p => (p.1, xa :: p.2)
      | none => none
    | some (.spectest sh) =>
      match Spectest.lookup? sh s i.name with
      | some (s₁, xa) => (resolve? regs s₁ is).map fun p => (p.1, xa :: p.2)
      | none => none
    | none => none

/-- A script context over the memory representation `R`: the store, the registry, the named
modules, the current module and the host-call log. -/
structure CtxR (R : Type) where
  store : Store Nat R
  regs : Regs := []
  named : Names := []
  cur : Option ModuleInst := none
  log : HostLog Nat := []

/-- A script context over the specification's `ByteArray` memories. -/
abbrev Ctx := CtxR ByteArray

/-- A context read through `Store.toBytes`. -/
def CtxR.toBytes {R : Type} [Silmaril.Wasm.Execution.MemRep R] (ctx : CtxR R) : Ctx :=
  ⟨ctx.store.toBytes, ctx.regs, ctx.named, ctx.cur, ctx.log⟩

/-- The instance of a target. -/
def CtxR.inst? {R : Type} (ctx : CtxR R) : Target → Option ModuleInst
  | .cur => ctx.cur
  | .named n => lookup ctx.named n

/-! ## Runs -/

/-- `y` is a normal form of `x` under `Spectest.host` and `profile o`, reached by a logged run. -/
def NF (o : GrowOracle) (x y : Config Nat × HostLog Nat) : Prop :=
  LSteps (profile o) Spectest.host x y ∧ ∀ c, ¬ Step (profile o) Spectest.host y.1 c

/-- The normal forms of an action in `ctx`: the outcome (`none` for a normal form that is not a
result), the store and the log. -/
inductive ActNF (o : GrowOracle) (ctx : Ctx) :
    Action → Option Result → Store Nat → HostLog Nat → Prop
  | invoke {t : Target} {name : String} {args : List Val} {mi : ModuleInst} {a : Nat}
      {c : Config Nat} {l : HostLog Nat} (hm : ctx.inst? t = some mi)
      (ha : exportFunc? mi name = some a) (hc : NF o (invoke ctx.store a args, ctx.log) (c, l)) :
      ActNF o ctx (.invoke t name args) c.outcome? c.store l
  | get {t : Target} {name : String} {mi : ModuleInst} {a : Nat} {gi : GlobalInst}
      (hm : ctx.inst? t = some mi) (ha : exportAddr? mi name = some (.global a))
      (hg : ctx.store.globals[a]? = some gi) :
      ActNF o ctx (.get t name) (some (.values [gi.value])) ctx.store ctx.log

/-- Linking and instantiating `m` in `ctx` can end with the outcome `ro` of the start code, the
store `s`, the log `l` and the instance `mi`: `m` is valid, its imports resolve (allocating the
fresh `spectest` entities) to addresses of the import types, `instantiateOnce?` allocates it and
initialises its segments, and the start call (if any) runs to a normal form. -/
inductive InstNF (o : GrowOracle) (ctx : Ctx) (m : Module) :
    Option Result → Store Nat → HostLog Nat → ModuleInst → Prop
  | mk {mt : CModuleType} {s₀ : Store Nat} {xas : List ExternAddr} {s : Store Nat} {f : Frame}
      {st : Option FuncIdx} {c : Config Nat} {l : HostLog Nat} (hm : ModuleOk m mt)
      (hr : resolve? ctx.regs ctx.store m.imports = some (s₀, xas))
      (hx : List.Forall₂ (ExternAddrOk s₀) xas mt.imports)
      (hi : instantiateOnce? s₀ m xas = some (s, f, st))
      (hc : NF o (⟨s, f, startCode st⟩, ctx.log) (c, l)) :
      InstNF o ctx m c.outcome? c.store l f.module

/-- One command changes the context. -/
inductive CmdRun (o : GrowOracle) : Ctx → Cmd → Ctx → Prop
  | module {ctx : Ctx} {name : Option String} {m : Module} {s : Store Nat} {l : HostLog Nat}
      {mi : ModuleInst} (h : InstNF o ctx m (some (.values [])) s l mi) :
      CmdRun o ctx (.module name m)
        { ctx with store := s, log := l, cur := some mi, named := bindName name mi ctx.named }
  | register {ctx : Ctx} {as : String} {t : Target} {mi : ModuleInst}
      (h : ctx.inst? t = some mi) :
      CmdRun o ctx (.register as t) { ctx with regs := (as, .inst mi) :: ctx.regs }
  | action {ctx : Ctx} {act : Action} {e : Option Expect} {r : Result} {s : Store Nat}
      {l : HostLog Nat} (h : ActNF o ctx act (some r) s l) :
      CmdRun o ctx (.action act e) { ctx with store := s, log := l }
  | unlinkable {ctx : Ctx} {m : Module} {claim : Bool} : CmdRun o ctx (.unlinkable m claim) ctx
  | uninstantiable {ctx : Ctx} {m : Module} {claim : Bool} {r : Result} {s : Store Nat}
      {l : HostLog Nat} {mi : ModuleInst} (h : InstNF o ctx m (some r) s l mi) :
      CmdRun o ctx (.uninstantiable m claim) { ctx with store := s, log := l }

/-- The commands run in order. -/
inductive Run (o : GrowOracle) : Ctx → List Cmd → Ctx → Prop
  | nil (ctx : Ctx) : Run o ctx [] ctx
  | cons {ctx ctx' ctx'' : Ctx} {cmd : Cmd} {cmds : List Cmd} (h : CmdRun o ctx cmd ctx')
      (t : Run o ctx' cmds ctx'') : Run o ctx (cmd :: cmds) ctx''

/-- **The initial context**: the instance `sh` of `Spectest.shared` (the shared table, table64
and memory), allocated in the empty store; `"spectest"` is bound to the environment with `sh`;
no current module; empty log. -/
def Init (ctx : Ctx) : Prop :=
  ∃ s f, instantiateOnce? (Game.importStore []) Spectest.shared [] = some (s, f, none) ∧
    ctx = { store := s, regs := [("spectest", .spectest f.module)] }

/-- The script prefix `pre` can be in the context `ctx`. -/
def ScriptAt (o : GrowOracle) (pre : List Cmd) (ctx : Ctx) : Prop :=
  ∃ ctx₀, Init ctx₀ ∧ Run o ctx₀ pre ctx

/-! ## Claims -/

/-- After `pre`, some normal form of `act` under `Spectest.host` has the outcome `r`. -/
def Reaches (o : GrowOracle) (pre : List Cmd) (act : Action) (r : Result) : Prop :=
  ∃ ctx s l, ScriptAt o pre ctx ∧ ActNF o ctx act (some r) s l

/-- After `pre`, every normal form of `act` under `Spectest.host` has the outcome `r`. -/
def Only (o : GrowOracle) (pre : List Cmd) (act : Action) (r : Result) : Prop :=
  ∀ ctx ro s l, ScriptAt o pre ctx → ActNF o ctx act ro s l → ro = some r

/-- **`assert_return` in a linked script, against the `spectest` host**: after the commands
`pre`, some run of `act` under `profile o` and `Spectest.host` returns `vs`, and every normal
form of `act` returns `vs`. -/
@[problem "silmaril.shapes.wasm.wast.host.returns_only"
  (title := "A WAST action after a linked script prefix (typed spectest host) returns given values, at every normal form")]
def ReturnsOnly (o : GrowOracle) (pre : List Cmd) (act : Action) (vs : List Val) : Prop :=
  Reaches o pre act (.values vs) ∧ Only o pre act (.values vs)

/-- **`assert_trap` in a linked script, against the `spectest` host**. -/
@[problem "silmaril.shapes.wasm.wast.host.traps_only"
  (title := "A WAST action after a linked script prefix (typed spectest host) traps, at every normal form")]
def TrapsOnly (o : GrowOracle) (pre : List Cmd) (act : Action) : Prop :=
  Reaches o pre act .trap ∧ Only o pre act .trap

/-- **`assert_unlinkable`, against the `spectest` host**: the prefix reaches a context, and in
every context it reaches, `m` is valid and cannot be linked: if its imports resolve to the store
`s₀` and the addresses `xas`, these do not have the import types of `m` in `s₀`. -/
@[problem "silmaril.shapes.wasm.wast.host.unlinkable"
  (title := "After a linked WAST script prefix (typed spectest host), a valid module's imports do not resolve to addresses of the import types")]
def Unlinkable (o : GrowOracle) (pre : List Cmd) (m : Module) : Prop :=
  (∃ ctx, ScriptAt o pre ctx) ∧
    ∀ ctx, ScriptAt o pre ctx → (∃ mt, ModuleOk m mt) ∧
      ∀ mt s₀ xas, ModuleOk m mt → resolve? ctx.regs ctx.store m.imports = some (s₀, xas) →
        ¬ List.Forall₂ (ExternAddrOk s₀) xas mt.imports

/-- **`assert_uninstantiable`, start trap, against the `spectest` host**. -/
@[problem "silmaril.shapes.wasm.wast.host.uninstantiable"
  (title := "After a linked WAST script prefix (typed spectest host), a module links and its start function traps, at every normal form")]
def Uninstantiable (o : GrowOracle) (pre : List Cmd) (m : Module) : Prop :=
  (∃ ctx s l mi, ScriptAt o pre ctx ∧ InstNF o ctx m (some .trap) s l mi) ∧
    ∀ ctx ro s l mi, ScriptAt o pre ctx → InstNF o ctx m ro s l mi → ro = some .trap

/-- **The observation of a linked script, against the `spectest` host**: the commands `cmds` run
(from `Init`, under `profile o`), and every context they reach has the host-call log `l`; the
reference interpreter prints `Spectest.printed l`, one line per value. -/
@[problem "silmaril.shapes.wasm.wast.host.log_is"
  (title := "A linked WAST script (typed spectest host) runs, and its host-call log (the printed values) is the given one")]
def LogIs (o : GrowOracle) (cmds : List Cmd) (l : HostLog Nat) : Prop :=
  (∃ ctx, ScriptAt o cmds ctx) ∧ ∀ ctx, ScriptAt o cmds ctx → ctx.log = l

/-- The claim of a command after the commands `pre`. -/
def CmdHolds (o : GrowOracle) (pre : List Cmd) : Cmd → Prop
  | .action act (some (.values vs)) => ReturnsOnly o pre act vs
  | .action act (some .trap) => TrapsOnly o pre act
  | .unlinkable m true => Unlinkable o pre m
  | .uninstantiable m true => Uninstantiable o pre m
  | _ => True

/-- The first `k` commands. -/
def pre (cmds : List Cmd) (k : Nat) : List Cmd := cmds.take k

/-- Every command of the script holds after the commands before it. -/
def ScriptHolds (o : GrowOracle) (cmds : List Cmd) : Prop :=
  ∀ k (cmd : Cmd), cmds[k]? = some cmd → CmdHolds o (pre cmds k) cmd

/-- **Termination and determinacy of the outcome** (not a shape; `ReturnsOnly.always`, `….Thms`):
after `pre`, no run of an invoked function under `Spectest.host` is infinite, and every finite
run extends to a normal form with the outcome `r`. -/
def Always (o : GrowOracle) (pre : List Cmd) (act : Action) (r : Result) : Prop :=
  ∀ ctx, ScriptAt o pre ctx → ∀ t name args mi a, act = .invoke t name args →
    ctx.inst? t = some mi → exportFunc? mi name = some a →
    ¬ Diverges (profile o) Spectest.host (invoke ctx.store a args) ∧
    ∀ c', Steps (profile o) Spectest.host (invoke ctx.store a args) c' →
      ∃ c l, Steps (profile o) Spectest.host c' c ∧ NF o (invoke ctx.store a args, ctx.log) (c, l) ∧
        c.outcome? = some r

/-! ## The kernel checker

`scriptHK o fuel cmds` instantiates `Spectest.shared`, then runs every command on `KMem` stores
(`Silmaril.Wasm.Execution.MemRep`). A run alternates host-free runs of at most `fuel` steps
(`WasmWastLink.runG`: the interpreter head step `interpHead o` under `Verify.Kernel.runK`) with
host calls at the callout (`decompose?`), at most `fuel` of them, answered as `Spectest.host`
answers and logged (`runHG`). It is stated over any memory representation; `ScriptHolds.of_kernel`
(`….Thms`) turns `scriptHK … = true` into `ScriptHolds`, through `ByteArray` stores. -/

section Checker

variable {R : Type} [Silmaril.Wasm.Execution.MemRep R]

/-- Run a configuration and log: host-free runs of `fuel` steps, and at most `n` host calls
answered by `Spectest.host`; the stopped configuration and the log. -/
noncomputable def runHG (o : GrowOracle) (fuel : Nat) :
    Nat → Config Nat R × HostLog Nat → Option (Config Nat R × HostLog Nat)
  | 0, _ => none
  | n + 1, (c, l) =>
    match WasmWastLink.runG o fuel c with
    | none => none
    | some c' =>
      match decompose? c'.store c'.code with
      | some (E, _, k, args) =>
        if Spectest.answers c'.store k then
          runHG o fuel n (⟨c'.store, c'.frame, E.fill []⟩, l ++ [(k, args)])
        else some (c', l)
      | none => some (c', l)

/-- Link, instantiate and run the start code of `m`: the stopped configuration, the log and the
instance. -/
noncomputable def instG (o : GrowOracle) (fuel : Nat) (ctx : CtxR R) (m : Module) :
    Option ((Config Nat R × HostLog Nat) × ModuleInst) :=
  match validate? m with
  | none => none
  | some mt =>
    match resolve? ctx.regs ctx.store m.imports with
    | none => none
    | some (s₀, xas) =>
      if externAddrsOk? s₀ xas mt.imports then
        match instantiateOnce? s₀ m xas with
        | some (s, f, st) =>
          (runHG o fuel fuel (⟨s, f, startCode st⟩, ctx.log)).map fun p => (p, f.module)
        | none => none
      else none

/-- `m` is valid and its imports do not resolve to addresses of its import types. -/
def unlinkableG (ctx : CtxR R) (m : Module) : Bool :=
  match validate? m with
  | some mt =>
    match resolve? ctx.regs ctx.store m.imports with
    | none => true
    | some (s₀, xas) => !externAddrsOk? s₀ xas mt.imports
  | none => false

/-- Run an action: its result, the next store and the next log. -/
noncomputable def actG (o : GrowOracle) (fuel : Nat) (ctx : CtxR R) :
    Action → Option (Result × Store Nat R × HostLog Nat)
  | .invoke t name args =>
    match ctx.inst? t with
    | some mi =>
      match exportFunc? mi name with
      | some a =>
        if invokeOkB ctx.store a args then
          (runHG o fuel fuel (invoke ctx.store a args, ctx.log)).bind fun p =>
            p.1.outcome?.map fun r => (r, p.1.store, p.2)
        else none
      | none => none
    | none => none
  | .get t name =>
    match ctx.inst? t with
    | some mi =>
      match exportAddr? mi name with
      | some (.global a) =>
        ctx.store.globals[a]?.map fun gi => (.values [gi.value], ctx.store, ctx.log)
      | _ => none
    | none => none

/-- Run the commands from `ctx`, checking each claim. -/
noncomputable def cmdsG (o : GrowOracle) (fuel : Nat) : CtxR R → List Cmd → Bool
  | _, [] => true
  | ctx, .module name m :: cmds =>
    match instG o fuel ctx m with
    | some ((c, l), mi) =>
      let ctx' : CtxR R :=
        { ctx with store := c.store, log := l, cur := some mi, named := bindName name mi ctx.named }
      decide (c.outcome? = some (.values [])) && cmdsG o fuel ctx' cmds
    | none => false
  | ctx, .register as t :: cmds =>
    match ctx.inst? t with
    | some mi => cmdsG o fuel { ctx with regs := (as, .inst mi) :: ctx.regs } cmds
    | none => false
  | ctx, .action act e :: cmds =>
    match actG o fuel ctx act with
    | some (r, s, l) =>
      (match e with
        | some e => decide (r = e.result)
        | none => true) && cmdsG o fuel { ctx with store := s, log := l } cmds
    | none => false
  | ctx, .unlinkable m claim :: cmds => (!claim || unlinkableG ctx m) && cmdsG o fuel ctx cmds
  | ctx, .uninstantiable m claim :: cmds =>
    match instG o fuel ctx m with
    | some ((c, l), _) =>
      match c.outcome? with
      | some r => (!claim || decide (r = .trap)) &&
          cmdsG o fuel { ctx with store := c.store, log := l } cmds
      | none => false
    | none => false

/-- Run the commands from `ctx` without checking their claims: the final context. -/
noncomputable def runCmdsG (o : GrowOracle) (fuel : Nat) : CtxR R → List Cmd → Option (CtxR R)
  | ctx, [] => some ctx
  | ctx, .module name m :: cmds =>
    match instG o fuel ctx m with
    | some ((c, l), mi) =>
      if c.outcome? = some (.values []) then
        runCmdsG o fuel
          { ctx with store := c.store, log := l, cur := some mi, named := bindName name mi ctx.named }
          cmds
      else none
    | none => none
  | ctx, .register as t :: cmds =>
    match ctx.inst? t with
    | some mi => runCmdsG o fuel { ctx with regs := (as, .inst mi) :: ctx.regs } cmds
    | none => none
  | ctx, .action act _ :: cmds =>
    match actG o fuel ctx act with
    | some (_, s, l) => runCmdsG o fuel { ctx with store := s, log := l } cmds
    | none => none
  | ctx, .unlinkable _ _ :: cmds => runCmdsG o fuel ctx cmds
  | ctx, .uninstantiable m _ :: cmds =>
    match instG o fuel ctx m with
    | some ((c, l), _) =>
      if c.outcome?.isSome then runCmdsG o fuel { ctx with store := c.store, log := l } cmds
      else none
    | none => none

/-- The host-call log after the commands, from the initial context on the empty store `s₀`. -/
noncomputable def logG (o : GrowOracle) (fuel : Nat) (s₀ : Store Nat R) (cmds : List Cmd) :
    Option (HostLog Nat) :=
  match validate? Spectest.shared with
  | some mt =>
    if mt.imports.isEmpty then
      match instantiateOnce? s₀ Spectest.shared [] with
      | some (s, f, none) =>
        (runCmdsG o fuel { store := s, regs := [("spectest", .spectest f.module)] } cmds).map
          (·.log)
      | _ => none
    else none
  | none => none

/-- Validate `Spectest.shared` (no imports), instantiate it in the empty store `s₀`, bind
`"spectest"`, and run the commands. -/
noncomputable def scriptG (o : GrowOracle) (fuel : Nat) (s₀ : Store Nat R) (cmds : List Cmd) :
    Bool :=
  match validate? Spectest.shared with
  | some mt =>
    mt.imports.isEmpty &&
      match instantiateOnce? s₀ Spectest.shared [] with
      | some (s, f, none) =>
        cmdsG o fuel { store := s, regs := [("spectest", .spectest f.module)] } cmds
      | _ => false
  | none => false

end Checker

open Silmaril.Wasm.Execution (KMem) in
/-- **The kernel log checker**: `logG` on `KMem` stores, from the empty store. -/
noncomputable def logHK (o : GrowOracle) (fuel : Nat) (cmds : List Cmd) : Option (HostLog Nat) :=
  logG (R := KMem) o fuel importStoreKM cmds

open Silmaril.Wasm.Execution (KMem) in
/-- **The kernel checker**: `scriptG` on `KMem` stores, from the empty store. -/
noncomputable def scriptHK (o : GrowOracle) (fuel : Nat) (cmds : List Cmd) : Bool :=
  scriptG (R := KMem) o fuel importStoreKM cmds

end Silmaril.Project.Shapes.WasmWastHost

end
