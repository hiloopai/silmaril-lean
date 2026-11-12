module

public import Silmaril.Wasm.Resource.CompProvider.Defs
public import Silmaril.Wasm.Component.Reference.Example.Defs
public import Silmaril.Wasm.Resource.Table.Defs

@[expose] public section

/-!
# A toy component defining a resource

A Core 3.0 component that defines a resource `r` (representation `i32`, no destructor) and
hands out representations from a counter:

```wat
(component
  (type $r (resource (rep i32)))                          ;; type 0
  (export "r" (type $r))                                  ;; type 1
  (core func $new (canon resource.new $r))                ;; core func 0
  (core func $drop (canon resource.drop $r))              ;; core func 1
  (core module $M                                         ;; core module 0
    (import "res" "new" (func (param i32) (result i32)))
    (import "res" "drop" (func (param i32)))
    (global $ctr (mut i32) (i32.const 0))
    (func (export "make") (result i32)
      global.get $ctr  i32.const -1  i32.eq  (if (then unreachable))
      global.get $ctr  global.get $ctr  i32.const 1  i32.add  global.set $ctr
      call $new)
    (func (export "get") (param i32) (result i32) local.get 0)
    (func (export "drop") (param i32) local.get 0  call $drop))
  (core instance $res (export "new" (func $new)) (export "drop" (func $drop)))
  (core instance $m (instantiate $M (with "res" (instance $res))))
  (alias core export $m "make" (core func))              ;; core func 2
  (alias core export $m "get" (core func))               ;; core func 3
  (alias core export $m "drop" (core func))              ;; core func 4
  (type (own 1)) (type (borrow 1))                        ;; types 2, 3
  (type (func (result 2)))                                ;; type 4
  (type (func (param "h" 3) (result u32)))                ;; type 5
  (type (func (param "h" 2)))                             ;; type 6
  (func (type 4) (canon lift (core func 2)))  (export "make" (func 0))
  (func (type 5) (canon lift (core func 3)))  (export "get" (func 2))
  (func (type 6) (canon lift (core func 4)))  (export "drop" (func 4)))
```

* `make` traps when the counter is at its maximum `2^32 - 1`, and otherwise calls
  `resource.new` on the counter's old value after incrementing it. An `i32` counter that wraps
  would hand out a live representation again after `2^32` calls.
* `get` receives a borrow of a resource its own instance defines; REF `lower_borrow` passes the
  bare representation, so `get` needs no `resource.rep`.
* `drop` drops the handle the lowered `own` argument was given.

`toyComp` is the component; `bugComp` is the same component whose `make` calls
`resource.new(7)` every time (`bugCore`). `toyProg`, `bugProg` are the reference programs at the
interface `Xt` (`make`, `get`, `drop`). `session c cs` runs instantiation and the export calls
`cs` with the copied executable drivers over `core3 neverFail` (`callSeq`); `twoMakes` is two
`make` calls, `toySession` is `make`, `make`, `get(borrow 0)`, `drop(own 0)`, `make`.

Over every profile `P`: `toyProgP P` (the toy over `core3P P`), `toyCtrP P` (its counter),
`silentRun` (an evaluator of silent specification programs), `toyInst P` (the configuration
after instantiation, computed by `silentRun`), `toyEs` (the exports), `ToyGarb`, `toyCfg` (the
configurations between calls: counter, instance and leftovers of earlier calls) and `toyR P`
(the reachability invariant proposed for `CtrVCOn`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource.CompToy

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Core3Adder
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

/-! ## The core modules -/

/-- The core function types: `[i32] → [i32]` (`resource.new`, `get`), `[i32] → []`
(`resource.drop`, `drop`), `[] → [i32]` (`make`), each a singleton final recursion group. -/
def coreTypes : List Silmaril.Wasm.RecType :=
  [⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩,
    ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]

/-- The body of the correct `make`: trap at the maximum, increment, `resource.new` of the old
value. -/
def makeBody : List Silmaril.Wasm.Instr :=
  [.globalGet ⟨0⟩, .intConst .i32 (-1), .intRelOp .i32 .eq, .if_ .empty [.unreachable] [],
    .globalGet ⟨0⟩, .globalGet ⟨0⟩, .intConst .i32 1, .intBinOp .i32 .add, .globalSet ⟨0⟩,
    .call ⟨0⟩]

/-- The body of the buggy `make`: `resource.new(7)`. -/
def bugMakeBody : List Silmaril.Wasm.Instr :=
  [.intConst .i32 7, .call ⟨0⟩]

/-- The core module with `make`'s body `mk`. -/
def coreWith (mk : List Silmaril.Wasm.Instr) : Silmaril.Wasm.Module where
  types := coreTypes
  imports := [⟨"res", "new", .func ⟨0⟩⟩, ⟨"res", "drop", .func ⟨1⟩⟩]
  globals := [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]
  funcs := [⟨⟨2⟩, [], mk⟩, ⟨⟨0⟩, [], [.localGet ⟨0⟩]⟩, ⟨⟨1⟩, [], [.localGet ⟨0⟩, .call ⟨1⟩]⟩]
  exports := [⟨"make", .func ⟨2⟩⟩, ⟨"get", .func ⟨3⟩⟩, ⟨"drop", .func ⟨4⟩⟩]

/-- The correct core module. -/
def toyCore : Silmaril.Wasm.Module := coreWith makeBody

/-- The buggy core module. -/
def bugCore : Silmaril.Wasm.Module := coreWith bugMakeBody

/-! ## The components -/

/-- The component over the core module `m` (see the module docstring). -/
def compOf (m : Silmaril.Wasm.Module) : Core3Component :=
  [ .type (.resource .i32 none)
  , .export_ { name := "r" } ⟨.type, 0⟩ none
  , .canon (.builtin (.resourceNew 0))
  , .canon (.builtin (.resourceDrop 0))
  , .coreModule m
  , .coreInstance (.exports [("new", ⟨.func, 0⟩), ("drop", ⟨.func, 1⟩)])
  , .coreInstance (.instantiate 0 [("res", 0)])
  , .alias (.coreExport 1 "make" .func)
  , .alias (.coreExport 1 "get" .func)
  , .alias (.coreExport 1 "drop" .func)
  , .type (.val (.own 1))
  , .type (.val (.borrow 1))
  , .type (.func { params := [], result := some (.idx 2) })
  , .type (.func { params := [("h", .idx 3)], result := some (.prim .u32) })
  , .type (.func { params := [("h", .idx 2)], result := none })
  , .canon (.lift 2 [] 4)
  , .export_ { name := "make" } ⟨.func, 0⟩ none
  , .canon (.lift 3 [] 5)
  , .export_ { name := "get" } ⟨.func, 2⟩ none
  , .canon (.lift 4 [] 6)
  , .export_ { name := "drop" } ⟨.func, 4⟩ none ]

/-- The toy component. -/
def toyComp : Core3Component := compOf toyCore

/-- The buggy component: `make` returns representation `7` every time. -/
def bugComp : Core3Component := compOf bugCore

/-- The reference validator (`check?`, WASI 0.2 features) accepts `c`. -/
def accepts (c : Core3Component) : Bool :=
  match check? Silmaril.Wasm.Component.Features.p2 c with
  | .ok _ => true
  | .error _ => false

/-! ## The interface and the reference programs -/

/-- `make() -> own<r>`, `get(borrow<r>) -> u32`, `drop(own<r>)`. -/
def Xt : CIface :=
  ⟨[], [⟨[], [.own 0]⟩, ⟨[.borrow 0], [.prim .u32]⟩, ⟨[.own 0], []⟩]⟩

/-- `make`. -/
def makeE : Xt.Exp := ⟨0, by decide⟩
/-- `get`. -/
def getE : Xt.Exp := ⟨1, by decide⟩
/-- `drop`. -/
def dropE : Xt.Exp := ⟨2, by decide⟩

/-- The export names. -/
def names : Xt.Exp → String
  | ⟨0, _⟩ => "make"
  | ⟨1, _⟩ => "get"
  | _ => "drop"

/-- The engine of the executable runs: Core 3.0 with the never-failing grow oracle. -/
abbrev E0 : Engine := core3 Silmaril.Wasm.SingleThreaded.neverFail

/-- The toy as a reference program. -/
def toyProg : RefProg E0 Xt := ⟨toyComp, [], names⟩

/-- The buggy component as a reference program. -/
def bugProg : RefProg E0 Xt := ⟨bugComp, [], names⟩

/-! ## The counter -/

/-- **The counter of the toy**: the value of core global `0` (the toy's only global, allocated
first in a store holding only the toy's core instance), as an unsigned number; `0` when it is
not numeric. The measure `ctr` of the counter verification condition `CtrVCOn`. -/
def toyCtr (m : Config E0 Unit) : ℕ :=
  let cs : Silmaril.Wasm.Execution.Core.Store (CanonHost E0) := m.store.core
  match (cs.globals[0]?).map Silmaril.Wasm.Execution.Core.GlobalInst.value with
  | some (Silmaril.Wasm.Execution.Core.Val.num v) => v.bits.toNat
  | _ => 0

/-! ## Executable runs -/

/-- Run the export calls `cs` (export, arguments) as top-level calls `k, k + 1, …` from `m`,
with the copied driver; `some` of the resolved calls and the final configuration when every
call resolves. -/
def callSeq (es : List (String × FuncId)) : ℕ → List (Xt.Exp × List Val) → Config E0 Unit →
    Option (List (DoneCall Xt) × Config E0 Unit)
  | _, [], m => some ([], m)
  | k, (j, a) :: cs, m =>
    (es.lookup (names j)).bind fun f =>
      (emb.callTop first 2000 ⟨k⟩ f a m).bind fun r =>
        match r.outcome, r.config.result? ⟨k⟩ with
        | .resolved, some res =>
          (callSeq es (k + 1) cs r.config).map fun (ds, m') => (⟨j, a, res⟩ :: ds, m')
        | _, _ => none

/-- Instantiate `c` from the empty store, then run the export calls `cs`; the resolved calls
as (export, arguments, resolution). -/
def session (c : Core3Component) (cs : List (Xt.Exp × List Val)) :
    Option (List (Xt.Exp × List Val × Option (List Val))) :=
  (emb.instantiateRun first 2000 c [] (initConfig ())).bind fun (r, _, es) =>
    (callSeq es 0 cs r.config).map fun (ds, _) => ds.map fun d => (d.exp, d.args, d.res)

/-- Instantiate `c` from the empty store, then run the export calls `cs`; the counter after the
instantiation and after each call. -/
def sessionCtrs (c : Core3Component) (cs : List (Xt.Exp × List Val)) : Option (List ℕ) :=
  (emb.instantiateRun first 2000 c [] (initConfig ())).bind fun (r, _, es) =>
    let rec go : ℕ → List (Xt.Exp × List Val) → Config E0 Unit → Option (List ℕ)
      | _, [], _ => some []
      | k, (j, a) :: cs, m =>
        (callSeq es k [(j, a)] m).bind fun (_, m') => (go (k + 1) cs m').map (toyCtr m' :: ·)
    (go 0 cs r.config).map (toyCtr r.config :: ·)

/-- Two calls of `make`. -/
def twoMakes : List (Xt.Exp × List Val) := [(makeE, []), (makeE, [])]

/-- A session: `make`, `make`, `get(borrow 0)`, `drop(own 0)`, `make`. -/
def toySession : List (Xt.Exp × List Val) :=
  [(makeE, []), (makeE, []), (getE, [.borrow 0]), (dropE, [.own 0]), (makeE, [])]

/-! ## Over every profile: the reachable configurations between calls -/

/-- **A silent evaluator** of specification programs: store reads, store updates that keep the
lockdown flag at the current store, and observations; `none` at any other operation. The
observations, the result and the final configuration (whose control chain is left alone). -/
def silentRun {E : CoreEngine} {σ α : Type} :
    Canon.P E σ α → Config E σ → Option (List HostObs × α × Config E σ)
  | .pure a, m => some ([], a, m)
  | .op .get k, m => silentRun (k m.store) m
  | .op (.modify f) k, m =>
    if (f m.store).lockdown = m.store.lockdown then
      silentRun (k ()) { m with store := f m.store }
    else none
  | .op (.emit o) k, m =>
    (silentRun (k ()) (StepDefs.observe m o)).map fun (os, a, m') => (o :: os, a, m')
  | .op _ _, _ => none

variable (P : Silmaril.Wasm.Numerics.Profile)

/-- The toy as a reference program over the Core 3.0 engine at profile `P`. -/
def toyProgP : RefProg (core3P P) Xt := ⟨toyComp, [], names⟩

/-- The counter `toyCtr` over `core3P P`: core global `0` as an unsigned number. -/
def toyCtrP (m : Config (core3P P) Unit) : ℕ :=
  let cs : Silmaril.Wasm.Execution.Core.Store (CanonHost (core3P P)) := m.store.core
  match (cs.globals[0]?).map Silmaril.Wasm.Execution.Core.GlobalInst.value with
  | some (Silmaril.Wasm.Execution.Core.Val.num v) => v.bits.toNat
  | _ => 0

/-- The toy's function exports: `make`, `get`, `drop` are component functions `0`, `1`, `2`. -/
def toyEs : List (String × FuncId) := [("make", ⟨0⟩), ("get", ⟨1⟩), ("drop", ⟨2⟩)]

/-- **The configuration after instantiating the toy** at profile `P`, computed by
`silentRun` of the instantiation program from the empty store (host in control). Its fields
are read off by kernel evaluation (`Silmaril.Proofs.Wasm.Resource.CompToy.Init`); it is
irreducible for the elaborator. -/
@[irreducible] noncomputable def toyInst : Config (core3P P) Unit :=
  match silentRun (instantiateProg (E := core3P P) toyComp []) (initConfig ()) with
  | some (_, _, m) => m
  | none => initConfig ()

/-- The core store with the counter (global `0`) set to the `i32` value `c`. -/
def setCtr (cs : Silmaril.Wasm.Execution.Core.Store (CanonHost (core3P P))) (c : ℕ) :
    Silmaril.Wasm.Execution.Core.Store (CanonHost (core3P P)) :=
  { cs with globals := cs.globals.modify 0 fun g =>
      { g with value := .i32 (BitVec.ofNat 32 c) } }

/-- What earlier calls may leave behind: tasks, threads, caller records, resource handles,
saved-continuation slots, top-level calls with their resolutions and `on_cancel`s. -/
structure ToyGarb where
  tasks : List (Runtime.Task (core3P P))
  threads : List Runtime.Thread
  callers : List (Caller (core3P P))
  handles : List ResourceHandle
  conts : List (Option (Activation (core3P P) Unit))
  pending : List (CallId × FuncId × List Val)
  results : List (CallId × Option (List Val))
  cancels : List (CallId × CancelRef)

/-- No leftovers. -/
def ToyGarb.empty : ToyGarb P := ⟨[], [], [], [], [], [], [], []⟩

/-- Every resolution and every `on_cancel` belongs to an issued top-level call. A call id that
can still be invoked (not pending) has no stale resolution. -/
def ToyGarb.Ok {P : Silmaril.Wasm.Numerics.Profile} (G : ToyGarb P) : Prop :=
  (∀ x ∈ G.results, ∃ y ∈ G.pending, y.1 = x.1) ∧ (∀ x ∈ G.cancels, ∃ y ∈ G.pending, y.1 = x.1)

/-- The toy between calls: the instantiated configuration with the counter at `c`, the
component instance `ι` and the leftovers `G`. -/
noncomputable def toyCfg (c : ℕ) (ι : InstState) (G : ToyGarb P) : Config (core3P P) Unit :=
  { toyInst P with
    store := { (toyInst P).store with
      core := setCtr P (toyInst P).store.core c
      insts := [ι]
      tasks := G.tasks
      threads := G.threads
      callers := G.callers
      resHandles := G.handles }
    conts := G.conts
    pending := G.pending
    results := G.results
    cancels := G.cancels }

/-- The thread table of an instance between calls: empty, with one freed slot (the implicit
thread of the last call, slot `1`), or with two (slot `2` also held the thread of a destructor
call made during the last call). -/
def ThreadsFree (t : Table ThreadId) : Prop :=
  t = ⟨#[none], []⟩ ∨ t = ⟨#[none, none], [1]⟩ ∨ t = ⟨#[none, none, none], [1, 2]⟩

/-- A handle table with a well-formed free list (`FreeOK`) and at most `maxLength + 1` slots,
so that every index it hands out is below `2^32`. -/
def TabB (t : Table HandleEntry) : Prop := FreeOK t ∧ t.array.size ≤ Table.maxLength + 1

/-- **The reachability invariant of the toy** (the `R` of `CtrVCOn`): the exports are
`toyEs`, and the configuration is `toyCfg P c ι G` for a counter `c < 2^32`, an instance with
only a handle table and a thread table that is empty or has one freed slot (all other instance
fields at their initial values), and leftovers whose resolutions and `on_cancel`s belong to
issued calls. The handle table's contents are not constrained: the every-run program logic used
for the core functions does not count host calls, so live entries left behind are allowed (they
do not affect freshness, which only reads entries created during the call). Only its shape is
(`TabB`): `resource.new` must return an index below `2^32`, the width of the core `i32`. -/
def toyR (es : List (String × FuncId)) (m : Config (core3P P) Unit) : Prop :=
  es = toyEs ∧ ∃ c ι G, m = toyCfg P c ι G ∧ c < 2 ^ 32 ∧
    ι = { handles := ι.handles, threads := ι.threads } ∧ ThreadsFree ι.threads ∧ TabB ι.handles ∧
    G.Ok

end Silmaril.Wasm.Resource.CompToy
