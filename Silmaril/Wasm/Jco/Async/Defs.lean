module

public import Silmaril.Wasm.Jco.Wrap.Defs
public import Silmaril.Wasm.Component.Async.Defs

/-!
# Async lifts through the adaptor (part (e), first piece)

The monadic construction `Silmaril.Wasm.Jco.wrap` builds a component from a module that implements
every world function **synchronously** under the C convention. This module extends it to worlds
whose exports are lifted with `canon lift … async`, in either async ABI style of the Component
Model (`definitions.py` at `a25fc0b`, `canon_lift`):

* **stackful**: the core function runs as the task's thread, delivers its results with the
  built-in `task.return` and returns no core values;
* **callback**: the core function returns an `i32` callback code `code | (si << 4)`
  (`CallbackCode`: `EXIT = 0`, `YIELD = 1`, `WAIT = 2`); on `WAIT` the runtime waits for an
  event of the waitable set `si` and calls the `callback` function with the event's
  `(code, index, payload)`, which returns the next code; on `YIELD` it calls the callback with
  the event `none`; codes `3..15` trap.

The module `M` stays synchronous: the async **shim** of world function `f` is the synchronous
export shim of `wrap` followed by the epilogue `call $task.return` (lifting the flat results at
the result type) and, in the callback style, `i32.const 0` (`EXIT`). A shim never waits, so the
callback function of the generated component is never called.

## The state

The async built-ins act on the handle table `Silmaril.Wasm.Component.Async.Store`, which the module
`M` does not touch: the component runs over `M.St × Store` (`CoreInst.withStore`), `M`'s exports
act on the first component (`RM.liftFst`) and the built-ins on the second.

## Definitions

* `Style`, `ASig` (a world function with an optional async style), `AMeta` (metadata with
  styles); `AMeta.sync` forgets the styles, `AMeta.ofMeta` declares every function synchronous,
  `AMeta.asyncFree`.
* `builtin op`: the built-in `op` of `Silmaril.Wasm.Component.Async.step` on the store (`none` traps);
  `startTask`: the runtime's creation of the callee task (`startSync`, not entered in the
  caller's table); `taskResult t`: the results `task.return` stored for `t` (trap if none).
* `Drive cb`: the runtime's callback loop, as an inductive relation (any ready member of the
  waited set may be chosen, as in `Async.Waits`).
* `asyncCall`: `canon lift async` of a task body: start the task, lower the arguments (as the
  synchronous lift does), run the body, drive it (callback) or check it returned nothing
  (stackful), and lift the results `task.return` stored.
* `AComp`: a wrapper-style component whose lifts carry an optional async style;
  `AComp.ofComp` embeds the synchronous components; `awrap md` is the construction.

Not modelled: `MAX_FLAT_ASYNC_PARAMS`, results through memory for async functions (an async
function with a `string` or `list<u8>` result traps at `task.return`), `task.cancel`,
backpressure, threads, and a module that is itself asynchronous (it would touch the store).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat Val)

/-! ## Instances with the async store -/

/-- Run a computation on the first component of a product state. -/
def RM.liftFst {σ τ α : Type} (m : RM σ α) : RM (σ × τ) α := fun s o =>
  match o with
  | .ok a s' => s'.2 = s.2 ∧ m s.1 (.ok a s'.1)
  | .trap => m s.1 .trap

/-- The core instance `M` next to the async store: `M`'s exports act on `M`'s state. -/
def CoreInst.withStore (M : CoreInst) : CoreInst where
  St := M.St × Silmaril.Wasm.Component.Async.Store
  mem s := M.mem s.1
  setMem s m := (M.setMem s.1 m, s.2)
  call n xs := RM.liftFst (M.call n xs)

namespace Async

open Silmaril.Wasm.Component.Async (Store Op Res Event)

variable (M : CoreInst)

/-- The built-in `op` on the async store. -/
def builtin (op : Op) : RM M.withStore.St Res := do
  let s ← RM.get
  let p ← RM.ofOption (Silmaril.Wasm.Component.Async.step s.2 op)
  RM.set ((s.1, p.1) : M.withStore.St)
  pure p.2

/-- The runtime creates the callee task of an async-lifted call. -/
def startTask : RM M.withStore.St Nat := do
  let s ← RM.get
  let p := Silmaril.Wasm.Component.Async.startSync s.2
  RM.set ((s.1, p.1) : M.withStore.St)
  pure p.2

/-- The results `task.return` stored for the task `t`. -/
def taskResult (t : Nat) : RM M.withStore.St (List Val) := do
  let s ← RM.get
  RM.ofOption (s.2.tasks t).result

/-! ## Styles and metadata -/

/-- The two async ABI styles of `canon lift async`. -/
inductive Style where
  | stackful
  | callback
  deriving Repr, Inhabited, DecidableEq

/-- A world function with an optional async style (`none`: a synchronous lift). -/
structure ASig where
  sig : Sig
  async : Option Style := none
  deriving Repr, Inhabited, DecidableEq

/-- Metadata with async styles. -/
structure AMeta where
  world : List ASig
  alloc : String := "alloc"
  deriving Repr, Inhabited, DecidableEq

namespace AMeta

/-- Forget the styles. -/
def sync (md : AMeta) : Meta := ⟨md.world.map (·.sig), md.alloc⟩

/-- Every function synchronous. -/
def ofMeta (md : Meta) : AMeta := ⟨md.world.map fun s => ⟨s, none⟩, md.alloc⟩

/-- No function is lifted async. -/
def asyncFree (md : AMeta) : Bool := md.world.all fun s => s.async.isNone

end AMeta

/-! ## Results of tasks -/

/-- The values `task.return` receives for a result of the fragment (strings and lists are not
in the async fragment). -/
def resVals : Option PVal → Option (List Val)
  | none => some []
  | some (.val v) => some [v]
  | some _ => none

/-- The result of a function from the values its task returned. -/
def valsRes : Option PTy → List Val → Option (Option PVal)
  | none, [] => some none
  | some (.val _), [v] => some (some (.val v))
  | _, _ => none

/-! ## The callback loop -/

/-- `CallbackCode.EXIT`. -/
def cbExit : Nat := 0

/-- **The runtime's callback loop** from the callback code `rs` (the flat results of the last
call), relationally: `EXIT` (low four bits `0`) ends, `YIELD` calls the callback with the event `none`, `WAIT si`
waits for an event of a member of the set `si` (any ready member, `Async.Waits`) and calls the
callback with it; other codes, and non-`i32` results, trap. A wait with no ready member has no
outcome (the task stays suspended). -/
inductive Drive (cb : List Flat → RM M.withStore.St (List Flat)) :
    List Flat → M.withStore.St → Out M.withStore.St Unit → Prop where
  | exit {c : BitVec 32} (s : M.withStore.St) (hc : c.toNat % 16 = 0) :
      Drive cb [Flat.i32 c] s (.ok () s)
  | yieldOk {c : BitVec 32} {s s₁ : M.withStore.St} {rs : List Flat} {o}
      (hc : c.toNat % 16 = 1) (h : cb [i32n 0, i32n 0, i32n 0] s (.ok rs s₁))
      (hd : Drive cb rs s₁ o) : Drive cb [Flat.i32 c] s o
  | yieldTrap {c : BitVec 32} {s : M.withStore.St} (hc : c.toNat % 16 = 1)
      (h : cb [i32n 0, i32n 0, i32n 0] s .trap) : Drive cb [Flat.i32 c] s .trap
  | waitOk {c : BitVec 32} {s s₁ : M.withStore.St} {h : Nat} {e : Event}
      {st' : Store} {rs : List Flat} {o}
      (hc : c.toNat % 16 = 2) (hw : Silmaril.Wasm.Component.Async.Waits s.2 (c.toNat / 16) h e st')
      (hcb : cb [i32n e.code.toNat, i32n e.index, i32n e.payload] (s.1, st') (.ok rs s₁))
      (hd : Drive cb rs s₁ o) : Drive cb [Flat.i32 c] s o
  | waitTrap {c : BitVec 32} {s : M.withStore.St} {h : Nat} {e : Event} {st' : Store}
      (hc : c.toNat % 16 = 2) (hw : Silmaril.Wasm.Component.Async.Waits s.2 (c.toNat / 16) h e st')
      (hcb : cb [i32n e.code.toNat, i32n e.index, i32n e.payload] (s.1, st') .trap) :
      Drive cb [Flat.i32 c] s .trap
  | bad {rs : List Flat} {s : M.withStore.St}
      (hb : ¬ ∃ c : BitVec 32, rs = [Flat.i32 c] ∧ c.toNat % 16 ≤ 2) : Drive cb rs s .trap

/-! ## `canon lift async` -/

/-- **`canon lift async`** of the task body `body` (given the task id) at `sig`: start the task,
lower the arguments through `realloc`, run the body, drive it (callback style, with the callback
`cb`) or check that it returned no core values (stackful style), and lift the values its
`task.return` stored. -/
def asyncCall (realloc : List Flat → RM M.withStore.St (List Flat))
    (body : Nat → List Flat → RM M.withStore.St (List Flat))
    (cb : List Flat → RM M.withStore.St (List Flat)) (style : Style) (sig : Sig)
    (vs : List PVal) : RM M.withStore.St (Option PVal) := do
  let t ← startTask M
  let xs ← lowerParams M.withStore realloc sig.params vs
  let rs ← body t xs
  match style with
  | .stackful => RM.check rs.isEmpty
  | .callback => Drive M cb rs
  let ws ← taskResult M t
  RM.ofOption (valsRes sig.result ws)

/-- The flat results a shim returns at its end: none (stackful) or `EXIT` (callback). -/
def Style.exitResult : Style → List Flat
  | .stackful => []
  | .callback => [i32n cbExit]

/-- **The async shim**: the synchronous adaptor function `core` (the export shim of `wrap`),
then `task.return` of its results lifted at `result`, then the style's exit. -/
def shimRun (core : List Flat → RM M.withStore.St (List Flat)) (result : Option PTy)
    (style : Style) (t : Nat) (xs : List Flat) : RM M.withStore.St (List Flat) := do
  let rs ← core xs
  let v ← liftResult M.withStore result rs
  let ws ← RM.ofOption (resVals v)
  let _ ← builtin M (.taskReturn t ws)
  pure style.exitResult

/-! ## Components with async lifts -/

/-- A lift with an optional async style. For an async lift the callee is the synchronous part
of the async shim (`shimRun`). -/
structure ALift where
  lift : Lift
  async : Option Style := none
  deriving Repr, Inhabited, DecidableEq

/-- A wrapper-style component whose lifts may be async. -/
structure AComp where
  adaptor : AMod := ⟨[]⟩
  lifts : List ALift
  deriving Repr, Inhabited, DecidableEq

namespace AComp

/-- The synchronous component underneath (styles forgotten). -/
def base (c : AComp) : Comp := { adaptor := c.adaptor, lifts := c.lifts.map (·.lift) }

/-- A synchronous component, every lift synchronous. -/
def ofComp (c : Comp) : AComp := { adaptor := c.adaptor, lifts := c.lifts.map fun l => ⟨l, none⟩ }

/-- The callback function of the generated components: never called by a shim; it traps. -/
def noCallback : List Flat → RM M.withStore.St (List Flat) := fun _ => RM.fail

/-- The behaviour of calling the export `name`. -/
def callExport (c : AComp) (name : String) (vs : List PVal) :
    RM M.withStore.St (Option PVal) :=
  match c.lifts.find? (·.lift.sig.name == name) with
  | some ⟨l, none⟩ =>
    canonCall M.withStore (c.base.callRef M.withStore l.realloc)
      (c.base.callRef M.withStore l.callee) l.sig vs
  | some ⟨l, some st⟩ =>
    asyncCall M (c.base.callRef M.withStore l.realloc)
      (shimRun M (c.base.callRef M.withStore l.callee) l.sig.result st) (noCallback M) st l.sig vs
  | none => RM.fail

end AComp

/-- **The async construction**: the adaptor of `wrap md.sync`, and the lifts of `wrap md.sync`
with the styles of `md`. -/
def awrap (md : AMeta) : AComp :=
  { adaptor := adaptorOf md.sync
    lifts := (liftsFrom 0 md.sync.world).zipWith (fun l s => ⟨l, s.async⟩) md.world }

/-! ## The specification -/

/-- **`M`'s behaviour at an async world function**: the runtime starts the task, `M` computes
the result under the C convention, `task.return` stores it, and the caller reads it back. -/
def aspecCall (md : AMeta) (s : ASig) (vs : List PVal) : RM M.withStore.St (Option PVal) :=
  match s.async with
  | none => md.sync.specCall M.withStore s.sig vs
  | some _ => do
    let t ← startTask M
    let r ← md.sync.specCall M.withStore s.sig vs
    let ws ← RM.ofOption (resVals r)
    let _ ← builtin M (.taskReturn t ws)
    let ws' ← taskResult M t
    RM.ofOption (valsRes s.sig.result ws')

/-- The specification by name. -/
def aspec (md : AMeta) (name : String) (vs : List PVal) : RM M.withStore.St (Option PVal) :=
  match md.world.find? (·.sig.name == name) with
  | some s => aspecCall M md s vs
  | none => RM.fail

end Async

end Silmaril.Wasm.Jco
