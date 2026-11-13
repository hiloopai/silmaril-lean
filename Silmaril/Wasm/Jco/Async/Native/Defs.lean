module

public import Silmaril.Wasm.Jco.Async.Defs
public import Silmaril.Wasm.Jco.Thin.Canon.Defs

/-!
# Natively async modules and thin async recognition

The async construction `awrap` (`Silmaril.Wasm.Jco.Async`) wraps a **synchronous** module `M`. Its
adaptor shim adds the async epilogue: it calls `task.return` with the lifted results and then
returns the style's exit code. A **natively async** module does this itself. Its async exports
are task bodies that may call any built-in of `Silmaril.Wasm.Component.Async` (`task.return`,
streams, futures, waitable sets) and, in the callback style, return `WAIT` or `YIELD` codes to
the runtime's loop. For a natively async module no adaptor code is needed: the wrapper is
**thin**, a `canon lift … async` of each core export, with the module's own callback.

## Definitions

* `NInst M`: a natively async module over the core instance `M`. Its synchronous exports and
  its `realloc` are `M`'s exports. For each async export `f` it has a task body `body f t xs`,
  run as task `t`, and a callback `callback f`. Both act on `M.withStore`, so they may touch
  the async store.
* `NLift`, `NComp`, `NComp.callExport`: a thin component over a natively async module. A
  synchronous lift is `canonCall`, and an async lift is `asyncCall` of the body with the module's
  callback.
* `thinA md r`: the thin async wrapper (every world function lifted from the core export of its
  name, with the module's `realloc` export `r`). `recognizeThinA md r` returns it when no world
  function returns through memory, as `recognizeThin` does.
* `canonSpecA N md r`: the **native async convention**: export `name` is the `canon lift` (sync
  or async) of `N`'s core export `name`.
* `shimRunWith core result ex`: the adaptor's async epilogue ending with the flat results `ex`.
  `shimRun core result st` is `shimRunWith core result st.exitResult`.
* `NInst.Inlines N md`: `N` inlines the adaptor's epilogue. Each async export runs `M`'s export,
  calls `task.return` with the lifted results and either exits at once (the `shimRun` of
  `awrap`), or, in the callback style, returns `YIELD` while its callback answers `EXIT`. This is
  the condition under which the thin async wrapper agrees with `awrap`
  (`Silmaril.Wasm.Jco.Async.Native.Thms`).
* `NInst.inlined M md`: the module that `awrap md`'s adaptor fused into `M` would be. Its body for
  `f` is the epilogue `shimRun` of the first world function named `f`.

Not modelled: a module that waits on a waitable set in its body (`Drive` covers the runtime side
of it, but no agreement theorem is stated for such bodies), and the canonical ABI's
`MAX_FLAT_ASYNC_PARAMS`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

open Silmaril.Wasm.Component (Flat Val)

variable (M : CoreInst)

/-- A natively async core module over `M`: task bodies and callbacks of its async exports. -/
structure NInst where
  /-- The body of the async export `f`, run as task `t`, on flat arguments. -/
  body : String → Nat → List Flat → RM M.withStore.St (List Flat)
  /-- The callback function of the async export `f` (callback style). -/
  callback : String → List Flat → RM M.withStore.St (List Flat) := fun _ _ => RM.fail

/-- A `canon lift` of a core export of a natively async module. -/
structure NLift where
  sig : Sig
  callee : String
  realloc : String
  async : Option Style := none
  deriving Repr, Inhabited, DecidableEq

/-- A thin component over a natively async module: lifts only, no adaptor. -/
structure NComp where
  lifts : List NLift
  deriving Repr, Inhabited, DecidableEq

variable {M}

/-- The behaviour of export `name` of a thin component over the natively async module `N`. -/
def NComp.callExport (N : NInst M) (c : NComp) (name : String) (vs : List PVal) :
    RM M.withStore.St (Option PVal) :=
  match c.lifts.find? (·.sig.name == name) with
  | some ⟨sig, f, r, none⟩ =>
    canonCall M.withStore (M.withStore.call r) (M.withStore.call f) sig vs
  | some ⟨sig, f, r, some st⟩ =>
    asyncCall M (M.withStore.call r) (N.body f) (N.callback f) st sig vs
  | none => RM.fail

/-- **The thin async wrapper.** -/
def thinA (md : AMeta) (r : String) : NComp :=
  { lifts := md.world.map fun s => ⟨s.sig, s.sig.name, r, s.async⟩ }

/-- **Thin async recognition** (partial): the thin async wrapper when no world function returns
through memory. -/
def recognizeThinA (md : AMeta) (r : String := "cabi_realloc") : Option NComp :=
  if md.sync.thinOk then some (thinA md r) else none

/-- **The native async convention**: the canonical `canon lift` (sync or async) of `N`'s core
export of each world function. -/
def canonSpecA (N : NInst M) (md : AMeta) (r : String) (name : String) (vs : List PVal) :
    RM M.withStore.St (Option PVal) :=
  match md.world.find? (·.sig.name == name) with
  | some ⟨sig, none⟩ => canonCall M.withStore (M.withStore.call r) (M.withStore.call sig.name) sig vs
  | some ⟨sig, some st⟩ =>
    asyncCall M (M.withStore.call r) (N.body sig.name) (N.callback sig.name) st sig vs
  | none => RM.fail

variable (M)

/-- The adaptor's async epilogue, ending with the flat results `ex`. -/
def shimRunWith (core : List Flat → RM M.withStore.St (List Flat)) (result : Option PTy)
    (ex : List Flat) (t : Nat) (xs : List Flat) : RM M.withStore.St (List Flat) := do
  let rs ← core xs
  let v ← liftResult M.withStore result rs
  let ws ← RM.ofOption (resVals v)
  let _ ← builtin M (.taskReturn t ws)
  pure ex

/-- `CallbackCode.YIELD`. -/
def cbYield : Nat := 1

variable {M}

/-- **`N` inlines the adaptor's async epilogue**: for each async world function, the body is
`M`'s export followed by `task.return` and either the style's exit, or (callback style) `YIELD`
with a callback that answers `EXIT`. -/
def NInst.Inlines (N : NInst M) (md : AMeta) : Prop :=
  ∀ s ∈ md.world, ∀ sty, s.async = some sty →
    N.body s.sig.name = shimRun M (M.withStore.call s.sig.name) s.sig.result sty ∨
      (sty = .callback ∧
        N.body s.sig.name =
          shimRunWith M (M.withStore.call s.sig.name) s.sig.result [i32n cbYield] ∧
        ∀ a, N.callback s.sig.name a = pure [i32n cbExit])

variable (M)

/-- **The module `awrap md`'s adaptor fused into `M` would be**: the body of `f` is the epilogue
of the first world function named `f` (a trap if it is not async). -/
def NInst.inlined (md : AMeta) : NInst M where
  body f :=
    match md.world.find? (·.sig.name == f) with
    | some ⟨sig, some st⟩ => shimRun M (M.withStore.call f) sig.result st
    | _ => fun _ _ => RM.fail

end Silmaril.Wasm.Jco.Async
