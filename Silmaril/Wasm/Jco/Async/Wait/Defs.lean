module

public import Silmaril.Wasm.Jco.Async.Native.Defs
public import Silmaril.Wasm.Jco.Async.Frame.Defs

/-!
# Natively async bodies that wait or use streams

`Silmaril.Wasm.Jco.Async.Native` relates a natively async module to `awrap` when each async body
is the adaptor's epilogue: `M`'s export, `task.return`, then `EXIT` (or `YIELD` with a callback
answering `EXIT`). This module allows other **epilogues**: after `M`'s export and the lift of its
results to the values `ws`, a body runs an arbitrary program `E t ws` over `M.withStore` that
may call any built-in (streams, futures, waitable sets) and returns the core results the runtime
then handles (no values in the stackful style; a callback code, possibly `WAIT`, in the callback
style).

## Definitions

* `bodyWith core result E`: the body of that form. The adaptor's shim is
  `bodyWith core result (retE st)`: `task.return ws`, then the style's exit.
* `epiTail E cb sty t ws`: what happens after `M` returned: the epilogue, the runtime's
  callback loop (callback style) or check (stackful style), and the read-back of the task's
  results.
* `EpiOk E cb sty st`: started in the store `st` (on the fresh task the runtime creates there),
  the tail of `E` **returns the values `ws` faithfully**: every outcome returns `ws` and keeps
  `M`'s state, and there is one. The store may change arbitrarily.
* `visible m₀ result`: what the caller sees of an async function whose C-convention call over
  `M` is `m₀`: the values of the result, read back at the result type.
* `SameFst m₁ m₂ s`, `FstIs m v s`: from the state `s`, `m₁` and `m₂` have the same outcomes up to the
  async store: the same values with the same state of `M`, and the same traps; `m` has the
  outcomes of `v` (a computation over `M`) over `M`'s state.

Epilogues (each with its theorem in `Thms`):

* `pipeE ex`: the values go **through a stream**: `stream.new`, `stream.write w ws` (pending),
  `stream.read r |ws|` (the rendezvous completes and delivers the items), `task.return` of the
  items read, then the flat results `ex`.
* `pipeWaitE`: the same, then the body **waits**: `waitable-set.new` (set `si`),
  `waitable.join w si` (the writable end has the pending `stream-write` event of the
  rendezvous), and the code `WAIT | si << 4`. With the callback `exitCb` (answering `EXIT`),
  the runtime's loop takes an event of a member of `si` and ends.
* `waitE`: `task.return ws`, then `WAIT` on a fresh empty set. The loop never ends.
* `retE st`, `yieldE`: the epilogues of `NInst.Inlines` (exit at once; `YIELD`).

Modules: `NInst.piped M md` (every async body is `pipeE`), `NInst.pipedWait M md` (every async
body is `pipeWaitE`, callback `exitCb`). `NInst.Epilogues N md P`: every async body of `N` is
`M`'s export followed by an epilogue that returns the values faithfully from the stores `P`.

`Fresh st`: the stream allocated after the task (handle `st.next + 1`) has a fresh channel, and
the waitable set's handle `st.next + 3` fits the callback code (`16 * (st.next + 3) + 2 < 2^32`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat Val)

namespace Async

open Silmaril.Wasm.Component.Async (Store Op Res startSync)

variable (M : CoreInst)

/-- From the state `s`, `m₁` and `m₂` have the same outcomes up to the async store: the same
values with the same state of `M`, and the same traps. -/
def SameFst {α : Type} (m₁ m₂ : RM M.withStore.St α) (s : M.withStore.St) : Prop :=
  (∀ a x, (∃ t, m₁ s (.ok a ((x, t) : M.withStore.St))) ↔
      (∃ t, m₂ s (.ok a ((x, t) : M.withStore.St)))) ∧ (m₁ s .trap ↔ m₂ s .trap)

/-- `m` agrees with `v` over `M`'s state from `s`: its values and states of `M` are `v`'s outcomes
from `s.1`, and so are its traps. -/
def FstIs {α : Type} (m : RM M.withStore.St α) (v : RM M.St α) (s : M.withStore.St) : Prop :=
  (∀ a x, (∃ t, m s (.ok a ((x, t) : M.withStore.St))) ↔ v s.1 (.ok a x)) ∧
    (m s .trap ↔ v s.1 .trap)

/-- **A body with an epilogue**: `M`'s core function, the lift of its results at `result`, and the
epilogue `E t ws` on the values `ws`. -/
def bodyWith (core : List Flat → RM M.withStore.St (List Flat)) (result : Option PTy)
    (E : Nat → List Val → RM M.withStore.St (List Flat)) (t : Nat) (xs : List Flat) :
    RM M.withStore.St (List Flat) := do
  let rs ← core xs
  let v ← liftResult M.withStore result rs
  let ws ← RM.ofOption (resVals v)
  E t ws

/-- The adaptor's epilogue: `task.return ws`, then the style's exit. -/
def retE (st : Style) (t : Nat) (ws : List Val) : RM M.withStore.St (List Flat) := do
  let _ ← builtin M (.taskReturn t ws)
  pure st.exitResult

/-- The runtime's part after the core function returned: the epilogue, the callback loop or the
stackful check, and the read-back. -/
def epiTail (E : Nat → List Val → RM M.withStore.St (List Flat))
    (cb : List Flat → RM M.withStore.St (List Flat)) (sty : Style) (t : Nat) (ws : List Val) :
    RM M.withStore.St (List Val) := do
  let rs ← E t ws
  match sty with
  | .stackful => RM.check rs.isEmpty
  | .callback => Drive M cb rs
  taskResult M t

/-- **The epilogue returns the values faithfully** from the store `st`: on the fresh task, every
outcome of its tail returns `ws` and keeps `M`'s state, and there is one. -/
def EpiOk (E : Nat → List Val → RM M.withStore.St (List Flat))
    (cb : List Flat → RM M.withStore.St (List Flat)) (sty : Style) (st : Store) : Prop :=
  ∀ ws x, (∀ o, epiTail M E cb sty st.next ws (x, (startSync st).1) o →
      ∃ st', o = .ok ws (x, st')) ∧
    ∃ st', epiTail M E cb sty st.next ws (x, (startSync st).1) (.ok ws (x, st'))

/-- **What the caller of an async function sees**, when its C-convention call over `M` is `m₀`. -/
def visible (m₀ : RM M.St (Option PVal)) (result : Option PTy) : RM M.St (Option PVal) := do
  let v ← m₀
  let ws ← RM.ofOption (resVals v)
  RM.ofOption (valsRes result ws)

/-- The yielding epilogue of `NInst.Inlines`: `task.return ws`, then `YIELD`. -/
def yieldE (t : Nat) (ws : List Val) : RM M.withStore.St (List Flat) := do
  let _ ← builtin M (.taskReturn t ws)
  pure [i32n cbYield]

/-! ## Epilogues with streams and waits -/

/-- A callback that answers `EXIT`. -/
def exitCb : List Flat → RM M.withStore.St (List Flat) := fun _ => pure [i32n cbExit]

/-- The callback code `WAIT | si << 4`. -/
def waitCode (si : Nat) : List Flat := [i32n (2 + 16 * si)]

/-- **The values through a stream**: `stream.new`, `stream.write w ws`, `stream.read r |ws|`,
`task.return` of the items read; then the flat results `k w`. -/
def pipeWith (k : Nat → RM M.withStore.St (List Flat)) (t : Nat) (ws : List Val) :
    RM M.withStore.St (List Flat) := do
  let e ← builtin M .streamNew
  match e with
  | .ends r w =>
    let _ ← builtin M (.streamWrite w ws)
    let rd ← builtin M (.streamRead r ws.length)
    match rd with
    | .read _ ys =>
      let _ ← builtin M (.taskReturn t ys)
      k w
    | _ => RM.fail
  | _ => RM.fail

/-- The stream epilogue ending with the flat results `ex`. -/
def pipeE (ex : List Flat) : Nat → List Val → RM M.withStore.St (List Flat) :=
  pipeWith M fun _ => pure ex

/-- Join the waitable `w` to a new waitable set and return `WAIT` on it. -/
def joinWait (w : Nat) : RM M.withStore.St (List Flat) := do
  let r ← builtin M .wsNew
  match r with
  | .nat si =>
    let _ ← builtin M (.join w si)
    pure (waitCode si)
  | _ => RM.fail

/-- **The stream epilogue that then waits** for the writable end's event. -/
def pipeWaitE : Nat → List Val → RM M.withStore.St (List Flat) := pipeWith M (joinWait M)

/-- `task.return ws`, then `WAIT` on a new, empty waitable set. -/
def waitE (t : Nat) (ws : List Val) : RM M.withStore.St (List Flat) := do
  let _ ← builtin M (.taskReturn t ws)
  let r ← builtin M .wsNew
  match r with
  | .nat si => pure (waitCode si)
  | _ => RM.fail

/-- The store suits the stream epilogues: the channel of the stream allocated after the task is
fresh, and the waitable set's handle fits the callback code. -/
def Fresh (st : Store) : Prop :=
  st.chans (st.next + 1) = {} ∧ 16 * (st.next + 3) + 2 < 2 ^ 32

/-! ## Natively async modules with epilogues -/

/-- **A natively async module whose async bodies pass `M`'s values through a stream** (`pipeE`,
ending with the style's exit). -/
def NInst.piped (md : AMeta) : NInst M where
  body f :=
    match md.world.find? (·.sig.name == f) with
    | some ⟨sig, some st⟩ => bodyWith M (M.withStore.call f) sig.result (pipeE M st.exitResult)
    | _ => fun _ _ => RM.fail

/-- **A natively async module whose async bodies pass the values through a stream and then
wait** (`pipeWaitE`), with a callback answering `EXIT` (callback style). -/
def NInst.pipedWait (md : AMeta) : NInst M where
  body f :=
    match md.world.find? (·.sig.name == f) with
    | some ⟨sig, some _⟩ => bodyWith M (M.withStore.call f) sig.result (pipeWaitE M)
    | _ => fun _ _ => RM.fail
  callback _ := exitCb M

variable {M}

/-- **`N`'s async bodies are `M`'s export followed by an epilogue** that returns the values
faithfully from every store satisfying `P`. -/
def NInst.Epilogues (N : NInst M) (md : AMeta) (P : Store → Prop) : Prop :=
  ∀ s ∈ md.world, ∀ sty, s.async = some sty →
    ∃ E, N.body s.sig.name = bodyWith M (M.withStore.call s.sig.name) s.sig.result E ∧
      ∀ st, P st → EpiOk M E (N.callback s.sig.name) sty st

end Async

end Silmaril.Wasm.Jco
