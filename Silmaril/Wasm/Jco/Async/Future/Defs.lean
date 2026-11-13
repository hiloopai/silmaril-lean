module

public import Silmaril.Wasm.Jco.Async.Early.Defs

/-!
# A function whose result is a future

`Silmaril.Wasm.Jco.Async.Early` models a function whose result is `stream<T>` (`streamSplit`): the
caller continues at `task.return` with the readable end, and the callee then writes the values.
This module does the same for **`future<T>`**, with the built-ins `future.new`, `future.write`
and `future.drop-writable` of `Silmaril.Wasm.Component.Async`:

* `futureSplit`: `future.new`, `task.return` of the readable end's handle; after the caller
  continued, `future.write` of `M`'s value on the writable end (pending until a reader reads),
  `waitable-set.new`, `waitable.join` of the writable end and `WAIT`. A future carries one value,
  so the body traps unless `M` returned exactly one (`T` is the function's result type in `Sig`).
* `asyncCallF`: the caller's view, the readable end's handle.
* `closeFCb`: **the future's callback**: on the event of the waitable `i`, it drops the writable
  end `i` (`future.drop-writable`, allowed once the value was delivered) and returns `EXIT`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat Val)

namespace Async

variable (M : CoreInst)

/-- **A function whose result is a future**: `future.new`, `task.return` of the readable end's
handle; then `M`'s value is written on the writable end, which joins a new set, and the body
waits (`WAIT`). -/
def futureSplit : Split M (Nat × List Val) where
  pre _ ws := do
    let e ← builtin M .futureNew
    match e with
    | .ends r w => pure ([Val.u32 (BitVec.ofNat 32 r)], (w, ws))
    | _ => RM.fail
  post _ l :=
    match l.2 with
    | [v] => do
      let _ ← builtin M (.futureWrite l.1 v)
      joinWait M l.1
    | _ => RM.fail

/-- The caller's view of a function whose result is a future: the readable end's handle. -/
def asyncCallF (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) : RM M.withStore.St Nat :=
  asyncCallK M R core (futureSplit M) sig vs fun _ ys _ =>
    match ys with
    | [Val.u32 h] => pure h.toNat
    | _ => RM.fail

/-- **The future's callback**: on the event of the waitable `i`, drop the writable end `i`, then
`EXIT`. -/
def closeFCb (a : List Flat) : RM M.withStore.St (List Flat) :=
  match a with
  | [_, i, _] =>
    match asI32? i with
    | some x => do
      let _ ← builtin M (.futureDropW x.toNat)
      pure [i32n cbExit]
    | none => RM.fail
  | _ => RM.fail

end Async

end Silmaril.Wasm.Jco
