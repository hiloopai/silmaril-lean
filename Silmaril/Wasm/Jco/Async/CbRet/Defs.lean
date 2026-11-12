module

public import Silmaril.Wasm.Jco.Async.Early.Defs

/-!
# `task.return` called from a callback

In the callback style of `canon lift async` (`definitions.py` at `a25fc0b`) the task may call
`task.return` from its **callback**, not only from the core function: the core function returns
`YIELD` or `WAIT`, and a later call of the callback delivers the results. The caller continues as
soon as `task.return` runs; the task goes on running.

`Silmaril.Wasm.Jco.Async.asyncCallR` (`Async/Early`) covers bodies that call `task.return` before
their first callback code. This module adds the callback case:

* `CbSplit M L`: the body after `M`'s core function, as `pre t ws` (the first callback code and
  local data `l : L`) and the callback `cb t l`. The local data stand for what the instance keeps
  in its memory between the core function and its callbacks (here: the values to return).
* `EarlyDrive cb t rs`: the runtime's callback loop **up to the task's `task.return`**: it stops,
  with the values and the next callback code, as soon as the task `t` holds results (before
  running the code `rs`); otherwise it runs `rs` as `Drive` does. `EXIT` before `task.return`
  traps.
* `asyncCallC R core b sig vs`: the caller's view: the task starts, the arguments are lowered,
  `core` runs, its results are lifted, `pre` runs, the loop runs up to `task.return`, and the
  caller reads the values at the result type. The rest of the loop belongs to the callee
  (`Finish`, from the code `EarlyDrive` stops at).
* `retCb ex`: the body yields at once (`YIELD`); the callback calls `task.return` of the values and
  returns the code `ex` (for example `EXIT`).
* `pipeCb ex`: the body passes the values through a stream, joins the writable end to a new set
  and returns `WAIT`; the callback calls `task.return` on the event.
* `CbSplit.asEpi`: the body as an epilogue of `asyncCall` (stackful), so that the results of
  `Async/Wait` apply.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat Val)

namespace Async

open Silmaril.Wasm.Component.Async (Store Event Waits)

variable (M : CoreInst)

/-- **A task body whose callback may call `task.return`**: `pre t ws` returns the first callback
code and local data; `cb t l` is the callback. -/
structure CbSplit (L : Type) where
  pre : Nat → List Val → RM M.withStore.St (List Flat × L)
  cb : Nat → L → List Flat → RM M.withStore.St (List Flat)

/-- **The callback loop up to `task.return`** of the task `t`: once the task holds results, the
loop stops with them and the next code; before that, `EXIT` traps and the other codes run as in
`Drive`. -/
inductive EarlyDrive (cb : List Flat → RM M.withStore.St (List Flat)) (t : Nat) :
    List Flat → M.withStore.St → Out M.withStore.St (List Val × List Flat) → Prop where
  | ret {rs : List Flat} {s : M.withStore.St} {ys : List Val}
      (hr : (s.2.tasks t).result = some ys) : EarlyDrive cb t rs s (.ok (ys, rs) s)
  | exitTrap {c : BitVec 32} {s : M.withStore.St} (hr : (s.2.tasks t).result = none)
      (hc : c.toNat % 16 = 0) : EarlyDrive cb t [Flat.i32 c] s .trap
  | yieldOk {c : BitVec 32} {s s₁ : M.withStore.St} {rs : List Flat} {o}
      (hr : (s.2.tasks t).result = none) (hc : c.toNat % 16 = 1)
      (h : cb [i32n 0, i32n 0, i32n 0] s (.ok rs s₁)) (hd : EarlyDrive cb t rs s₁ o) :
      EarlyDrive cb t [Flat.i32 c] s o
  | yieldTrap {c : BitVec 32} {s : M.withStore.St} (hr : (s.2.tasks t).result = none)
      (hc : c.toNat % 16 = 1) (h : cb [i32n 0, i32n 0, i32n 0] s .trap) :
      EarlyDrive cb t [Flat.i32 c] s .trap
  | waitOk {c : BitVec 32} {s s₁ : M.withStore.St} {h : Nat} {e : Event} {st' : Store}
      {rs : List Flat} {o} (hr : (s.2.tasks t).result = none) (hc : c.toNat % 16 = 2)
      (hw : Waits s.2 (c.toNat / 16) h e st')
      (hcb : cb [i32n e.code.toNat, i32n e.index, i32n e.payload] (s.1, st') (.ok rs s₁))
      (hd : EarlyDrive cb t rs s₁ o) : EarlyDrive cb t [Flat.i32 c] s o
  | waitTrap {c : BitVec 32} {s : M.withStore.St} {h : Nat} {e : Event} {st' : Store}
      (hr : (s.2.tasks t).result = none) (hc : c.toNat % 16 = 2)
      (hw : Waits s.2 (c.toNat / 16) h e st')
      (hcb : cb [i32n e.code.toNat, i32n e.index, i32n e.payload] (s.1, st') .trap) :
      EarlyDrive cb t [Flat.i32 c] s .trap
  | bad {rs : List Flat} {s : M.withStore.St} (hr : (s.2.tasks t).result = none)
      (hb : ¬ ∃ c : BitVec 32, rs = [Flat.i32 c] ∧ c.toNat % 16 ≤ 2) :
      EarlyDrive cb t rs s .trap

/-- **The caller's view of a body whose callback may call `task.return`**: it continues with the
values as soon as `task.return` ran. -/
def asyncCallC {L : Type} (R core : List Flat → RM M.withStore.St (List Flat)) (b : CbSplit M L)
    (sig : Sig) (vs : List PVal) : RM M.withStore.St (Option PVal) := do
  let t ← startTask M
  let xs ← lowerParams M.withStore R sig.params vs
  let rs ← core xs
  let v ← liftResult M.withStore sig.result rs
  let ws ← RM.ofOption (resVals v)
  let p ← b.pre t ws
  let q ← (EarlyDrive M (b.cb t p.2) t p.1 : RM M.withStore.St (List Val × List Flat))
  RM.ofOption (valsRes sig.result q.1)

/-- **`task.return` from the callback**: the body yields at once, keeping the values; the
callback calls `task.return` of them and returns the code `ex`. -/
def retCb (ex : List Flat) : CbSplit M (List Val) where
  pre _ ws := pure ([i32n cbYield], ws)
  cb t ws _ := do
    let _ ← builtin M (.taskReturn t ws)
    pure ex

/-- **The body as an epilogue of `asyncCall`** (stackful): `pre`, then the loop up to
`task.return`, then no core results. The read-back of `asyncCall` then finds the values. -/
def CbSplit.asEpi {L : Type} (b : CbSplit M L) (t : Nat) (ws : List Val) :
    RM M.withStore.St (List Flat) := do
  let p ← b.pre t ws
  let _ ← (EarlyDrive M (b.cb t p.2) t p.1 : RM M.withStore.St (List Val × List Flat))
  pure []

/-- **`task.return` from a callback, after a wait**: the body passes the values through a stream
(`stream.new`, `stream.write`, the rendezvous `stream.read`), joins the writable end to a new
set and returns `WAIT`; the callback, on the event, calls `task.return` of the items read and
returns `ex`. -/
def pipeCb (ex : List Flat) : CbSplit M (List Val) where
  pre _ ws := do
    let e ← builtin M .streamNew
    match e with
    | .ends r w =>
      let _ ← builtin M (.streamWrite w ws)
      let rd ← builtin M (.streamRead r ws.length)
      match rd with
      | .read _ ys => do
        let c ← joinWait M w
        pure (c, ys)
      | _ => RM.fail
    | _ => RM.fail
  cb := (retCb M ex).cb

end Async

end Silmaril.Wasm.Jco
