module

public import Silmaril.Wasm.Jco.Async.Wait.Defs

/-!
# The caller continues at `task.return`

`Silmaril.Wasm.Jco.Async.asyncCall` runs the whole task, callback loop included, before the caller
reads the results. In the Component Model (`definitions.py` at `a25fc0b`, `canon_lift` and
`canon_task_return`) the caller's continuation receives the values at `task.return`, and the
callee goes on running concurrently. A body that waits for an event only another party can cause
(for example a reader of a stream it writes) works there and never returns under `asyncCall`
(`asyncCall_waitE_noOk`).

This module models the early return for bodies **split at their `task.return`**:

* `Split M L`: an epilogue in two halves around `task.return`. After `M`'s core function and the
  lift of its results to the values `ws`, `pre t ws` runs up to `task.return` and yields the values
  `ys` it passes to `task.return` and local data `l : L` the body keeps; `post t l` is the rest of
  the body, returning the callback code (or nothing, stackful).
* `Split.epi b`: the whole epilogue, the form `asyncCall` runs (`bodyWith core result b.epi`).
  `Split.cutE b`: the epilogue cut at `task.return`, ending at once (stackful).
* `asyncCallK R core b sig vs k`: start the task, lower the arguments, run `core`, lift its results,
  run `pre`, `task.return`, then the caller's continuation `k t ys l`. `asyncCallR` is the caller's
  view at a result type (`valsRes`); `asyncCallS` is the view of a function whose result is the
  readable end of a stream (`stream<T>` in the world).
* `Finish cb rs s s'`: the callee's callback loop after the caller continued, from the code `rs`,
  **interleaved with built-ins of other parties** (`Async.step` on the store); it ends at `EXIT`.
  `Rest b cb t l s s'`: `post t l`, then `Finish`.

Bodies:

* `Split.ret post`: `task.return ws` at once, then `post`. `waitPost`: `WAIT` on a new empty set,
  so `(Split.ret waitPost).epi = waitE`.
* `pipeSplit post`: the values through a stream before `task.return` (`pipeWith` cut in two);
  `pipeSplit (fun _ w => joinWait M w)` is `pipeWaitE`.
* `streamSplit`: **a function whose result is a stream**: `stream.new`, `task.return` of the
  readable end's handle, then (after the caller continued) `stream.write` of the values on the
  writable end, `waitable-set.new`, `waitable.join` and `WAIT`. The write stays pending until a
  reader reads, so the body waits for its caller.
* `closeCb`: **a callback that does work**: on the event of the waitable `i`, it drops the
  writable end `i` (`stream.drop-writable`) and returns `EXIT`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat Val)

namespace Async

open Silmaril.Wasm.Component.Async (Store Op Res Event Waits step)

/-- **A task epilogue split at its `task.return`**: `pre t ws` runs up to `task.return` and yields
the values passed to it and local data; `post t l` is the rest of the body. -/
structure Split (M : CoreInst) (L : Type) where
  pre : Nat → List Val → RM M.withStore.St (List Val × L)
  post : Nat → L → RM M.withStore.St (List Flat)

variable (M : CoreInst)

namespace Split

variable {M} {L : Type} (b : Split M L)

/-- The whole epilogue, as `asyncCall` runs it. -/
def epi (t : Nat) (ws : List Val) : RM M.withStore.St (List Flat) := do
  let p ← b.pre t ws
  let _ ← builtin M (.taskReturn t p.1)
  b.post t p.2

/-- The epilogue cut at `task.return`, ending at once (no core results). -/
def cutE (t : Nat) (ws : List Val) : RM M.withStore.St (List Flat) := do
  let p ← b.pre t ws
  let _ ← builtin M (.taskReturn t p.1)
  pure []

/-- `task.return` of the values at once, then `post` (the local data are the values). -/
def ret (post : Nat → List Val → RM M.withStore.St (List Flat)) : Split M (List Val) where
  pre _ ws := pure (ws, ws)
  post := post

end Split

/-- **`canon lift async` with the caller continuing at `task.return`**: the task starts, the
arguments are lowered, `core` runs, its results are lifted, the first half of the epilogue runs,
`task.return` stores its values, and the caller's continuation `k t ys l` runs. The second half
of the body is left to the callee (`Rest`). -/
def asyncCallK {L β : Type} (R core : List Flat → RM M.withStore.St (List Flat)) (b : Split M L)
    (sig : Sig) (vs : List PVal) (k : Nat → List Val → L → RM M.withStore.St β) :
    RM M.withStore.St β := do
  let t ← startTask M
  let xs ← lowerParams M.withStore R sig.params vs
  let rs ← core xs
  let v ← liftResult M.withStore sig.result rs
  let ws ← RM.ofOption (resVals v)
  let p ← b.pre t ws
  let _ ← builtin M (.taskReturn t p.1)
  k t p.1 p.2

/-- **The caller's view at the result type**: the values of `task.return`, lifted. -/
def asyncCallR {L : Type} (R core : List Flat → RM M.withStore.St (List Flat)) (b : Split M L)
    (sig : Sig) (vs : List PVal) : RM M.withStore.St (Option PVal) :=
  asyncCallK M R core b sig vs fun _ ys _ => RM.ofOption (valsRes sig.result ys)

/-- **The callee after the caller continued**: its callback loop from the code `rs`, interleaved
with built-ins of other parties; it ends at `EXIT`. -/
inductive Finish (cb : List Flat → RM M.withStore.St (List Flat)) :
    List Flat → M.withStore.St → M.withStore.St → Prop where
  | exit {c : BitVec 32} (s : M.withStore.St) (hc : c.toNat % 16 = 0) :
      Finish cb [Flat.i32 c] s s
  | env {rs : List Flat} {s s' : M.withStore.St} {st' : Store} {r : Res} (op : Op)
      (h : step s.2 op = some (st', r)) (hf : Finish cb rs (s.1, st') s') : Finish cb rs s s'
  | yield {c : BitVec 32} {s s₁ s' : M.withStore.St} {rs : List Flat} (hc : c.toNat % 16 = 1)
      (h : cb [i32n 0, i32n 0, i32n 0] s (.ok rs s₁)) (hf : Finish cb rs s₁ s') :
      Finish cb [Flat.i32 c] s s'
  | wait {c : BitVec 32} {s s₁ s' : M.withStore.St} {h : Nat} {e : Event} {st' : Store}
      {rs : List Flat} (hc : c.toNat % 16 = 2) (hw : Waits s.2 (c.toNat / 16) h e st')
      (hcb : cb [i32n e.code.toNat, i32n e.index, i32n e.payload] (s.1, st') (.ok rs s₁))
      (hf : Finish cb rs s₁ s') : Finish cb [Flat.i32 c] s s'

/-- The rest of a split body after the caller continued: `post`, then the callback loop. -/
def Rest {L : Type} (b : Split M L) (cb : List Flat → RM M.withStore.St (List Flat)) (t : Nat)
    (l : L) (s s' : M.withStore.St) : Prop :=
  ∃ rs s₁, b.post t l s (.ok rs s₁) ∧ Finish M cb rs s₁ s'

/-! ## Bodies -/

/-- `WAIT` on a new waitable set (nothing joins it). -/
def waitPost (_ : Nat) (_ : List Val) : RM M.withStore.St (List Flat) := do
  let r ← builtin M .wsNew
  match r with
  | .nat si => pure (waitCode si)
  | _ => RM.fail

/-- The values through a stream, up to `task.return`: `stream.new`, `stream.write w ws`,
`stream.read r |ws|`; it yields the items read and the writable end. -/
def pipePre (_ : Nat) (ws : List Val) : RM M.withStore.St (List Val × Nat) := do
  let e ← builtin M .streamNew
  match e with
  | .ends r w =>
    let _ ← builtin M (.streamWrite w ws)
    let rd ← builtin M (.streamRead r ws.length)
    match rd with
    | .read _ ys => pure (ys, w)
    | _ => RM.fail
  | _ => RM.fail

/-- `pipeWith` split at its `task.return`. -/
def pipeSplit (post : Nat → Nat → RM M.withStore.St (List Flat)) : Split M Nat where
  pre := pipePre M
  post := post

/-- `pipeWaitE` split at its `task.return`. -/
def pipeWaitSplit : Split M Nat := pipeSplit M fun _ w => joinWait M w

/-- **A function whose result is a stream**: `stream.new`, `task.return` of the readable end's
handle; then the values are written on the writable end, which joins a new set, and the body
waits (`WAIT`). -/
def streamSplit : Split M (Nat × List Val) where
  pre _ ws := do
    let e ← builtin M .streamNew
    match e with
    | .ends r w => pure ([Val.u32 (BitVec.ofNat 32 r)], (w, ws))
    | _ => RM.fail
  post _ l := do
    let _ ← builtin M (.streamWrite l.1 l.2)
    joinWait M l.1

/-- The caller's view of a function whose result is a stream: the readable end's handle. -/
def asyncCallS (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) : RM M.withStore.St Nat :=
  asyncCallK M R core (streamSplit M) sig vs fun _ ys _ =>
    match ys with
    | [Val.u32 h] => pure h.toNat
    | _ => RM.fail

/-- **A callback that does work**: on the event of the waitable `i`, drop the writable end `i`,
then `EXIT`. -/
def closeCb (a : List Flat) : RM M.withStore.St (List Flat) :=
  match a with
  | [_, i, _] =>
    match asI32? i with
    | some x => do
      let _ ← builtin M (.streamDropW x.toNat)
      pure [i32n cbExit]
    | none => RM.fail
  | _ => RM.fail

/-- Handles from `st.next` on are unused: no table entry, fresh channel, no event, no
membership, and no waitable has joined them. -/
def Unused (st : Store) : Prop :=
  ∀ h, st.next ≤ h → st.tbl h = none ∧ st.chans h = {} ∧ st.ev h = none ∧
    st.joined h = none ∧ ∀ h', st.joined h' ≠ some h

end Async

end Silmaril.Wasm.Jco
