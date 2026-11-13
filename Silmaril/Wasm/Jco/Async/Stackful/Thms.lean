module

public import Silmaril.Wasm.Jco.Async.Stackful.Defs
public import Silmaril.Wasm.Jco.Async.Early.Thms
public import Silmaril.Proofs.Wasm.Jco.Async.Stackful

/-!
# The stackful style after `task.return`: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Async.Stackful`.

* `asyncCallR_atomic`: the caller's view (`asyncCallR` of `Async/Early`) is the same for the
  thread with atomic waits and with waits between which other parties run: it ends at
  `task.return`.
* `atomic_srest`: a run of the atomic rest is a run of `SRest` with no other party (so `SRest`
  only adds runs).
* **The stackful stream function** (`streamThread`), from a store whose handles from `st.next` on
  are `Unused`: `streamThread_asyncCallS`: its caller's view is `asyncCallS`, so
  `asyncCallS_ok` applies (the readable end `st.next + 1`, `M`'s C convention, store `sB`);
  **`streamThread_atomic_hangs`**: with atomic waits its rest has no outcome (the wait finds no
  event and no reader can run); **`streamThread_srest`**: with the caller's `stream.read` between
  the write and the wait's return, the thread takes the writable end's event, drops it and ends
  at `sF`, where the caller's next read reports the end of the stream (`stream_eos`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store)
open Silmaril.Proofs.Wasm.Jco.Async.Early (sB sF)

variable (M : CoreInst)

/-- **The caller's view does not depend on how the thread runs after `task.return`.** -/
theorem asyncCallR_atomic {L : Type} (R core : List Flat → RM M.withStore.St (List Flat))
    (th : SThread M L) (sig : Sig) (vs : List PVal) :
    asyncCallR M R core th.atomic sig vs = asyncCallR M R core th.toSplit sig vs := rfl

/-- An atomic run of the thread is a run of `SRest` with no other party. -/
theorem atomic_srest {L : Type} (th : SThread M L) (t : Nat) (l : L) (s s' : M.withStore.St)
    (rs : List Flat) (h : th.atomic.post t l s (.ok rs s')) : SRest M th t l s s' :=
  Silmaril.Proofs.Wasm.Jco.Async.Stackful.atomic_srest M th t l s s' rs h

/-- The stackful stream function is the stream function of `Async/Early` with `closeCb`. -/
theorem streamThread_toSplit : (streamThread M).toSplit = streamSplit M := rfl

/-- The caller's view of the stackful stream function is `asyncCallS`. -/
theorem streamThread_asyncCallS (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) :
    (asyncCallK M R core (streamThread M).atomic sig vs fun _ ys _ =>
        match ys with
        | [Val.u32 h] => pure h.toNat
        | _ => RM.fail) = asyncCallS M R core sig vs := rfl

/-- **With atomic waits, the stackful stream function's rest has no outcome.** -/
theorem streamThread_atomic_hangs (st : Store) (hU : Unused st)
    (hb : 16 * (st.next + 3) + 2 < 2 ^ 32) (ws : List Val) (x : M.St)
    (o : Out M.withStore.St (List Flat)) :
    ¬ (streamThread M).atomic.post st.next (st.next + 2, ws) (x, sB st) o :=
  Silmaril.Proofs.Wasm.Jco.Async.Stackful.streamThread_atomic_hangs M st hU hb ws x o

/-- **With the caller's read between the write and the wait's return, the thread ends.** -/
theorem streamThread_srest (st : Store) (hU : Unused st) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32)
    (ws : List Val) (m : Nat) (x : M.St) :
    SRest M (streamThread M) st.next (st.next + 2, ws) (x, sB st) (x, sF st ws m) :=
  stream_rest M st hU hb ws m x

end Silmaril.Wasm.Jco.Async

/--
info: 'Silmaril.Wasm.Jco.Async.streamThread_atomic_hangs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Async.streamThread_atomic_hangs
