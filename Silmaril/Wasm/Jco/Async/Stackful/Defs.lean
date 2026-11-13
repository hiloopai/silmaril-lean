module

public import Silmaril.Wasm.Jco.Async.Early.Defs

/-!
# The stackful style after `task.return`

In the stackful style of `canon lift async` (`definitions.py` at `a25fc0b`) the core function is
the task's thread: after `task.return` it may go on and block in `waitable-set.wait`, while the
caller (which continued at `task.return`) and other parties run. In `Async/Early` the rest of a
split body, `Split.post`, is one computation: a wait inside it happens with no other party in
between (it is atomic), so it can only take an event that is already pending.

This module splits the thread after `task.return` at its waits:

* `SThread M L`: `pre`, up to `task.return` (as in `Split`); `run t l`, the thread from
  `task.return` to its first `waitable-set.wait si` (the code `waitCode si`) or to its end
  (`EXIT`); `resume t l e`, the thread from the return of a wait with the event `e` (its code,
  index and payload) to the next wait or the end.
* `SThread.toSplit`: the split body whose rest is `run`; the thread is then the callback loop of
  `Async/Early` with the callback `resume t l`. `SRest th t l s s'` is that rest (`Rest`), with
  other parties interleaved between the waits.
* `SThread.atomic`: the model's earlier reading, a `Split` whose rest runs the whole thread at
  once (`run`, then `Drive` with `resume`: every wait takes an event pending at that point).
* `streamThread`: the stream function of `Async/Early` in the stackful style: after
  `task.return` of the readable end, `stream.write` (pending), `waitable-set.wait` on a set
  joined by the writable end, then `stream.drop-writable` and the end.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat Val)

namespace Async

variable (M : CoreInst)

/-- **A stackful body split at its `task.return` and at its waits.** -/
structure SThread (L : Type) where
  pre : Nat → List Val → RM M.withStore.St (List Val × L)
  run : Nat → L → RM M.withStore.St (List Flat)
  resume : Nat → L → List Flat → RM M.withStore.St (List Flat)

namespace SThread

variable {M} {L : Type} (th : SThread M L)

/-- The split body whose rest is the thread up to its first wait. -/
def toSplit : Split M L := ⟨th.pre, th.run⟩

/-- The whole thread after `task.return` as one computation: its waits are atomic. -/
def atomic : Split M L where
  pre := th.pre
  post t l := do
    let rs ← th.run t l
    let _ ← (Drive M (th.resume t l) rs : RM M.withStore.St Unit)
    pure []

end SThread

/-- **The thread after the caller continued**, with other parties between its waits. -/
def SRest {L : Type} (th : SThread M L) (t : Nat) (l : L) (s s' : M.withStore.St) : Prop :=
  Rest M th.toSplit (th.resume t l) t l s s'

/-- **The stream function in the stackful style**: `task.return` of the readable end; then
`stream.write` (pending), `waitable-set.wait` on the writable end's set; on its event,
`stream.drop-writable` and the end. -/
def streamThread : SThread M (Nat × List Val) where
  pre := (streamSplit M).pre
  run := (streamSplit M).post
  resume _ _ := closeCb M

end Async

end Silmaril.Wasm.Jco
