module

public import Silmaril.Wasm.Component.Async.Defs
public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Raw.Wasm.Component.RefZero

@[expose] public section

/-!
# Zero-length stream copies: the store model against the reference machine

`Silmaril.Wasm.Component.Async` states that it does not give zero-length copies their special
meaning. This module checks the two zero-length rendezvous used by the separating play of
`Silmaril.Wasi.Versions.P2OverP3.Sep` against the reference machine copied from `definitions.py`
(component-model `a25fc0b`): `Silmaril.Wasm.Component.Runtime.copyCore` (REF `End.copy`,
L956-979), reached through the header `Silmaril.Wasm.Component.Reference`.

PROVED (REF side, for every store with the stated ends):

* **`ref_zeroRead_meets_write`** (REF case 5): a zero-length read of a readable end whose writer
  has a parked non-empty buffer completes at once with progress `0` (its own `notify(0)`); the
  writer's end is **unchanged**: its buffer stays parked and no event is posted for it.
* **`ref_write_meets_zeroRead`** (REF case 4): a non-empty write meeting a parked zero-length
  read parks its buffer and posts **no** event for itself (the canon `stream.write` then returns
  `BLOCKED`); the reader's zero-length read completes (`notify(0)`) and its buffer is unparked.
* **`ref_own_progress_pos`**, **`ref_peer_progress_pos`** (proofs unrefined, in
  `Silmaril.Raw.Wasm.Component.RefZero`): more generally, whenever `copyCore` posts an event for the
  copying end, its buffer was empty or the recorded progress is at least `1`; and whenever it
  posts an event for the peer, the peer's parked buffer was empty or the progress is at least
  `1`. So in REF a non-empty `stream.write` (or `stream.read`) never completes with
  `COMPLETED 0`, neither on its own call nor through the other end's copy. (Cancellation and
  drops post `CANCELLED`/`DROPPED`, not `COMPLETED`; `deliverStep`.)

STORE MODEL (`Silmaril.Wasm.Component.Async`, proved in `Silmaril.Wasi.Versions.P2OverP3.Sep.Thms`):
`zeroRead_completes_write` (a zero-length read completes the parked write with `COMPLETED 0`)
and `write_meets_zeroRead` (a write meeting a pending zero-length read completes at once with
`COMPLETED 0`).

**Consequence.** The two store-model answers differ from REF in both cases. The host answers of
`sepPlay` (`waitable-set.wait` → `stream-write COMPLETED 0` for a parked write of `cap` bytes,
then `stream.write` → `COMPLETED 0` for the same non-empty buffer) are answers of the simplified
store, **not** of the reference machine: the first contradicts `ref_zeroRead_meets_write` (the
zero-length read leaves the writer parked, with no event), the second contradicts
`ref_own_progress_pos`. Neither can arise in REF in any other way (`ref_peer_progress_pos`). The separation `p2OverP3_not_strict` is a theorem about `p3Th`, which
accepts these answers; that the answers can come from a reference runtime is refuted for these
two steps.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Component.Async.RefZero

open Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.AsyncRef
open Silmaril.Wasm.Component.Engine (CoreEngine)

variable {E : CoreEngine}

/-- **REF case 5: a zero-length read meeting a parked non-empty write** completes the read with
progress `0` and leaves the writer as it was. -/
theorem ref_zeroRead_meets_write {s : CStore E} {e o : EndId} {x y : End E}
    {buf ob : BufferDesc E} (hx : s.end? e = some x) (hk : x.kind.isReadable = true)
    (ho : x.other = some o) (hne : o ≠ e) (hy : s.end? o = some y) (hb : y.buffer = some ob)
    (hob : 0 < ob.remain) (hbuf : buf.remain = 0) :
    copyCore e buf true s = .ok (setEnd s e ({ x with state := .copying }.withNotify e 0), .none) ∧
      (setEnd s e ({ x with state := .copying }.withNotify e 0)).end? o = some y := by
  have hc : copyCore e buf true s =
      .ok (setEnd s e ({ x with state := .copying }.withNotify e 0), .none) := by
    have hob' : ob.remain ≠ 0 := Nat.pos_iff_ne_zero.1 hob
    simp [copyCore, hx, hk, ho, hne, hy, hb, hbuf, hob']
  exact ⟨hc, (end?_setEnd_ne s _ hne).trans hy⟩

/-- **REF case 4: a non-empty write meeting a parked zero-length read** parks the write without
an event for it, and completes the read with progress `0`. -/
theorem ref_write_meets_zeroRead {s : CStore E} {e o : EndId} {x y : End E}
    {buf ob : BufferDesc E} (hx : s.end? e = some x) (hk : x.kind.isReadable = false)
    (ho : x.other = some o) (hne : o ≠ e) (hy : s.end? o = some y) (hb : y.buffer = some ob)
    (hob : ob.remain = 0) (hbuf : 0 < buf.remain) :
    copyCore e buf false s = .ok (setEnd (setEnd s e { x with state := .copying, buffer := some buf })
      o { y.withNotify o 0 with buffer := none }, .none) := by
  have hnot : ¬ (0 < buf.remain ∧ 0 < ob.remain) := fun h => by omega
  simp [copyCore, hx, hk, ho, hne, hy, hb, hob, hbuf]

end Silmaril.Wasm.Component.Async.RefZero
