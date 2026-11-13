module

public import Silmaril.Wasm.Component.Async.CabiAgree.Defs

@[expose] public section

/-!
# More bounded families: futures and guarded drops, at the canon level

`Silmaril.Wasm.Component.Async.CabiAgree` runs the store model and the transcription of
`definitions.py` on the same canon built-ins (one instance, one async task, handle tables
included) and proves agreement on two families of stream traces. This module adds the
families the unbounded simulations of `CabiSim`/`CabiSim2` leave out:

* **futures** (`preF`, `alphaF`): one future with both ends in a waitable set; writes, reads,
  `poll` and `wait`;
* **drops, guarded** (`guardOk`): streams and futures with `drop-readable`/`drop-writable`,
  where a drop is taken only when the dropping end has no untaken event and the peer has a
  copy pending (then both models post `DROPPED` to the peer). Without the guard the models
  differ (differences 1, 3 and 6 of `CabiAgree`).

The comparison is `CabiAgree.compareR` (agreement up to the first step where
`definitions.py` traps and the store model does not).
-/

namespace Silmaril.Wasm.Component.Async.CabiAgree

open Silmaril.Wasm.Component.Async (Op Obj Pend)

/-- One future (`r = 1`, `w = 2`) with both ends joined to the waitable set `3`. -/
def preF : List MOp := [.futureNew, .wsNew, .join 1 3, .join 2 3]

/-- Future writes and reads, `poll` and `wait`. -/
def alphaF : List MOp := [.futureWrite 2 va, .futureRead 1, .poll 3, .wait 3]

/-- Stream copies of one item, `poll`, and both drops. -/
def alphaSD : List MOp := [.streamWrite 2 [va], .streamRead 1 1, .poll 3, .streamDropR 1,
  .streamDropW 2]

/-- Future copies, `poll`, and both drops. -/
def alphaFD : List MOp := [.futureWrite 2 va, .futureRead 1, .poll 3, .futureDropR 1,
  .futureDropW 2]

/-- The peer of the end `h` has a copy pending. -/
def peerPending (m : MStore) (h : Nat) : Bool :=
  match m.tbl h with
  | some (.streamW s) | some (.futureW s) =>
    match (m.chans s).pend with
    | .read .. => true
    | _ => false
  | some (.streamR s) | some (.futureR s) =>
    match (m.chans s).pend with
    | .write .. => true
    | _ => false
  | _ => false

/-- **The guard**: every drop is of an end without an untaken event whose peer has a copy
pending (judged on the store model's state before the drop). -/
def guardOk (m : MStore) : List MOp → Bool
  | [] => true
  | o :: os =>
    let ok := match o with
      | .streamDropR h | .streamDropW h | .futureDropR h | .futureDropW h =>
        (m.ev h).isNone && peerPending m h
      | _ => true
    ok && match Silmaril.Wasm.Component.Async.step m o with
      | some (m', _) => guardOk m' os
      | none => true

/-- The drops. -/
def isDrop : MOp → Bool
  | .streamDropR _ | .streamDropW _ | .futureDropR _ | .futureDropW _ => true
  | _ => false

/-- The guarded traces of a family (after the prefix `p`) that contain a drop. -/
def guardedWithDrop (p : List MOp) (ts : List (List MOp)) : List (List MOp) :=
  ts.filter fun t => guardOk Silmaril.Wasm.Component.Async.Store.empty (p ++ t) && t.any isDrop

/-- The traces of a family on which the comparison finds a difference. -/
def differing (p : List MOp) (ts : List (List MOp)) : List (List MOp) :=
  ts.filter fun t => compareR (p ++ t) != none

/-- Agreement on every guarded trace of a family (after the prefix `p`). -/
def agreeGuarded (p : List MOp) (ts : List (List MOp)) : Bool :=
  ts.all fun t => !guardOk Silmaril.Wasm.Component.Async.Store.empty (p ++ t) ||
    compareR (p ++ t) == none

end Silmaril.Wasm.Component.Async.CabiAgree
