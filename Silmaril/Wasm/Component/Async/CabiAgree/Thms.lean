module

public import Silmaril.Wasm.Component.Async.CabiAgree.Defs

@[expose] public section

/-!
# The store model against `definitions.py`: agreement and refutations

PROVED by kernel evaluation (`decide`), for the translation of
`Silmaril.Wasm.Component.Async.CabiAgree`:

* **Agreement on uniform chunks** (`agree_alpha1`, `agree_alpha2`). On one stream with both
  ends in a waitable set, every trace of at most `5` operations over writes of one item, reads
  of one item, `poll` and `wait` (1365 traces), and the same with two items, gets the same
  answers, items included, from both models up to the first step where `definitions.py`
  traps and the store model does not (`compareR`). COMPUTED (`#eval`, not a theorem): in 880
  of the 1365 traces of each family the transcription traps at some step, so those are
  compared up to that step only; at depth `6` (5461 traces, 4004 with a trap) the families
  also agree (by `#eval`; the kernel check of depth 6 takes longer than a module may).
  The unbounded counterpart, at the level of the stream state machine (without `poll`,
  `wait` and the values read), is `Silmaril.Wasm.Component.Async.CabiSim.agree_fragment`.
* **Refutations**: concrete traces on which the models differ (`differ_*`), one per
  difference, each with both answers.

Differences found (all on the store model's side; the transcription follows `definitions.py`):

1. `differ_idleDrop`: dropping an end notifies an **idle** peer (`DROPPED`, through its
   waitable set); the store model posts nothing.
2. `differ_partialWriteParked`, `differ_partialReadParked`: after a partial rendezvous the
   larger buffer **stays parked**: the next read (write) continues from it at once; the store
   model makes the pending side complete and returns `BLOCKED`.
3. `differ_eventAtDelivery`: the copy result of an event is computed **when it is
   delivered**: a reader whose read completed but whose event was not yet taken sees
   `DROPPED` (with the count) if the writer dropped in between; the store model reports
   `COMPLETED`.
4. `differ_uncollected`: a copy on an end whose previous copy completed but whose event was
   not collected **traps** (the end is not idle); the store model accepts it.
5. `differ_afterDropped`: after an end has received `DROPPED`, a further copy **traps**; the
   store model answers `DROPPED` again.
6. `differ_futureDropW`: a future's writable end may be dropped only once **its own** write
   event was delivered; the store model allows the drop as soon as a reader took the value.
7. `differ_zeroRead`: a zero-length read leaves a pending write parked with no event (as
   `Silmaril.Wasm.Component.Async.RefZero` showed for `a25fc0b`); the store model completes the
   write with `COMPLETED 0`.
8. `differ_handleReuse`: handle indices are **reused** (last freed first); the store model
   never reuses them.
-/

namespace Silmaril.Wasm.Component.Async.CabiAgree

open Silmaril.Wasm.Component.Async (Op)

/-- **Agreement, one-item chunks**: no trace of at most 5 operations differs. -/
theorem agree_alpha1 : (upTo alpha1 5).all (fun t => compareR (pre ++ t) == none) = true := by
  decide +kernel

/-- **Agreement, two-item chunks**: no trace of at most 5 operations differs. -/
theorem agree_alpha2 : (upTo alpha2 5).all (fun t => compareR (pre ++ t) == none) = true := by
  decide +kernel

/-- The number of traces in each family. -/
theorem upTo_length : (upTo alpha1 5).length = 1365 ∧ (upTo alpha2 5).length = 1365 := by
  decide +kernel

/-- `r | w << 32` for the stream of `pre`. -/
abbrev ends12 : Nat := 1 + 2 * 2 ^ 32

/-! ## Refutations -/

/-- **1. Idle drop.** Dropping the readable end of an idle stream posts `DROPPED` for the
writable end in `definitions.py`; the store model's `poll` finds no event. -/
theorem differ_idleDrop :
    firstDiff (pre ++ [.streamDropR 1, .poll 3]) = some 5 ∧
    answersAre (pre ++ [.streamDropR 1, .poll 3]) 5 (.ret [0, 0, 0] [])
      (.ret [3, 2, 1] []) = true := by decide +kernel

/-- **2a. A partial read leaves the write parked.** After a write of two items is read one
item at a time, the second read completes at once in `definitions.py`; the store model
returns `BLOCKED`. -/
theorem differ_partialWriteParked :
    firstDiff (pre ++ [.streamWrite 2 [va, vb], .streamRead 1 1, .streamRead 1 1]) = some 6 ∧
    answersAre (pre ++ [.streamWrite 2 [va, vb], .streamRead 1 1, .streamRead 1 1]) 6
      (.ret [Cabi.BLOCKED] []) (.ret [16] [vb]) = true := by decide +kernel

/-- **2b. A partial write leaves the read parked.** -/
theorem differ_partialReadParked :
    firstDiff (pre ++ [.streamRead 1 2, .streamWrite 2 [va], .streamWrite 2 [vb]]) = some 6 ∧
    answersAre (pre ++ [.streamRead 1 2, .streamWrite 2 [va], .streamWrite 2 [vb]]) 6
      (.ret [Cabi.BLOCKED] []) (.ret [16] []) = true := by decide +kernel

/-- **3. Copy results are computed at delivery.** A completed read whose event is taken after
the writer dropped reports `DROPPED | 2 << 4` in `definitions.py`, `COMPLETED | 2 << 4` in the
store model. -/
theorem differ_eventAtDelivery :
    firstDiff (pre ++ [.streamRead 1 2, .streamWrite 2 [va, vb], .streamDropW 2, .poll 3]) =
      some 7 ∧
    answersAre (pre ++ [.streamRead 1 2, .streamWrite 2 [va, vb], .streamDropW 2, .poll 3]) 7
      (.ret [2, 1, 32] [va, vb]) (.ret [2, 1, 33] [va, vb]) = true := by decide +kernel

/-- **4. Uncollected events.** A read after a pending read was completed by a write, but
before its event was taken, traps in `definitions.py` (the end is still `COPYING`); the store
model starts a new read. -/
theorem differ_uncollected :
    firstDiff (pre ++ [.streamRead 1 2, .streamWrite 2 [va, vb], .streamRead 1 2]) = some 6 ∧
    answersAre (pre ++ [.streamRead 1 2, .streamWrite 2 [va, vb], .streamRead 1 2]) 6
      (.ret [Cabi.BLOCKED] []) .trap = true := by decide +kernel

/-- **5. After `DROPPED`.** Once the writer has received `DROPPED`, a write traps in
`definitions.py`; the store model answers `DROPPED` again. -/
theorem differ_afterDropped :
    firstDiff (pre ++ [.streamDropR 1, .poll 3, .streamWrite 2 [va]]) = some 5 ∧
    answersAre (pre ++ [.streamDropR 1, .poll 3, .streamWrite 2 [va]]) 6
      (.ret [1] []) .trap = true := by decide +kernel

/-- **6. Dropping a written future.** The writer may drop only after its own write event:
`definitions.py` traps, the store model accepts. -/
theorem differ_futureDropW :
    firstDiff [.futureNew, .futureWrite 2 va, .futureRead 1, .futureDropW 2] = some 3 ∧
    answersAre [.futureNew, .futureWrite 2 va, .futureRead 1, .futureDropW 2] 3
      (.ret [] []) .trap = true := by decide +kernel

/-- **7. Zero-length reads.** A zero-length read meeting a parked write leaves it parked
without an event in `definitions.py`; the store model completes it with `COMPLETED 0`. -/
theorem differ_zeroRead :
    firstDiff (pre ++ [.streamWrite 2 [va], .streamRead 1 0, .poll 3]) = some 6 ∧
    answersAre (pre ++ [.streamWrite 2 [va], .streamRead 1 0, .poll 3]) 6
      (.ret [3, 2, 0] []) (.ret [0, 0, 0] []) = true := by decide +kernel

/-- **8. Handle reuse.** After both ends of a stream are dropped, `stream.new` reuses their
indices (last freed first) in `definitions.py`; the store model allocates fresh ones. -/
theorem differ_handleReuse :
    firstDiff [.streamNew, .streamDropR 1, .streamDropW 2, .streamNew] = some 3 ∧
    answersAre [.streamNew, .streamDropR 1, .streamDropW 2, .streamNew] 3
      (.ret [3 + 4 * 2 ^ 32] []) (.ret [2 + 1 * 2 ^ 32] []) = true := by decide +kernel

end Silmaril.Wasm.Component.Async.CabiAgree
