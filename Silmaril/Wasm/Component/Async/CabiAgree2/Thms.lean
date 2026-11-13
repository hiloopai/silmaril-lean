module

public import Silmaril.Wasm.Component.Async.CabiAgree2.Defs

@[expose] public section

/-!
# Futures and guarded drops: bounded agreement at the canon level

PROVED by kernel evaluation (`decide +kernel`), for the canon-level translation of
`Silmaril.Wasm.Component.Async.CabiAgree` (handle tables, waitable sets and memory included):

* `agree_future`: one future with both ends in a waitable set; every trace of at most 5
  operations over {`future.write`, `future.read`, `poll`, `wait`} (1365 traces) gets the same
  answers, values included, from the store model and from the transcription of
  `definitions.py`, up to the first step where `definitions.py` traps and the store model
  does not.
* `agree_future_strict`: on the same family the models agree at every step (`firstDiff`),
  without stopping at a transcription trap.
* `agree_streamDrops`, `agree_futureDrops`: streams (one-item copies) and futures with both
  drops, every trace of at most 4 operations (781 traces each) that satisfies the guard
  `guardOk` (a drop only of an end without an untaken event whose peer has a copy pending)
  gets the same answers in both, up to such a trap. The guard is not vacuous
  (`guarded_counts`: 98 of 219 guarded stream traces and 126 of 247 guarded future traces
  contain a drop) and it is needed (`unguarded_differ`: without it 78 stream and 38 future
  traces differ).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Component.Async.CabiAgree

/-- **Futures**: no trace of at most 5 operations differs. -/
theorem agree_future : (upTo alphaF 5).all (fun t => compareR (preF ++ t) == none) = true := by
  decide +kernel

/-- **Stream drops, guarded**: no guarded trace of at most 4 operations differs. -/
theorem agree_streamDrops : agreeGuarded pre (upTo alphaSD 4) = true := by
  decide +kernel

/-- **Future drops, guarded**: no guarded trace of at most 4 operations differs. -/
theorem agree_futureDrops : agreeGuarded preF (upTo alphaFD 4) = true := by
  decide +kernel

/-- **Futures, strictly**: on the future family the models agree at every step, with no
transcription trap to stop at (`firstDiff`, not `compareR`). -/
theorem agree_future_strict :
    (upTo alphaF 5).all (fun t => firstDiff (preF ++ t) == none) = true := by
  decide +kernel

/-- The guard is not vacuous: 98 of the 219 guarded stream traces and 126 of the 247 guarded
future traces contain a drop. -/
theorem guarded_counts :
    (guardedWithDrop pre (upTo alphaSD 4)).length = 98 ∧
    ((upTo alphaSD 4).filter fun t => guardOk Silmaril.Wasm.Component.Async.Store.empty (pre ++ t)).length = 219 ∧
    (guardedWithDrop preF (upTo alphaFD 4)).length = 126 ∧
    ((upTo alphaFD 4).filter fun t => guardOk Silmaril.Wasm.Component.Async.Store.empty (preF ++ t)).length = 247 := by
  decide +kernel

/-- The guard is needed: without it the models differ on 78 of the 781 stream traces and on
38 of the 781 future traces (differences 1, 3, 5 and 6 of `CabiAgree`). -/
theorem unguarded_differ :
    (differing pre (upTo alphaSD 4)).length = 78 ∧ (differing preF (upTo alphaFD 4)).length = 38 := by
  decide +kernel

/-- The sizes of the families. -/
theorem families_length : (upTo alphaF 5).length = 1365 ∧ (upTo alphaSD 4).length = 781 ∧
    (upTo alphaFD 4).length = 781 := by
  decide +kernel

end Silmaril.Wasm.Component.Async.CabiAgree
