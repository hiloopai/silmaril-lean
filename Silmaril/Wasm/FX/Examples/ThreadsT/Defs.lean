module

public import Silmaril.Wasm.Models.FXTRun.Defs
public import Silmaril.Wasm.Models.FXLComp.Defs
public import Silmaril.Wasm.FX.Examples.Threads.Defs

/-!
# The explainer's lightweight threads compiled to `StepFXT`: checkpoints of the dynamic run

The `StepFXL` programs of `Silmaril.Wasm.FX.Examples.Threads` compiled by
`Silmaril.Wasm.Models.FXLComp`. The dynamic `run` (function `9` of `dynP`) is long, so its
`StepFXT` run is checked in five segments (`Silmaril.Wasm.Models.FXTRun.segT`), between the
configurations `dynMid i` reached after the first `i` schedulers have returned, just before
`run` logs `-(i+1)`:

* the continuation store has `13 i` entries, all used (each scheduler run makes 13
  continuations and resumes each of them to the end, so none is live);
* the code is `run`'s frame and label around the rest of its compiled body (`body9`, dropping
  `9 i` instructions: `log`, `cont.new $main`, storing the argument, calling the scheduler);
* the cells are `ref.null`, the queue is empty, and the log is `dynPre i`: `-1`, the first
  scheduler's block, `-2`, … up to the `i`-th block.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples.ThreadsT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXLComp Silmaril.Wasm.FX.Examples.Threads

/-- The compiled body of the dynamic `run`. -/
def body9 : List InstrFX :=
  match fxOf dynP 2 9 with
  | some F => F.body
  | none => []

/-- The log after the first `i` schedulers (`i ≤ 4`). -/
def dynPre : Nat → List Int
  | 0 => [-1]
  | 1 => [-1] ++ syncLog
  | 2 => [-1] ++ syncLog ++ [-2] ++ ktLog
  | 3 => [-1] ++ syncLog ++ [-2] ++ ktLog ++ [-3] ++ tkLog
  | _ => [-1] ++ syncLog ++ [-2] ++ ktLog ++ [-3] ++ tkLog ++ [-4] ++ yktLog

/-- **The checkpoint** after the first `i` schedulers of the dynamic `run`. -/
def dynMid (i : Nat) : ConfigT Nat :=
  ⟨⟨storeOf dynP 2, List.replicate (13 * i) none, ⟨[], modOf dynP 2⟩,
    [.frame 0 ⟨[], modOf dynP 2⟩ [.label 0 [] ((body9.drop (9 * i)).map InstrFX.toAdmin)]]⟩,
   ⟨List.replicate 6 (.val (.ref .null)), [], logV (dynPre i)⟩⟩

end Silmaril.Wasm.FX.Examples.ThreadsT
