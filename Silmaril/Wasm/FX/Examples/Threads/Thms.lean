module

public import Silmaril.Wasm.FX.Examples.Threads.Defs
public import Silmaril.Wasm.Models.FXL.Thms

/-!
# The explainer's lightweight threads print their documented output

Each trace is a closed evaluation of `runN` (checked by the kernel, `decide +kernel`), and by
determinism (`FXL.beh_eq_of_out`) it is the **only** behaviour of the program:

* **`static_beh`**: the static threads print `-1 10 20 30 11 21 31 12 22 32 -2`;
* **`dyn_beh`**: the dynamic example's `run` prints the documented output of the five schedulers
  in sequence;
* `sync_beh`, `kt_beh`, `tk_beh`, `ykt_beh`, `ytk_beh`: each scheduler alone on
  `cont.new $main` prints its block of that output.

Every run ends with an empty result list (`run` has no results).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples.Threads

open Silmaril.Wasm.Models.FXL

theorem static_run : (runN staticP staticAr 1000 (init staticP 4)).out =
    some (.done staticLog []) := by decide +kernel

/-- **Static lightweight threads**: the only behaviour prints the documented output. -/
theorem static_beh : beh staticP staticAr (init staticP 4) = {.done staticLog []} :=
  beh_eq_of_out static_run

theorem dyn_run : (runN dynP dynAr 5000 (init dynP 9)).out = some (.done dynLog []) := by
  decide +kernel

/-- **Dynamic lightweight threads, all five schedulers in sequence**: the only behaviour prints
the documented output. -/
theorem dyn_beh : beh dynP dynAr (init dynP 9) = {.done dynLog []} := beh_eq_of_out dyn_run

theorem sync_run : (runN dynP dynAr 1000 (init dynP 10)).out = some (.done syncLog []) := by
  decide +kernel

theorem kt_run : (runN dynP dynAr 1000 (init dynP 11)).out = some (.done ktLog []) := by
  decide +kernel

theorem tk_run : (runN dynP dynAr 1000 (init dynP 12)).out = some (.done tkLog []) := by
  decide +kernel

theorem ykt_run : (runN dynP dynAr 1000 (init dynP 13)).out = some (.done yktLog []) := by
  decide +kernel

theorem ytk_run : (runN dynP dynAr 1000 (init dynP 14)).out = some (.done ytkLog []) := by
  decide +kernel

/-- **The `sync` scheduler**: main runs to completion, then each thread in turn. -/
theorem sync_beh : beh dynP dynAr (init dynP 10) = {.done syncLog []} := beh_eq_of_out sync_run

/-- **The `kt` scheduler**: no yield on fork, continuation first. -/
theorem kt_beh : beh dynP dynAr (init dynP 11) = {.done ktLog []} := beh_eq_of_out kt_run

/-- **The `tk` scheduler**: no yield on fork, new thread first. -/
theorem tk_beh : beh dynP dynAr (init dynP 12) = {.done tkLog []} := beh_eq_of_out tk_run

/-- **The `ykt` scheduler**: yield on fork, continuation first. -/
theorem ykt_beh : beh dynP dynAr (init dynP 13) = {.done yktLog []} := beh_eq_of_out ykt_run

/-- **The `ytk` scheduler**: yield on fork, new thread first. -/
theorem ytk_beh : beh dynP dynAr (init dynP 14) = {.done ytkLog []} := beh_eq_of_out ytk_run

end Silmaril.Wasm.FX.Examples.Threads
