module

public import Silmaril.Proofs.Wasi.Versions.P2OverP3.CliDflt

/-!
# Proofs: lifting `wasi:cli`/`wasi:clocks` answers

* `cliOk_fix` (from `cliOk_dflt` in `CliDflt`): lifting at the WIT type gives a
  well-typed answer; `cliFix_now`: the answer of
  `monotonic-clock.now` is forwarded unchanged.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions.P2

/-! ## `wasi:cli` and `wasi:clocks` -/

/-- **Lifting at the WIT type gives a well-typed answer.** -/
theorem cliOk_fix (f : FnName) (r : Option (List Val)) : cliOk f (cliFix f r) = true := by
  unfold cliFix
  split
  · assumption
  · exact cliOk_dflt f

/-- `monotonic-clock.now` is not constrained by `cliOk`. -/
theorem cliOk_now (r : Option (List Val)) : cliOk clockNow r = true := by
  rw [cliOk_eq_hand]
  unfold cliOkH
  repeat rw [ite_eq_right (by decide)]

theorem cliFix_now (r : Option (List Val)) : cliFix clockNow r = r := by
  unfold cliFix
  rw [cliOk_now, ite_eq_left rfl]

end Silmaril.Wasi.Versions.P2OverP3
