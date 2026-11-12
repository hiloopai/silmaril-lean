module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.Encode
public import Silmaril.Wasm.SpecTec.Sim.Round7.Determ.Thms

/-!
# Round 7, the export swap: `Task.swapEquiv` from the evaluator-level leaf

* `swapEquiv_of_stepErase`: `Round7.Swap.Task.stepErase → Round7.Task.swapEquiv`. The forward
  half lifts a step at the stripped image along `eraseV` and reads the successor back with
  `eq_configV_unstrip`; the backward half erases the step (`eraseV_configV`) and reads every image
  successor back the same way.
* `wholeStepValidREI_of_stepErase`: with `Round7.Determ.envAgreeNE`, the leaf gives
  `Round7.Task.wholeStepValidREI`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Swap

/-- **`Task.swapEquiv` from `Task.stepErase`.** -/
theorem swapEquiv_of_stepErase (hE : Task.stepErase) : Round7.Task.swapEquiv := by
  intro H hn hinj host hf hok hb hp nd r c ts hc hs hi
  obtain ⟨hfwd, hbwd⟩ := hE H hn hinj host hf hok hb hp nd r c ts hc hs hi
  refine ⟨fun d hd hstep => ?_, fun w hstep => ?_⟩
  · obtain ⟨w, hw, he, hstep'⟩ := hbwd d hd hstep
    rwa [← eq_configV_unstrip hn hi hd hw he]
  · obtain ⟨hw, hstep'⟩ := hfwd w hstep
    exact ⟨eraseV w, hstep', fun d hd he => eq_configV_unstrip hn hi hd hw he⟩

/-- **`Round7.Task.wholeStepValidREI` from `Task.stepErase`.** -/
theorem wholeStepValidREI_of_stepErase (hE : Task.stepErase) : Round7.Task.wholeStepValidREI :=
  Determ.wholeStepValidREI_of_swapEquiv (swapEquiv_of_stepErase hE)

end Silmaril.Wasm.SpecTec.Sim.Round7.Swap
