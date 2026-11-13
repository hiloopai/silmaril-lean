module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripStep

/-!
# `Utf8Mono.Task.fwdU20` from its legs

* `noHost20_of_storeOkB`: `StoreOkB` stores hold no host function, so `step_strip20` applies at
  every `Good20BU` configuration.
* **`fwdU20_of_legs`**: `Task.goodStrip20`, `Task.goodUnstrip20` and `Task.unstripStep20` give
  `Utf8Mono.Task.fwdU20`. A step `c → c'` from a `Good20BU` configuration strips to a step between
  `Good20B` configurations (`step_strip20`, leg 2); `StoreBulk.fwd_good20B` makes it a step of
  `simEnv20T` and its successor `Good20B`; `Utf8Else.sstepB_utf8_20T` moves it to `utf8Env20T`;
  leg 3 un-strips it, and the successor half of leg 2 gives `Good20BU` of `c'`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Strip

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (Good20B StoreOkB fwd_good20B)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (Good20BU utf8Env20T storeB_utf8)

variable {H : Type}

/-- **`StoreOkB` stores hold no host function.** -/
theorem noHost20_of_storeOkB {s : Store H} (hs : StoreOkB s) : NoHost20 s :=
  fun _ _ _ hf hc => hs.not_host hf hc

/-- **`Utf8Mono.Task.fwdU20` from its three legs.** -/
theorem fwdU20_of_legs (h₂ : Task.goodStrip20) (h₂' : Task.goodUnstrip20)
    (h₃ : Task.unstripStep20) : Utf8Mono.Task.fwdU20 := by
  intro H hn P host c c' hg hs
  have hs₀ : Step P host (stripConfig20 c) (stripConfig20 c') :=
    step_strip20 hs (noHost20_of_storeOkB hg.store)
  have hg₀ : Good20B hn P (stripConfig20 c) := h₂ H hn P c hg
  obtain ⟨hg₀', hT⟩ : Good20B hn P (stripConfig20 c') ∧
      SStepB (simEnv20T (Whole.storeB P)) (configV hn (stripConfig20 c))
        (configV hn (stripConfig20 c')) := fwd_good20B hg₀ hs₀
  have hU : SStepB (utf8Env20T (Whole.storeB P)) (configV hn (stripConfig20 c))
      (configV hn (stripConfig20 c')) := Utf8Else.sstepB_utf8_20T (storeB_utf8 P) hT
  exact ⟨h₂' H hn P host c c' hg hs hg₀', h₃ H hn P host c c' hg hs hU⟩

end Silmaril.Wasm.SpecTec.Sim20.Utf8Strip
