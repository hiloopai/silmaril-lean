module

public import Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.Thms

/-!
# Leg 3 of the 2.0 `$utf8` forward theorem is equivalent to the theorem itself

Round 7 split `Utf8Mono.Task.fwdU20` into three legs through export stripping and proved two of
them (`Utf8Strip.goodStrip20_holds`, `goodUnstrip20_holds`), leaving
`Utf8Strip.Task.unstripStep20`. This file records that the remaining leg carries the whole
difficulty: its conclusion is the step half of `fwdU20` itself, so

* `unstripStep20_of_fwdU20`: `fwdU20` gives leg 3 (its stripped-step hypothesis is not used);
* **`unstripStep20_iff_fwdU20`**: with round 7's `fwdU20_of_unstripStep`, the two frozen
  statements are equivalent.

So stripping did not reduce the open part of the 2.0 forward theorem under the `$utf8` erratum:
a proof of leg 3 must build or transport a `utf8Env20T` derivation at images whose modules
export non-empty names.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Leg3

open Silmaril.Wasm.SpecTec.Sim20.Utf8Strip (Task.unstripStep20 fwdU20_of_unstripStep)

/-- **`fwdU20` gives leg 3.** -/
theorem unstripStep20_of_fwdU20 (h : Utf8Mono.Task.fwdU20) : Task.unstripStep20 :=
  fun H hn P host c c' hg hs _ => (h H hn P host c c' hg hs).2

/-- **Leg 3 and the 2.0 forward theorem under the `$utf8` erratum are equivalent.** -/
theorem unstripStep20_iff_fwdU20 : Task.unstripStep20 ↔ Utf8Mono.Task.fwdU20 :=
  ⟨fwdU20_of_unstripStep, unstripStep20_of_fwdU20⟩

end Silmaril.Wasm.SpecTec.Sim20.Utf8Leg3
