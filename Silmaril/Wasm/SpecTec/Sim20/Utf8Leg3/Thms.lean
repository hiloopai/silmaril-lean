module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8Leg3

/-!
# Leg 3 of the 2.0 `$utf8` forward theorem: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.Utf8Leg3`; see `docs/projects/spectec/README.md`, "utf8
".

* **`unstripStep20_iff_fwdU20`**: `Utf8Strip.Task.unstripStep20` is equivalent to
  `Utf8Mono.Task.fwdU20`. Both remain open.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Leg3.unstripStep20_iff_fwdU20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Leg3.unstripStep20_iff_fwdU20
