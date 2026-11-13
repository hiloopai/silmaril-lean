module

public import Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Swap10Fwd

/-!
# The 1.0 `$utf8` erratum by an involutive re-encoding of export lists: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10`; see `docs/projects/spectec/README.md`, "utf8".

* `Utf8Swap10Enc`: the 1.0 encoders other than `moduleInstV` build no `EXPORTS` record; the
  exchange `swapS10 S` is an involution; **`swapV_configV_exp10`**.
* `Utf8Swap10Step`, `Utf8Swap10Inv`: **`step_exp10`** (V1 steps commute with any re-encoding of
  export lists on host-free stores) and round 4's invariants at re-encoded configurations.
* `Utf8Swap10Typ`: **`typed10_exp10`**, typing at re-encoded configurations.
* `Utf8Swap10Fwd`: **`stepFwd10U_of_swapStep10`**, the 1.0 forward step at non-empty export
  names from the leaf `Task.swapStep10` (proved as `XSwap.swapStep10_holds`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10.swapV_configV_exp10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10.swapV_configV_exp10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10.typed10_exp10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10.typed10_exp10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10.stepFwd10U_of_swapStep10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10.stepFwd10U_of_swapStep10
