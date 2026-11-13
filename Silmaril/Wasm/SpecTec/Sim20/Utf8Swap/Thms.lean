module

public import Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8SwapFwd

/-!
# The 2.0 `$utf8` erratum by an involutive re-encoding of export lists: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.Utf8Swap`; see `docs/projects/spectec/README.md`, "utf8".

* `Utf8SwapValue`: `swapV τ` is an involution when `τ` is (`swapV_swapV`), and fixes values
  without `EXPORTS` records (`swapV_of_nxB`), which every 2.0 encoder but `moduleInstV` builds.
* `Utf8SwapEnc`: the exchange `swapS S` is an involution (`swapS_swapS`) that takes re-encodings
  back (`swapS_encV`); **`swapV_configV_exp`**: `swapV τ` of a re-encoded configuration's image is
  the original image.
* `Utf8SwapBase`, `Utf8SwapStep`: **`step_exp20`**, V2 steps commute with any re-encoding of
  export lists on host-free stores.
* `Utf8SwapTypMod`, `Utf8SwapTypCode`, `Utf8SwapGood`: **`good20B_exp`**, a `Good20BU`
  configuration whose exports are re-encoded by lists typed in `simEnv20` is `Good20B`.
* `Utf8SwapTyp`, `Utf8SwapTypEx`: typing in `utf8Env20T` of the exchanged lists, with
  `name_bnd_of_typed20U` (a `name` of `utf8Env20` is within SpecTec's bound).
* `Utf8SwapFwd`: **`fwdU20_of_swapStep20`** and **`unstripStep20_of_swapStep20`**.

Open: `Task.swapStep20`, the evaluator-level leaf.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.swapV_swapV' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.swapV_swapV

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.swapS_swapS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.swapS_swapS

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.step_exp20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.step_exp20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.good20B_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.good20B_exp

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.fwdU20_of_swapStep20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.fwdU20_of_swapStep20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.unstripStep20_of_swapStep20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.unstripStep20_of_swapStep20
