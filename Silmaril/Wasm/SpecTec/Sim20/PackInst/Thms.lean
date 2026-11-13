module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PackInst

/-!
# `FuncsValid` from V2 instantiation: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.PackInst`; see `docs/projects/spectec/README.md`, "utf8
".

* `funcsValid_of_storeOk`, `funcsValid_of_configOk`: `Store_ok` and `Config_ok` give
  `PackValid.FuncsValid`.
* **`funcsValid_instantiate`**, **`funcsValid_instantiate_steps`**: the store `$instantiate`
  returns from a valid store, and every store reachable from it under a `HostOk` host, has
  `FuncsValid`.
* **`invokeOkS_of_instantiate_steps`**: `BodyTyp.InvokeOkS` at such a store from bounded types
  and typed names alone.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.PackInst.funcsValid_instantiate_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.PackInst.funcsValid_instantiate_steps

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.PackInst.invokeOkS_of_instantiate_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.PackInst.invokeOkS_of_instantiate_steps
