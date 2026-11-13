module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecRefute

/-!
# The float-only vector operators are not typed in the 2.0 script: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.VecRefute`; see `docs/projects/spectec/README.md`, "fwd20
".

* `FloatOnly i`: `i` is `VUNOP` with `sqrt`/`ceil`/`floor`/`trunc`/`nearest`, `VBINOP` with
  `div`/`min`/`max`/`pmin`/`pmax`, or `VRELOP` with `lt`/`gt`/`le`/`ge`, at `f32x4` or `f64x2`.
* **`not_typedA_floatOnly20`**, **`not_typedA_floatOnly20T`**, `not_typedI_floatOnly20`: no such
  instruction is an `admininstr` (or `instr`) of `simEnv20 B` or `simEnv20T B`, for any `B`
  (`hasTyp` answers `false` at fuel 200, by evaluation, and `not_hasTyp_of_false`).
  `hasTyp_abs_neg20`: `abs` and `neg`, which have integer namesakes, are typed.
* **`not_good20B_floatOnly`**: no `Good20B` configuration has such an instruction in its code.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecRefute.not_typedA_floatOnly20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecRefute.not_typedA_floatOnly20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecRefute.not_typedA_floatOnly20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecRefute.not_typedA_floatOnly20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecRefute.not_good20B_floatOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecRefute.not_good20B_floatOnly
