module

public import Silmaril.Wasm.Spec.Auto.Defs
public import Silmaril.Proofs.Wasm.Spec.Auto.Basic

@[expose] public section

/-!
# Automation: the property registry, results

Proofs in `Silmaril.Proofs.Wasm.Spec.Auto.Basic`.

* `neverCallFrom_of_neverCall` (generic in the semantics).
* **`Reduces.sound`**: every reduction of tasks is sound, including **harness reduction** of a
  return postcondition to `assertNeverFalse` of the linkage with the most general return harness
  (`wasm_harness_iff`); `ModReduces.sound`; **`Task.reduce_sound`**: the normaliser is sound.
* The `wasm_spec` simp set: `models_neverCall_iff`, `models_callPre_iff`, `models_retPost_iff`,
  `models_neverCallFrom_iff`, `models_assertNeverFalse_iff`, `models_exportHist_iff`,
  `models_act_iff` (satisfaction at a program as trace conditions), and
  `models_ltlMax_neverCall_iff`, `models_ltlFin_neverCall_iff`, `models_tla_neverCall_iff`,
  `models_ltlMax_assert_iff`, `models_tla_assert_iff` (temporal images of simple sentences,
  back along the logic maps of `Silmaril.Wasm.Spec.Embed`).

The verifier dispatch, the `wasm_spec` and `wasm_spec_refute` tactics and litmus tests are in
`Silmaril.Wasm.Spec.Auto.Verify.Thms`.
-/
