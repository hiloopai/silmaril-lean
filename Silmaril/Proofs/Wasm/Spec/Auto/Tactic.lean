module

public import Silmaril.Proofs.Wasm.Spec.Auto.Verify

@[expose] public section

/-!
# Automation: the `wasm_spec` tactics

Defined after the lemmas they apply (`ModProp.verdict_proved`, `ModProp.verdict_refuted`, the
`@[wasm_spec]` rewriting lemmas).
-/

namespace Silmaril.Wasm.Spec.Auto

/-- **`wasm_spec`**: discharge a module sentence by the verifier. It closes `neverCall` and
`assertNeverFalse` goals about `progOf m` (`wasm_check`); `ModProp.Satisfies P (progOf m) φ`
goals by evaluating `ModProp.verdict` in the kernel; `neverCallFrom` goals through `neverCall`;
and the `ltlMax`/`ltlFin`/`tla` images of `neverCall`/`assertNeverFalse` sentences by rewriting
them back along the logic maps. Otherwise it normalises with the `wasm_spec` simp set
(satisfaction of the simple logics as trace conditions). -/
macro "wasm_spec" : tactic => `(tactic| first
  | wasm_check
  | (refine Silmaril.Wasm.Spec.Auto.ModProp.verdict_proved ?_ _; decide +kernel)
  | (refine Silmaril.Wasm.Spec.Auto.neverCallFrom_of_neverCall ?_ _; wasm_check)
  | (rw [Silmaril.Wasm.Spec.Auto.models_ltlMax_neverCall_iff]; wasm_check)
  | (rw [Silmaril.Wasm.Spec.Auto.models_ltlFin_neverCall_iff]; wasm_check)
  | (rw [Silmaril.Wasm.Spec.Auto.models_tla_neverCall_iff]; wasm_check)
  | (rw [Silmaril.Wasm.Spec.Auto.models_ltlMax_assert_iff]; wasm_check)
  | (rw [Silmaril.Wasm.Spec.Auto.models_tla_assert_iff]; wasm_check)
  | simp only [wasm_spec])

/-- **`wasm_spec_refute`**: refute a module sentence at a specification profile by the verifier
(`wasm_refute`, or `ModProp.verdict_refuted` with the verdict evaluated in the kernel). -/
macro "wasm_spec_refute" : tactic => `(tactic| first
  | wasm_refute
  | (refine Silmaril.Wasm.Spec.Auto.ModProp.verdict_refuted ?_ _; decide +kernel))

end Silmaril.Wasm.Spec.Auto
