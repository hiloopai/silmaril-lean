module

public import Silmaril.Wasm.Spec.Auto.Verify.Defs
public import Silmaril.Wasm.Spec.Auto.Thms
public import Silmaril.Proofs.Wasm.Spec.Auto.Verify
public import Silmaril.Proofs.Wasm.Spec.Auto.Tactic
public import Silmaril.Proofs.Wasm.Spec.Auto.Litmus

@[expose] public section

/-!
# Automation: verifier dispatch, results

Proofs in `Silmaril.Proofs.Wasm.Spec.Auto.{Verify,Tactic,Litmus}`.

* **`ModProp.verdict_proved`**: a `proved` verdict of `ModProp.verdict m φ` means
  `φ.Satisfies P (progOf m)` at every profile `P` (from `check_neverCall`,
  `check_assertNeverFalse`, the per-export `checkFrom_neverCallFrom`, and
  `neverCallFrom_of_neverCall`);
  **`ModProp.verdict_refuted`**: a `refuted` verdict means `¬ φ.Satisfies (Profile.spec nd {})
  (progOf m)` at every specification profile (from `check_refuted_*`,
  `checkFrom_refuted_neverCallFrom`);
  `Request.sound`, `Request.refuted_sound`: the same for service requests as tasks.
* **Tactics** `wasm_spec` (verifier, registry verdicts, `neverCallFrom` per export or through
  `neverCall`,
  temporal images rewritten back, else the `wasm_spec` simp set) and `wasm_spec_refute`.
* Litmus (real Core 3.0 modules of `Silmaril.Wasm.Verify.Litmus`, every profile):
  `modDead_ltlMax`, `modDead_ltlFin`, `modDead_tla`, `modDead_neverCallFrom`,
  `modOne_tla_assert`, `modOne_ltlMax_assert`, `modDead_and`; refutations `modZero_not_assert`,
  `modZero_not_and` (specification profiles); per export, `modTwo_verdict_b`,
  `modTwo_from_b_and`, `modTwo_not_from_a`; `reduce_neverCallFrom`; components:
  `greet_task`, `greet_info`.

Only `neverCall`, `assertNeverFalse`, `neverCallFrom` and their conjunctions are decided; the
other shapes get `unknown` (they are stated and reducible, and proved by hand or through
`Silmaril.Wasm.Spec.Check`).
-/
