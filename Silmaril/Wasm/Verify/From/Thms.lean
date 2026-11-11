module

public import Silmaril.Wasm.Verify.From.Defs
public import Silmaril.Wasm.Verify.Split.Thms
public import Silmaril.Proofs.Wasm.Verify.From.Basic

@[expose] public section

/-!
# The per-export verifier: soundness

Proofs in `Silmaril.Proofs.Wasm.Verify.From.Basic`.

* `closedVB_sound`, `splitIn_of_fromB`: the certificate check gives `SplitIn` with the escaping
  set `V`, the callable set `Ce` for export `e` and `A` for the other exports (`fromSets`), and
  `Ce` avoids the import; `splitIn_of_checkFrom`.
* **`checkFrom_sound`**: if `IsInstance m mt I` and `(checkFrom m i e).verdict = .proved`, then
  `Models (neverCallFrom …) (wasmSem P) (WasmProg.ofInstance I) (i, e)` for every profile `P`;
  `checkFrom_neverCallFrom` for `progOf m` (hypotheses decidable by `decide +kernel`).
* **`checkFrom_closed_world`**: under the same hypotheses, in every Core run of a call of export
  `e` from the instance's store, against every environment, no configuration is about to call
  import `i`.
* **`checkFrom_refuted_sound`**: a `refuted` verdict is a play `[call e args, icall i args']`, so
  `neverCallFrom (i, e)` fails at every profile admitting the deterministic steps of
  `profile refOracle`; `checkFrom_refuted_sound_spec` (specification profiles),
  `checkFrom_refuted_neverCallFrom` (`progOf m`).
-/
