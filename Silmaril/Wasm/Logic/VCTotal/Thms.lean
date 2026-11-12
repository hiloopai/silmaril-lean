module

public import Silmaril.Proofs.Wasm.Logic.VCTotal.Sound

/-!
# Total correctness from the verification-condition generator (loop-free code): results

Proofs in `Silmaril.Proofs.Wasm.Logic.VCTotal.Sound`, at every profile and for every host relation:

* **`wpc_sound_total`**: for `loops is = 0`, `wpc inv k is Q s f vs` implies
  `TWP P host s f (vals vs ++ expression is) Q` (every run terminates at an exit satisfying `Q`);
* **`TFSpecAt.of_wpc`**: a total function specification (`Silmaril.Wasm.Logic.Hoare.TFSpecAt`) from
  the generator's condition for a loop-free body, so `wat_vc` proves total correctness of
  loop-free functions (e.g. a simulator's decode-and-execute `step`) without change;
* `TFSpecAt.of_wpc_fn`, `FSpecValid.of_wpc_fn`, `wpc_sound_total_ctx`: the same with a spec
  context for calls and the body postcondition `fnPost` (which accepts `return`);
* `twp_cut`: segment-by-segment verification of long loop-free code (`cutQ`);
* `fnPost_of_bodyPost`, `bodyPost_iff_fnPost`: `Silmaril.Wasm.Logic.Exec.bodyPost` is the
  no-`return` case of `fnPost`.

`TFSpecAt.of_wpc` and `TFSpecAt.of_wpc_fn` are also available in the namespace of the predicate,
as `Silmaril.Wasm.Logic.Hoare.TFSpecAt.of_wpc(_fn)` (aliases).

* `wp_of_twp`: total correctness gives a run (`Core.WP`) for postconditions excluding traps
  and escaping exceptions, so `wpc` solves `WP`-style entries (`Silmaril.WasmSpec.Rv64*`).

Loops still need the partial `wpc_sound` (no variants in `wpc`). A Silmaril addition.
-/
