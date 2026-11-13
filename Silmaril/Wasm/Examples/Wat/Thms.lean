module

public import Silmaril.Proofs.Wasm.Examples.Wat.Basic
public import Silmaril.Proofs.Wasm.Examples.Wat.Funcs

/-!
# Talk-sized Wasm examples written in WAT: results

Proofs in `Silmaril.Proofs.Wasm.Examples.Wat.{Basic,Funcs}`, at every profile and for every host
relation (partial correctness and safety, `Silmaril.Wasm.Logic.Hoare.HWP`):

* `demo_funcs`, `add_addr`, `abs_addr`, `max_addr`, `sum_addr`: the instantiated store holds
  the quoted functions with their types, and the exports resolve to addresses `0‥3` (by `rfl`
  and `decide +kernel`);
* **`add_valid`**: the quoted `add` returns `x + y` in every run (`retSpec`), by symbolic
  execution directly in the logic;
* **`abs_valid`**, **`max_valid`**: `abs` returns `-x` for negative `x` and `x` otherwise,
  `max` the signed maximum; by the verification-condition generator
  (`Silmaril.Wasm.Logic.VC.FSpecValid.of_wpc`), the conditions closed by `wat_vc` alone;
* **`sum_valid`**: the `block`/`loop`/`br_if` loop returns `0 + 1 + ⋯ + n` modulo `2³²`
  (`triangle`), with the invariant `sumInv`; `wat_vc` leaves only `triangle_step`;
* `retSpec_invoke`: a valid `retSpec` read off every run of the embedder's `$invoke`;
* **`add_export`**, `abs_export`, `max_export`, `sum_export`: every run of `$invoke` of the
  export in the instantiated store can still step or has returned exactly the specified value
  with the store unchanged (it never traps or gets stuck; termination is not claimed).
-/
