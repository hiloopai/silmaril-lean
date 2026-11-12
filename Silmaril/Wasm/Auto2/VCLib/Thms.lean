module

public import Silmaril.Proofs.Wasm.Auto2.VCLib.Meets

/-!
# Contracts of the VC library: results

`Silmaril.Proofs.Wasm.Auto2.VCLib.{Conds,Meets}`:

* the proved contracts `sumEntry`, `maxEntry`, `addEntry`, `div10Entry` and the library `entries` that
  `wasm-check` searches (`wasm-check vc`, and the reference-function cases of
  `wasm-check bench`);
* **`sum_meets`**: `SumTo`'s program meets `sumRef` (the triangular numbers modulo `2^32`) at
  every profile and for both front-end relations: the `sum-ref` case of the front-end benchmark,
  which the summary stages leave unknown (a loop: the function summaries have no loops);
* `max_meets'`, `add_meets'`, `div10Mulhi_meets'`: the same for `max-ref`, `add-ref`,
  `div10-mulhi-ref` through the VC generator (they are also proved through function summaries, `max_meets`,
  `add_meets`, `div10Mulhi_meets`).
-/

@[expose] public section

/--
info: 'Silmaril.Wasm.Auto2.VCLib.sum_meets' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCLib.sum_meets

/--
info: 'Silmaril.Wasm.Auto2.VCLib.max_meets'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCLib.max_meets'

/--
info: 'Silmaril.Wasm.Auto2.VCLib.div10Mulhi_meets'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCLib.div10Mulhi_meets'
