module

public import Silmaril.Wasm.Auto2.Summ2.Defs
public import Silmaril.Raw.Wasm.Auto2.Summ2.Mod

/-!
# Function summaries with the third simplifier: results

Proofs in `Silmaril.Raw.Wasm.Auto2.Summ2.{Simp,Mod}` (unrefined):

* `evX_simp3`, `evX_canon3`: the third simplifier (`rem_u` by `2^k` as a mask, shift and rotation
  counts modulo the width) preserves values;
* `out_of_sumCheckV`, **`modEquiv_of_fnCheckV`**, **`modEquiv_of_checkAmongV`**: the check proves
  `ModEquiv` at every profile, for every reflexive relation;
* **`checkAmongV_eq_K`**: `checkAmongV = checkAmongVK` (validation-free instance, closed-form
  data segments, memories compared by list recursion) when both modules validate; a certificate
  proves validity once and decides each chunk on `checkAmongVK`.
-/

@[expose] public section

/--
info: 'Silmaril.Wasm.Auto2.Summ2.modEquiv_of_checkAmongV' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Auto2.Summ2.modEquiv_of_checkAmongV

/--
info: 'Silmaril.Wasm.Auto2.Summ2.checkAmongV_eq_K' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Auto2.Summ2.checkAmongV_eq_K
