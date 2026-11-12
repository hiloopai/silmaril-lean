module

public import Silmaril.Proofs.Wasm.Auto2.VCCheck.Mod

/-!
# The VC stage with memory, callees and normalised conditions: results

Proofs in `Silmaril.Proofs.Wasm.Auto2.VCCheck.Mod`, for `Silmaril.Wasm.Auto2.VCCheck.Defs`:

* **`modTSpecM_of_vcCheckM`**: `vcCheckM e m j = true` gives the total every-run specification of
  export `j` (memory at entry and callees in the precondition), at every profile;
* `calleesValid`: the callees of a proved contract meet their total specifications;
* **`modMeets_of_vcCheckM`**, **`checkMeetsVCN_proved`**: for the contracts of `VcEntry` (no memory, no
  callees) the front end's `ModMeets`.
-/

@[expose] public section

/--
info: 'Silmaril.Wasm.Auto2.VCCheck.modTSpecM_of_vcCheckM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCCheck.modTSpecM_of_vcCheckM

/--
info: 'Silmaril.Wasm.Auto2.VCCheck.checkMeetsVCN_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCCheck.checkMeetsVCN_proved
