module

public import Silmaril.Proofs.Wasm.Auto2.VCBridge.Mod

/-!
# The VC generator at the module level: results

Proofs in `Silmaril.Proofs.Wasm.Auto2.VCBridge.Mod`, for the proved contracts and the check of
`Silmaril.Wasm.Auto2.VCBridge.Defs`:

* `allValid_of_covered`: conditions among proved conditions are valid;
* **`modTSpec_of_vcCheck`**: `vcCheck e m j = true` gives the total every-run specification of
  export `j` (`ModTSpec`: every call meeting the precondition terminates without a trap and meets
  the postcondition), at every profile;
* **`modMeets_of_vcCheck`**: with a precondition that holds for all arguments and a reference
  function that agrees with every result the postcondition allows, `ModMeets R P m j f` (the
  front end's statement for reference functions) for every reflexive `R` and every profile.

Divergence is excluded (total correctness, `TFSpecAt.invoke_terminates`), so the statement is
`ModMeets` itself, not the partial-correctness reading `OrDiv` of
`Silmaril.Wasm.Auto.Bridge.meets_orDiv_of_fspecValid`.
-/

@[expose] public section

/--
info: 'Silmaril.Wasm.Auto2.VCBridge.modMeets_of_vcCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCBridge.modMeets_of_vcCheck
