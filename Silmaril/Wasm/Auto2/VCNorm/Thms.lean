module

public import Silmaril.Proofs.Wasm.Auto2.VCNorm.Basic

/-!
# The normaliser of VC generator 4: results

Proofs in `Silmaril.Proofs.Wasm.Auto2.VCNorm.Basic`, for `Silmaril.Wasm.Auto2.VCNorm.Defs`:

* `Tm.den_norm`, `Fm.den_norm`, `valid_norm`: normalisation preserves the meaning;
* `Tm.den_rn`, `Fm.den_rn`, `valid_rn`: a renaming of the variables is a change of environment,
  so it preserves validity;
* **`valid_of_accepts`**, **`allValid_of_coveredN`**: every condition the check accepts against
  valid conditions is valid.
-/

@[expose] public section

/--
info: 'Silmaril.Wasm.Auto2.VCGen.allValid_of_coveredN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCGen.allValid_of_coveredN
