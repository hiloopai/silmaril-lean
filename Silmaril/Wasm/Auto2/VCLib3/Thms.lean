module

public import Silmaril.Proofs.Wasm.Auto2.VCLib3.Lib

/-!
# VC library, pass 3: results

`Silmaril.Proofs.Wasm.Auto2.VCLib3.Lib`:

* linear arithmetic in the normaliser: `dblShl_spec`, `dblMul_spec` (`x << 1` and `2 * x` against
  the contract of `x + x`), `add3Assoc_spec`, `add3Sub_spec` (reassociation, subtraction of a
  negation); the mutants `dblShl2Prog` and `add3MutProg` are not accepted;
* the library `entriesM3` of `wasm-check vc`.
-/

@[expose] public section

/--
info: 'Silmaril.Wasm.Auto2.VCLib3.add3Sub_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCLib3.add3Sub_spec
