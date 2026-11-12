module

public import Silmaril.Wasm.Auto2.VCEquiv.Defs
public import Silmaril.Raw.Wasm.Auto2.VCEquiv.Lib

/-!
# Equivalence of loops through a shared contract: results

Proofs in `Silmaril.Raw.Wasm.Auto2.VCEquiv.{Conds,Mod,Lib}` (unrefined):

* `behaviours_of_vcCheck_typed`: an export that passes `vcCheck e` returns, on every typed
  argument list, the values of a reference function the contract determines (total
  correctness: it terminates, does not trap, and its results meet the postcondition);
* **`modEquiv_of_vcEquiv`**, `modEquiv_of_vcEquivWith`, `modEquiv_of_vcEquivAny`: two exports
  checked against contracts of one functional contract are equivalent, at every profile, for
  every reflexive relation;
* `sumO3_vcs`, `sumDoWhile_vcs`: the conditions of `sum`'s Binaryen `-O3` form (with
  `Silmaril.Wasm.Auto2.VCLib.sumSpec`'s invariant) and of its guarded `do … while` form (with
  `sumDoWhileSpec`, whose invariant also says `n ≠ 0`), closed by `vcgen4` and `bv_omega`;
* the library `eqFuns`: `sumFun` (three program shapes), `maxFun`, `addFun`, `div10Fun`.

So two programs whose loops run an input-dependent number of times are proved equivalent when
each is proved, with its own invariant and variant, to compute the same function; the invariants
are annotations of the contracts, not inferred.
-/

@[expose] public section

/--
info: 'Silmaril.Wasm.Auto2.VCEquiv.modEquiv_of_vcEquivAny' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCEquiv.modEquiv_of_vcEquivAny

/--
info: 'Silmaril.Wasm.Auto2.VCEquiv.sumO3_vcs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCEquiv.sumO3_vcs

/--
info: 'Silmaril.Wasm.Auto2.VCEquiv.sumDoWhile_vcs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCEquiv.sumDoWhile_vcs
