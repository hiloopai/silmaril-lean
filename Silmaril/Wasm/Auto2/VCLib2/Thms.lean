module

public import Silmaril.Proofs.Wasm.Auto2.VCLib2.Lib

/-!
# Contracts with memory and callees (VC library): results

`Silmaril.Proofs.Wasm.Auto2.VCLib2.Lib`:

* the proved contracts `doubleEntry` (a callee: `add`, read from the module and checked against
  its own contract) and `load2Entry` (memory), and the library `entriesM` of `wasm-check vc`;
* kernel-checked checks (`decide +kernel` of `vcCheckM`): `double_spec`, `doubleSwap_spec` (a
  callee with other code), `load2_spec`, `load2Swap_spec` (accepted by normalisation),
  `maxSelect_spec` and `addSwap_spec` (the front-end benchmark's `max-select` and `add-swap`
  against the `max` and `add` contracts, which the syntactic check of `VCBridge.vcCheck` leaves unknown); the
  mutants `doubleSubProg`, `load2OffProg`, `addSub` are not accepted;
* globals: `bumpEntry`, `addnEntry` (a global written in a loop), `frameEntry` (a stack pointer
  restored), kernel-checked `bump_spec`, `addn_spec`, `frame_spec`; the mutants `bumpLostProg` and
  `frameLeakProg` are not accepted.
-/

@[expose] public section

/--
info: 'Silmaril.Wasm.Auto2.VCLib2.maxSelect_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCLib2.maxSelect_spec

/--
info: 'Silmaril.Wasm.Auto2.VCLib2.double_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCLib2.double_spec
