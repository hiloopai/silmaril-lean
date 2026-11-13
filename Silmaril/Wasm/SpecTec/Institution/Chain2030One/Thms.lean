module

public import Silmaril.Wasm.SpecTec.Institution.Chain2030One.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Chain2030Witness
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Chain2030One

/-!
# The chain wasm-2.0 → wasm-3.0, strengthened: results

Namespace `Silmaril.Wasm.SpecTec.Institution.Chain2030`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.{Chain2030Witness,Chain2030One}`; see
`docs/projects/spectec/README.md`, "chain".

* `pairDom_nop`, `pairDom_nop1`: concrete points 's `PairDom` (`nop nop`, `nop`,
  host-free, every profile).
* `progress_not_bwd`, `progress_not_equal`, `chain_progress_strict`: no transition with the
  chain's point map at `nopPair` that fixes `progress` and has it in its class reflects it, so
  the chain cannot be upgraded to `equal` on progress.
* `v2ToCore1`, `v2ToModel1`, `sat_iff_v2_model1`: on the one-step sub-fragment `PairDom1`, V2
  and the wasm-3.0 model are equal on sentences respecting `SimV` and `CfgRel`.
* `chainExist1`, `exist_chain1`; `chainUniv1`, `univ_chain1`: the wasm-2.0 model to the wasm-3.0
  model on `PairDom1`, existential sentences forwards and universal sentences backwards,
  value-sensitive ones included.
* `pairDom1_nop1`, `nop1_codeNil`: `nop` is in `PairDom1`, and the value-sensitive sentences
  `may () CodeNil` and `always () CodeNil` are transported there.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Chain2030.pairDom_nop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Chain2030.pairDom_nop

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Chain2030.pairDom1_nop1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Chain2030.pairDom1_nop1

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Chain2030.progress_not_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Chain2030.progress_not_equal

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Chain2030.sat_iff_v2_model1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Chain2030.sat_iff_v2_model1

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Chain2030.exist_chain1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Chain2030.exist_chain1

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Chain2030.univ_chain1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Chain2030.univ_chain1

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Chain2030.nop1_codeNil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Chain2030.nop1_codeNil
