module

public import Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSAtoms.Bridge
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSAtoms.ConfigV

/-!
# Round 7, the `NoMemSimd → NoAtoms` bridge (round 7, pass 2, track rm)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms`; see `docs/projects/spectec/README.md`. Definitions (`instrOk`, `AdminsOk`, `StoreOk`, `NoCallRef`) are in
`Round7/MSAtoms/Defs.lean`.

* `noAtoms_ms_configVD_iff`: `VInv.NoAtoms msAtoms (configVD hn c) ↔ NoMemSimd c`, at every
  configuration; `noAtoms_ms_configV_iff` the same at `configV` (whose memory SIMD images keep
  the same atoms through `schemaInstrV`).
* `noAtoms_h_configVD_iff`: `VInv.NoAtoms HStep.hAtoms (configVD hn c) ↔ NoCallRef c`;
  `noAtoms_h_configV_iff` the same at `configV` off memory SIMD code.
* `easy_iff`: `RMRed.Easy hn P host c ↔ NoMemSimd c ∧ (∀ c₁, Step P host c c₁ → NoMemSimd c₁) ∧
  NoCallRef c`.
* `na_configV`: the general form, for every atom list `A ⊆ hAtoms`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms.noAtoms_ms_configVD_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms noAtoms_ms_configVD_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms.noAtoms_h_configVD_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms noAtoms_h_configVD_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms.easy_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms easy_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms.noAtoms_ms_configV_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms noAtoms_ms_configV_iff

end Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms
