module

public import Silmaril.Proofs.Wasm.FnInst.Ground.Link

@[expose] public section

/-! # `checkInst` sentences from the grounded rules

Header of `Silmaril.Proofs.Wasm.FnInst.Ground.Link`. When the computed instances of two
modules are related by the rules' source pairs (`InstRel`), the bridges' code simulations
make the `checkInst` sentences hold in **every** model with the relation `Rel.eq`:

* `sat_le_of_good` (frame-free bridge, `gBaseSim`) and `sat_le_of_goodW` (deferred bridge,
  `wDeferredSim`): `m ⊑ m'`;
* `sat_eqv_of_good`, `sat_eqv_of_goodW`: `m ≐ m'`, from rule lemmas in both directions.

These are the same simulations that give `Binaryen.ExportEquiv` under the closed host
(`exportEquiv_of_good`, `exportRefines_of_goodW`); the hosts coincide
(`closedHost_eq_noHost`). What is **open** is deriving `InstRel` from `ModuleBodiesRel`
(the computed instance is `instantiateOnce?`, which allocates each global once, while the
spec instantiation behind `ExportEquiv` allocates them twice), so that `ExportEquiv`'s
hypotheses alone give the sentence.
-/

namespace Silmaril.Wasm.FnInst.Ground.Check

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.FnInst.Ground

variable {m m' : Module} {j : ℕ}

/-- Frame-free rules: `m ⊑ m'` holds in every model with equal behaviours. -/
theorem sat_le_of_good {BI : List Instr → List Instr → Prop} (hBI : ∀ x y, BI x y → GBI x y)
    (hI : InstRel BI m m') (P : Profile) : checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.le m m') :=
  modRefines_of_baseSim gBaseSim (hI.mono hBI) j

/-- Rules of the deferred bridge: `m ⊑ m'` holds in every model with equal behaviours. -/
theorem sat_le_of_goodW {BI : List Instr → List Instr → Prop} (hBI : ∀ x y, BI x y → GWI x y)
    (hI : InstRel BI m m') (P : Profile) : checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.le m m') :=
  modRefines_of_deferred wDeferredSim (hI.mono hBI) j

/-- Frame-free rules in both directions: `m ≐ m'` in every model with equal behaviours. -/
theorem sat_eqv_of_good {BI BI' : List Instr → List Instr → Prop}
    (hBI : ∀ x y, BI x y → GBI x y) (hBI' : ∀ x y, BI' x y → GBI x y)
    (hI : InstRel BI m m') (hI' : InstRel BI' m' m) (P : Profile) :
    checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.eqv m m') :=
  modEquiv_of_refines (sat_le_of_good hBI hI P) (sat_le_of_good hBI' hI' P)

/-- Rules of the deferred bridge in both directions: `m ≐ m'` in every model with equal
behaviours. -/
theorem sat_eqv_of_goodW {BI BI' : List Instr → List Instr → Prop}
    (hBI : ∀ x y, BI x y → GWI x y) (hBI' : ∀ x y, BI' x y → GWI x y)
    (hI : InstRel BI m m') (hI' : InstRel BI' m' m) (P : Profile) :
    checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.eqv m m') :=
  modEquiv_of_refines (sat_le_of_goodW hBI hI P) (sat_le_of_goodW hBI' hI' P)

end Silmaril.Wasm.FnInst.Ground.Check
