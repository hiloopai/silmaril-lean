module

public import Silmaril.Proofs.Wasm.FnInst.Ground.Inst
public import Silmaril.Wasm.FnInst.Ground.Link.Thms

@[expose] public section

/-! # `checkInst` sentences from `ExportEquiv`'s hypotheses

Header of `Silmaril.Proofs.Wasm.FnInst.Ground.Inst`. wasm-check's computed instance
(`instOf`: `instantiateOnce?`, that is `evalGlobals?`, then `prepare?` and `initSegments?` of
the residue) never reads function code, so modules with related bodies have related computed
instances: **`instRel_of_bodiesRel`** turns `ModuleBodiesRel BI m m'` and the validity of
both modules (the hypotheses of `exportRefines_of_bodiesRel`) into `InstRel BI m m'`, the
hypothesis of the `checkInst` link (`Ground.Link`).

With it, the hypotheses behind the grounded `ExportEquiv` theorems alone give the
`checkInst` sentences, in every model with `Rel.eq`:

* `sat_le_of_good_bodies`, `sat_le_of_goodW_bodies` (`m ⊑ m'`) and
  `sat_eqv_of_good_bodies`, `sat_eqv_of_goodW_bodies` (`m ≐ m'`);
* the restated stages: `teeForm_sat`, `rseLine_sat`, and the rule forms
  `neutralC_sat`, `eqz3_sat`, `twoSets_sat`.
-/

namespace Silmaril.Wasm.FnInst.Ground.Check

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.FnInst.Ground Silmaril.Wasm.FnInst.Ground.Inst

variable {m m' : Module} {j : ℕ}

/-- Frame-free rules: `m ⊑ m'` from `ModuleBodiesRel` and validity. -/
theorem sat_le_of_good_bodies {BI : List Instr → List Instr → Prop}
    (hBI : ∀ x y, BI x y → GBI x y) (hrel : ModuleBodiesRel BI m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) (P : Profile) :
    checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.le m m') :=
  sat_le_of_good hBI (instRel_of_bodiesRel hrel hm hm') P

/-- Rules of the deferred bridge: `m ⊑ m'` from `ModuleBodiesRel` and validity. -/
theorem sat_le_of_goodW_bodies {BI : List Instr → List Instr → Prop}
    (hBI : ∀ x y, BI x y → GWI x y) (hrel : ModuleBodiesRel BI m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) (P : Profile) :
    checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.le m m') :=
  sat_le_of_goodW hBI (instRel_of_bodiesRel hrel hm hm') P

/-- Frame-free rules in both directions: `m ≐ m'` from one `ModuleBodiesRel`. -/
theorem sat_eqv_of_good_bodies {BI : List Instr → List Instr → Prop}
    (hBI : ∀ x y, BI x y → GBI x y) (hBI' : ∀ x y, BI y x → GBI x y)
    (hrel : ModuleBodiesRel BI m m') (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt)
    (P : Profile) : checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.eqv m m') :=
  modEquiv_of_refines (sat_le_of_good_bodies hBI hrel hm hm' P)
    (sat_le_of_good_bodies hBI' hrel.flip hm' hm P)

/-- Rules of the deferred bridge in both directions: `m ≐ m'` from one `ModuleBodiesRel`. -/
theorem sat_eqv_of_goodW_bodies {BI : List Instr → List Instr → Prop}
    (hBI : ∀ x y, BI x y → GWI x y) (hBI' : ∀ x y, BI y x → GWI x y)
    (hrel : ModuleBodiesRel BI m m') (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt)
    (P : Profile) : checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.eqv m m') :=
  modEquiv_of_refines (sat_le_of_goodW_bodies hBI hrel hm hm' P)
    (sat_le_of_goodW_bodies hBI' hrel.flip hm' hm P)

/-! ## Restated stages as `checkInst` sentences -/

/-- **`tee-form` as a `checkInst` sentence**: valid in every model with `Rel.eq`. -/
theorem teeForm_sat {m : BModule} (hm : m.Ok) (hm' : (Silmaril.Wasm.Binaryen.TeeForm.teeForm m).Ok)
    (P : Profile) : checkPlain.Sat (S := ⟨j⟩) (P, .eq)
      (.eqv (Silmaril.Wasm.Binaryen.TeeForm.teeForm m).lower m.lower) :=
  sat_eqv_of_goodW_bodies tfBI_goodW tfBI_goodW_rev
    (Silmaril.Wasm.Binaryen.TeeForm.teeForm_bodiesRel m) hm' hm P

/-- **`rse-line` as a `checkInst` sentence**: frame-free forward, deferred backward. -/
theorem rseLine_sat {m : BModule} (hm : m.Ok) (hm' : (RedundantSetLine.rseLine m).Ok)
    (P : Profile) : checkPlain.Sat (S := ⟨j⟩) (P, .eq)
      (.eqv (RedundantSetLine.rseLine m).lower m.lower) :=
  modEquiv_of_refines
    (sat_le_of_good_bodies rsBI_good (Silmaril.Wasm.Binaryen.RseLine.rseLine_bodiesRel m) hm' hm P)
    (sat_le_of_goodW_bodies rsBI_goodW_rev
      (Silmaril.Wasm.Binaryen.RseLine.rseLine_bodiesRel m).flip hm hm' P)

/-- One frame-free rule with a rule lemma in each direction, as a `checkInst` sentence. -/
theorem pair_sat {a b : List GInstr} (h : Good a b) (h' : Good b a)
    (hrel : ModuleBodiesRel (Pair a b) m m') (hm : ∃ mt, ModuleOk m mt)
    (hm' : ∃ mt, ModuleOk m' mt) (P : Profile) :
    checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.eqv m m') := by
  refine sat_eqv_of_good_bodies ?_ ?_ hrel hm hm' P
  · rintro _ _ ⟨rfl, rfl⟩
    exact gbi_of_good h
  · rintro _ _ hp
    obtain ⟨rfl, rfl⟩ := pair_flip hp
    exact gbi_of_good h'

/-- One rule of the deferred bridge with a rule lemma in each direction, as a `checkInst`
sentence. -/
theorem pairW_sat {a b : List GInstr} (h : GoodW a b) (h' : GoodW b a)
    (hrel : ModuleBodiesRel (Pair a b) m m') (hm : ∃ mt, ModuleOk m mt)
    (hm' : ∃ mt, ModuleOk m' mt) (P : Profile) :
    checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.eqv m m') := by
  refine sat_eqv_of_goodW_bodies ?_ ?_ hrel hm hm' P
  · rintro _ _ ⟨rfl, rfl⟩
    exact ⟨a, b, h, rfl, rfl⟩
  · rintro _ _ hp
    obtain ⟨rfl, rfl⟩ := pair_flip hp
    exact ⟨b, a, h', rfl, rfl⟩

/-- `neutral-ops` with a consumer of the fragment, as a `checkInst` sentence. -/
theorem neutralC_sat {b : Bin} {k : BitVec 32} (hk : Neutral b k) {X : GInstr}
    (hX : Consumer X) (hrel : ModuleBodiesRel (Pair [.const k, .bin b, X] [X]) m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) (P : Profile) :
    checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.eqv m m') :=
  pair_sat (good_neutralC hk hX) (good_neutralC_rev hk hX) hrel hm hm' P

/-- `eqz-pair` with consumer `i32.eqz`, as a `checkInst` sentence. -/
theorem eqz3_sat (hrel : ModuleBodiesRel (Pair [.eqz, .eqz, .eqz] [.eqz]) m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) (P : Profile) :
    checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.eqv m m') :=
  pair_sat good_eqz3 good_eqz3_rev hrel hm hm' P

/-- Two stores to one local are one store, as a `checkInst` sentence. -/
theorem twoSets_sat (hrel : ModuleBodiesRel (Pair twoSets oneSet) m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) (P : Profile) :
    checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.eqv m m') :=
  pairW_sat goodW_twoSets goodW_oneSet hrel hm hm' P

end Silmaril.Wasm.FnInst.Ground.Check
