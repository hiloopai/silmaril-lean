module

public import Silmaril.Proofs.Wasm.Models.Lime1Mvp.Lime1
import Silmaril.Proofs.Wasm.Models.Lime1Mvp.V10

/-!
# `lime1own → core‖lime1`: Lime1 lands in the `lime1` profile at the module level

The header of the amended restriction `core‖S` (`Defs`). Track H showed that the Core
image of a Lime1 module with a table is never `InFeat lime1`
(`Lime1Core.not_inFeat_lime1_of_table`), so `lime1Emb` had to target `core|v30`. Here:

* `inFeatM_of_inFeat`, `inFeat_of_inFeatM` (with `refTypes`), `inFeatM_mono`: `InFeatM S` sits
  between `InFeat S` and `InFeat T` for every `T ≥ S` with reference types;
* **`lime1_inFeatM`**, `validInM_lime1`: the Core image of a valid Lime1 module is a valid
  module of `lime1` up to the canonical MVP initialisers, and `table_obstruction` records that
  for a module with a table this is the strongest restriction that holds;
* `coreToM P H S : core|S → core‖S` and `mToCore P H h hr : core‖S → core|T` (`S ≤ T`, `T` with
  reference types): equality embeddings (identity on modules, points and calls);
* **`lime1EmbM H : (lime1own H).Emb (coreModelM Profile.spec H lime1)`**, direction `sub`;
  `lime1EmbM_factor`: followed by `mToCore` into `core|v30` it has the module, point and call
  maps of track H's `lime1Emb`; `lime1TransM`, `lime1TransMExist`: its atlas transitions.

An earlier step (1.0 code in the `v10` profile):

* **`v10_expr_inFeat`**: the Core image of 1.0 code is in the MVP profile `v10` (no multi-value
  block types, no sign-extension, no saturating conversions), not only in `lime1`;
* **`v10_storeIn`**: every Wasm function of the Core image of the Lime1 image of a 1.0 store
  (the store `v10own` runs) has a body in `v10` (`Rt.StoreIn v10`), the runtime restriction the
  component engine's restricted runs use.

The module-level counterpart (`InFeatM v10` of the image of a valid 1.0 module) is not proved:
`constExprB v10` needs single-instruction initialisers, which 1.0 validation gives only through
typing (`ConstExprType`), and that inversion is not done.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.Lime1Mvp

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Atlas Silmaril.Wasm.Models.Lime1Core
open Silmaril.Wasm.Numerics (Profile)

variable {S T : FeatureSet}

/-- A module of `S` is a module of `S` up to the canonical MVP initialisers. -/
theorem inFeatM_of_inFeat {m : Module} (h : Module.InFeat S m) : InFeatM S m :=
  Silmaril.Proofs.Wasm.Models.Lime1Mvp.inFeatM_of_inFeat h

/-- With reference types, the amendment changes nothing. -/
theorem inFeat_of_inFeatM (hr : S.has .refTypes = true) {m : Module} (h : InFeatM S m) :
    Module.InFeat S m :=
  Silmaril.Proofs.Wasm.Models.Lime1Mvp.inFeat_of_inFeatM hr h

theorem inFeatM_mono (h : S ≤ T) {m : Module} (hs : InFeatM S m) : InFeatM T m :=
  Silmaril.Proofs.Wasm.Models.Lime1Mvp.inFeatM_mono h hs

theorem validInM_of_validIn {m : Module} (h : ValidIn S m) : ValidInM S m :=
  ⟨h.1, inFeatM_of_inFeat h.2⟩

theorem validIn_of_validInM (h : S ≤ T) (hr : T.has .refTypes = true) {m : Module}
    (hs : ValidInM S m) : ValidIn T m :=
  ⟨hs.1, inFeat_of_inFeatM hr (inFeatM_mono h hs.2)⟩

/-- **The Core image of a valid Lime1 module is a module of `lime1` up to the canonical MVP
initialisers.** -/
theorem lime1_inFeatM {m : Silmaril.Wasm.Lime1.Module}
    (hv : Silmaril.Wasm.Lime1.Validation.ModuleValid m) :
    InFeatM lime1 (Silmaril.Wasm.Lime1.Module.toCore m) :=
  Silmaril.Proofs.Wasm.Models.Lime1Mvp.lime1_inFeatM hv

/-- The Core image of a valid Lime1 module is a valid module of `core‖lime1`. -/
theorem validInM_lime1 {m : Silmaril.Wasm.Lime1.Module}
    (hv : Silmaril.Wasm.Lime1.Validation.ModuleValid m) :
    ValidInM lime1 (Silmaril.Wasm.Lime1.Module.toCore m) :=
  ⟨Silmaril.Wasm.Lime1.Validation.ModuleValid.toCore hv, lime1_inFeatM hv⟩

/-- **The obstruction is exactly the MVP initialisers**: a valid Lime1 module with a table has a
Core image that is in `lime1` up to MVP initialisers, but not in `lime1`. -/
theorem table_obstruction {m : Silmaril.Wasm.Lime1.Module}
    (hv : Silmaril.Wasm.Lime1.Validation.ModuleValid m) (ht : m.tables ≠ []) :
    InFeatM lime1 (Silmaril.Wasm.Lime1.Module.toCore m) ∧
      ¬ Module.InFeat lime1 (Silmaril.Wasm.Lime1.Module.toCore m) :=
  ⟨lime1_inFeatM hv, not_inFeat_lime1_of_table ht⟩

/-- `core|S → core‖S`: an equality embedding. -/
def coreToM (P : Profile) (H : Type) (S : FeatureSet) :
    (coreModel P H S).Emb (coreModelM P H S) where
  mod m := m
  valid _ hm := validInM_of_validIn hm
  pt p := p
  call c := c
  readback := some
  dom _ hp := hp
  dir := .eq
  sat p _ c := WasmModel.view_some (coreModel P H S) p c

/-- `core‖S → core|T` for `S ≤ T` with reference types: an equality embedding. -/
def mToCore (P : Profile) (H : Type) (h : S ≤ T) (hr : T.has .refTypes = true) :
    (coreModelM P H S).Emb (coreModel P H T) where
  mod m := m
  valid _ hm := validIn_of_validInM h hr hm
  pt p := p
  call c := c
  readback := some
  dom _ hp := coreDom_mono h hp
  dir := .eq
  sat p _ c := WasmModel.view_some (coreModel P H T) p c

theorem v30_refTypes : v30.has .refTypes = true := by decide

/-- **The embedding `lime1own → core‖lime1`** (direction `sub`): modules, points and calls all
land in the `lime1` profile. -/
def lime1EmbM (H : Type) : (lime1own H).Emb (coreModelM Profile.spec H lime1) where
  mod := Silmaril.Wasm.Lime1.Module.toCore
  valid _ hm := validInM_lime1 hm
  pt := ptCore
  call := callCore
  readback := some
  dom p _ := ptCore_dom_lime1 p
  dir := .sub
  sat _ hp c := fun b hb => ⟨b, obs_sub hp c hb, rfl⟩

theorem lime1EmbM_dir (H : Type) : (lime1EmbM H).dir = .sub := rfl

/-- `lime1EmbM` followed by `core‖lime1 → core|v30` has the maps of track H's `lime1Emb`. -/
theorem lime1EmbM_factor (H : Type) (m : Silmaril.Wasm.Lime1.Module) (p : Pt H) (c : Call) :
    (mToCore Profile.spec H lime1_le_v30 v30_refTypes).mod ((lime1EmbM H).mod m) =
        (lime1Emb H).mod m ∧
      (mToCore Profile.spec H lime1_le_v30 v30_refTypes).pt ((lime1EmbM H).pt p) =
        (lime1Emb H).pt p ∧
      (mToCore Profile.spec H lime1_le_v30 v30_refTypes).call ((lime1EmbM H).call c) =
        (lime1Emb H).call c :=
  ⟨rfl, rfl, rfl⟩

/-- The atlas transition of `lime1EmbM`: universal sentences of `core‖lime1` are reflected. -/
def lime1TransM (H : Type) :
    Transition (lime1own H).chart ((coreModelM Profile.spec H lime1).viewChart some) :=
  (lime1EmbM H).toTransition

/-- Existential sentences of the own model are preserved into `core‖lime1`. -/
def lime1TransMExist (H : Type) :
    Transition (lime1own H).chart ((coreModelM Profile.spec H lime1).viewChart some) :=
  (lime1EmbM H).toTransitionExist (by simp [lime1EmbM_dir])

/-- **The Core image of 1.0 code is in `v10`.** -/
theorem v10_expr_inFeat (e : List Silmaril.Wasm.V1.Instr) :
    Instr.insInFeatB v10 (Silmaril.Wasm.V1.Expr.toCore e) = true :=
  Silmaril.Proofs.Wasm.Models.Lime1Mvp.expr_inFeat_v10 e

/-- **The Core image of the Lime1 image of a 1.0 store runs `v10` code.** -/
theorem v10_storeIn {H : Type} (s : Silmaril.Wasm.V1.Execution.Store H) :
    Rt.StoreIn v10 (s.mapCode Silmaril.Wasm.V1.Func.toLime).toCore :=
  Silmaril.Proofs.Wasm.Models.Lime1Mvp.storeIn_v10 s

/-- info: 'Silmaril.Wasm.Models.Lime1Mvp.v10_storeIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms v10_storeIn

/-- info: 'Silmaril.Wasm.Models.Lime1Mvp.lime1EmbM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lime1EmbM

/-- info: 'Silmaril.Wasm.Models.Lime1Mvp.table_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms table_obstruction

end Silmaril.Wasm.Models.Lime1Mvp
