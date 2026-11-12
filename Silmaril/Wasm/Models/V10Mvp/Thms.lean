module

public import Silmaril.Proofs.Wasm.Models.V10Mvp.Module
public import Silmaril.Proofs.Wasm.Models.V10Mvp.Emb

/-!
# Valid Wasm 1.0 modules land in `core‖v10`

The module-level counterpart of `Lime1Mvp.v10_expr_inFeat` and `Lime1Mvp.v10_storeIn`, which
round 2 left open because `constExprB v10` needs single-instruction initialisers and
1.0 validation gives them only through typing (`ConstExprType`).

* **`constExprType_single`**: a valid 1.0 constant expression is a single constant instruction.
  Every `ConstantInstr` pushes exactly one value, and the expression has type `[] → [t]`;
* **`v10_inFeatM`**: the Core image of a valid 1.0 module is `InFeatM v10`, a module of the MVP
  profile up to the canonical MVP initialisers (`mvpNorm`);
* `validInM_v10`: it is a valid module of `core‖v10` (`ValidInM v10`), with Core validity from
  the copied `V1.Validation.ModuleValid.toCore`;
* `validIn_v20_of_v10`: so it is `ValidIn v20` (and of every profile with reference types above
  `v10`), with the initialisers kept;
* `storeIn_v10_v2`, `ptCore_dom_v10`: the Core store `v10own` runs (through Lime1 and 2.0) is
  `Rt.StoreIn v10`, so the Core point of a `v10own` point lies in the domain of `core|v10`;
* **`v10EmbM H : (v10own H).Emb (coreModelM Profile.spec H v10)`**, direction `sub`: modules,
  points and calls all land in the MVP profile. Its observations are `V10.v10_core_obs` (the
  copied 1.0 → Lime1 → 2.0 simulation, then 2.0 → Core); `v10TransM`, `v10TransMExist` are its
  atlas transitions, and `v10EmbM_v20` checks that, followed by `mToCore` into `core|v20`, it has
  the module map of the 2.0 route (`V1.Module.toV2_toCore`).

The obstruction to `InFeat v10` (without the amendment) is the one of Lime1:
`Lime1Mvp.table_obstruction`, since `V1.Module.toCore = Lime1.Module.toCore ∘ toLime`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V10Mvp

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.Lime1Mvp

/-- **A valid 1.0 constant expression is a single constant instruction.** -/
theorem constExprType_single {C : Silmaril.Wasm.V1.Validation.Context}
    {body : Silmaril.Wasm.V1.Expr} {t : Silmaril.Wasm.V1.ValType}
    (h : Silmaril.Wasm.V1.Validation.ConstExprType C body t) :
    ∃ i, body = [i] ∧ Silmaril.Wasm.V1.Validation.ConstantInstr C i :=
  Silmaril.Proofs.Wasm.Models.V10Mvp.constExprType_single h

/-- The Core image of a valid 1.0 constant expression is a constant expression of `v10`. -/
theorem constExprB_v10 {C : Silmaril.Wasm.V1.Validation.Context}
    {body : Silmaril.Wasm.V1.Expr} {t : Silmaril.Wasm.V1.ValType}
    (h : Silmaril.Wasm.V1.Validation.ConstExprType C body t) :
    constExprB v10 (Silmaril.Wasm.V1.Expr.toCore body) = true :=
  Silmaril.Proofs.Wasm.Models.V10Mvp.constExprB_v10 h

/-- **The Core image of a valid 1.0 module is a module of `v10` up to the canonical MVP
initialisers.** -/
theorem v10_inFeatM {m : Silmaril.Wasm.V1.Module}
    (hv : Silmaril.Wasm.V1.Validation.ModuleValid m) :
    InFeatM v10 (Silmaril.Wasm.V1.Module.toCore m) :=
  Silmaril.Proofs.Wasm.Models.V10Mvp.v10_inFeatM hv

/-- **The Core image of a valid 1.0 module is a valid module of `core‖v10`.** -/
theorem validInM_v10 {m : Silmaril.Wasm.V1.Module}
    (hv : Silmaril.Wasm.V1.Validation.ModuleValid m) :
    ValidInM v10 (Silmaril.Wasm.V1.Module.toCore m) :=
  ⟨Silmaril.Wasm.V1.Validation.ModuleValid.toCore hv, v10_inFeatM hv⟩

theorem v20_refTypes : v20.has .refTypes = true := by decide

/-- The Core image of a valid 1.0 module is a valid module of `v20`, initialisers included. -/
theorem validIn_v20_of_v10 {m : Silmaril.Wasm.V1.Module}
    (hv : Silmaril.Wasm.V1.Validation.ModuleValid m) :
    ValidIn v20 (Silmaril.Wasm.V1.Module.toCore m) :=
  validIn_of_validInM v10_le_v20 v20_refTypes (validInM_v10 hv)

/-- The Core store of a `v10own` point is in `v10`. -/
theorem storeIn_v10_v2 {H : Type} (s : Silmaril.Wasm.V1.Execution.Store H)
    {X : Silmaril.Wasm.Execution.Core.Store H}
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore
        (Silmaril.Wasm.Execution.Runtime.Store.toV2 (s.mapCode Silmaril.Wasm.V1.Func.toLime)) =
      some X) :
    Rt.StoreIn v10 X :=
  Silmaril.Proofs.Wasm.Models.V10Mvp.storeIn_v10_v2 s hX

/-- The Core point of a `v10own` point lies in the domain of `core|v10`. -/
theorem ptCore_dom_v10 {H : Type} {p : Silmaril.Wasm.Models.V10.Pt H}
    (hp : Silmaril.Wasm.Models.V10.dom p) :
    coreDom v10 (Silmaril.Wasm.Models.V2Core.ptCore (Silmaril.Wasm.Models.V10.ptV2 p)) :=
  Silmaril.Proofs.Wasm.Models.V10Mvp.ptCore_dom_v10 hp

/-- **The embedding `v10own → core‖v10`** (direction `sub`): modules, points and calls all land
in the MVP profile `v10`. -/
def v10EmbM (H : Type) :
    (Silmaril.Wasm.Models.V10.v10own H).Emb (coreModelM Silmaril.Wasm.Numerics.Profile.spec H v10)
    where
  mod := Silmaril.Wasm.V1.Module.toCore
  valid _ hm := validInM_v10 hm.1
  pt p := Silmaril.Wasm.Models.V2Core.ptCore (Silmaril.Wasm.Models.V10.ptV2 p)
  call c := Silmaril.Wasm.Models.V2Core.callCore (Silmaril.Wasm.Models.V10.callV2 c)
  readback := some
  dom _ hp := ptCore_dom_v10 hp
  dir := .sub
  sat _ hp c := fun b hb => ⟨b, Silmaril.Wasm.Models.V10.v10_core_obs hp c hb, rfl⟩

theorem v10EmbM_dir (H : Type) : (v10EmbM H).dir = .sub := rfl

/-- The atlas transition of `v10EmbM`: universal sentences of `core‖v10` are reflected. -/
def v10TransM (H : Type) :
    Silmaril.Wasm.Atlas.Transition (Silmaril.Wasm.Models.V10.v10own H).chart
      ((coreModelM Silmaril.Wasm.Numerics.Profile.spec H v10).viewChart some) :=
  (v10EmbM H).toTransition

/-- Existential sentences of `v10own` are preserved into `core‖v10`. -/
def v10TransMExist (H : Type) :
    Silmaril.Wasm.Atlas.Transition (Silmaril.Wasm.Models.V10.v10own H).chart
      ((coreModelM Silmaril.Wasm.Numerics.Profile.spec H v10).viewChart some) :=
  (v10EmbM H).toTransitionExist (by simp [v10EmbM_dir])

/-- Followed by `core‖v10 → core|v20`, the module map of `v10EmbM` is the 2.0 route's:
`V1.Module.toCore m` is the Core image of the 2.0 image of `m`. -/
theorem v10EmbM_v20 (H : Type) (m : Silmaril.Wasm.V1.Module) :
    some ((mToCore Silmaril.Wasm.Numerics.Profile.spec H v10_le_v20 v20_refTypes).mod
        ((v10EmbM H).mod m)) = Silmaril.Wasm.V2.Module.toCore m.toV2 :=
  (Silmaril.Wasm.V1.Module.toV2_toCore m).symm

/-- info: 'Silmaril.Wasm.Models.V10Mvp.v10EmbM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms v10EmbM

/-- info: 'Silmaril.Wasm.Models.V10Mvp.validInM_v10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validInM_v10

end Silmaril.Wasm.Models.V10Mvp
