module

public import Silmaril.Proofs.Wasm.Models.Lime1Core.Behaviours
public import Silmaril.Proofs.Wasm.Models.Lime1Core.Module

/-!
# `lime1own → core|v30`: Lime1 behaviours are Core 3.0 behaviours

The header of the Lime1 → Core 3.0 embedding (track H of
[wasm-models.md](../../../../docs/projects/spectec/README.md), §6). The execution simulation is the copied
`Silmaril.Wasm.Lime1.Execution.{Step,Steps,Diverges}.toCore` and `Sim.result`
(`Silmaril/Raw/Wasm/Versions/Lime1/ToCore/*`, an earlier development; provenance in

* `lime1_core_beh`: the behaviours of invoking an allocated address of a well-formed Lime1 point,
  read in Core values, are Core behaviours of the image point;
* `storeIn_image`: the image store is in `lime1` (`Rt.StoreIn lime1`), so the runtime part of
  the image never leaves `lime1`;
* `validIn_v30`: the Core image of a valid Lime1 module is `ValidIn v30`;
* **`lime1Emb H : (lime1own H).Emb (coreModel Profile.spec H v30)`**, direction `sub`, with the
  atlas transitions `lime1Trans` (universal sentences reflected) and `lime1TransExist`
  (existential sentences preserved), and the composite `lime1EmbLime1Dom`: the image point lies
  in the domain of `core|lime1`;
* `not_inFeat_lime1_of_table`, `not_inFeat_lime1_of_elem` (refutations of `ValidIn lime1` of the
  image): Core spells the MVP table initialiser and function-index elements with `ref.null` and
  `ref.func`, which the restricted syntax files under `refTypes`. So the target is `core|v30`
  at the module level, while points land in `core|lime1`.

New statements over the copied proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.Lime1Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime Silmaril.Wasm.Models Silmaril.Wasm.Atlas
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Models.V10 (LStore LHost HostKeepsL)

variable {H : Type}

theorem liftHostC_compatible {src : LHost H}
    (hp : Silmaril.Wasm.Lime1.Execution.HostPreserves src) (hk : HostKeepsL src) :
    Silmaril.Wasm.Lime1.Execution.HostCompatible src (liftHostC src) :=
  Silmaril.Proofs.Wasm.Models.Lime1Core.compat hp hk

/-- **Lime1 behaviours are Core 3.0 behaviours** (at `Profile.spec`). -/
theorem lime1_core_beh {s : LStore H} {src : LHost H}
    (hwf : Silmaril.Wasm.Lime1.Execution.StoreWF s)
    (hp : Silmaril.Wasm.Lime1.Execution.HostPreserves src) (hk : HostKeepsL src) {a : FuncAddr}
    (ha : a.value < s.funcs.length) (vs : List Value) :
    Behaviour.mapSet Value.toCore (behavioursL src s a vs) ⊆
      Silmaril.Wasm.Execution.Core.behaviours Profile.spec (liftHostC src) s.toCore a.value
        (vs.map Value.toCore) :=
  Silmaril.Proofs.Wasm.Models.Lime1Core.behaviours_sub hwf (liftHostC_compatible hp hk) ha vs

/-- The Core image of a Lime1 store is in `lime1`. -/
theorem storeIn_image (s : LStore H) : Rt.StoreIn lime1 s.toCore :=
  Silmaril.Proofs.Wasm.Models.Lime1Core.storeIn_image s

/-- The Core image of a valid Lime1 module is a valid module of `v30`. -/
theorem validIn_v30 {m : Silmaril.Wasm.Lime1.Module}
    (h : Silmaril.Wasm.Lime1.Validation.ModuleValid m) :
    ValidIn v30 (Silmaril.Wasm.Lime1.Module.toCore m) :=
  Silmaril.Proofs.Wasm.Models.Lime1Core.validIn_v30 h

/-- **The Core image of a Lime1 module with a table is not a module of `lime1`.** -/
theorem not_inFeat_lime1_of_table {m : Silmaril.Wasm.Lime1.Module} (h : m.tables ≠ []) :
    ¬ Module.InFeat lime1 (Silmaril.Wasm.Lime1.Module.toCore m) :=
  Silmaril.Proofs.Wasm.Models.Lime1Core.not_inFeat_lime1_of_table h

/-- **The Core image of a Lime1 module with a nonempty element segment is not a module of
`lime1`.** -/
theorem not_inFeat_lime1_of_elem {m : Silmaril.Wasm.Lime1.Module}
    {e : Silmaril.Wasm.Lime1.Elem} (he : e ∈ m.elems) (hi : e.init ≠ []) :
    ¬ Module.InFeat lime1 (Silmaril.Wasm.Lime1.Module.toCore m) :=
  Silmaril.Proofs.Wasm.Models.Lime1Core.not_inFeat_lime1_of_elem he hi

/-- The image point lies in the domain of `core|lime1`. -/
theorem ptCore_dom_lime1 (p : Pt H) : coreDom lime1 (ptCore p) :=
  ⟨storeIn_image p.1, Silmaril.Proofs.Wasm.Models.Lime1Core.keeps p.2,
    Silmaril.Proofs.Wasm.Models.Lime1Core.throwsIn lime1 p.2⟩

/-- The image point lies in the domain of `core|v30`. -/
theorem ptCore_dom (p : Pt H) : coreDom v30 (ptCore p) :=
  coreDom_mono lime1_le_v30 (ptCore_dom_lime1 p)

/-- The observations of the own model are Core observations. -/
theorem obs_sub {p : Pt H} (hp : dom p) (c : Call) :
    obs p c ⊆ Silmaril.Wasm.Atlas.Core.obs Profile.spec (ptCore p) (callCore c) := by
  rintro b ⟨ha, hb⟩
  exact lime1_core_beh hp.1 hp.2.1 hp.2.2 ha c.2 hb

/-- **The embedding `lime1own → core|v30`** (direction `sub`). -/
def lime1Emb (H : Type) : (lime1own H).Emb (coreModel Profile.spec H v30) where
  mod := Silmaril.Wasm.Lime1.Module.toCore
  valid _ hm := validIn_v30 hm
  pt := ptCore
  call := callCore
  readback := some
  dom p _ := ptCore_dom p
  dir := .sub
  sat _ hp c := fun b hb => ⟨b, obs_sub hp c hb, rfl⟩

theorem lime1Emb_dir (H : Type) : (lime1Emb H).dir = .sub := rfl

/-- The atlas transition of `lime1Emb`: universal sentences of `core|v30` are reflected. -/
def lime1Trans (H : Type) :
    Transition (lime1own H).chart ((coreModel Profile.spec H v30).viewChart some) :=
  (lime1Emb H).toTransition

/-- Existential sentences of the own model are preserved into `core|v30`. -/
def lime1TransExist (H : Type) :
    Transition (lime1own H).chart ((coreModel Profile.spec H v30).viewChart some) :=
  (lime1Emb H).toTransitionExist (by simp [lime1Emb_dir])

end Silmaril.Wasm.Models.Lime1Core
