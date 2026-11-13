module

public import Silmaril.Proofs.Wasm.Models.V10.Behaviours
public import Silmaril.Proofs.Wasm.Models.V10.Valid
public import Silmaril.Wasm.Models.V2Core.Thms

/-!
# `v10own → v20own`: Wasm 1.0 behaviours are Wasm 2.0 behaviours

Over the copied 1.0 → Lime1 → 2.0 simulation (`Silmaril.Wasm.Versions.Thms`):

* `v10_v20_beh`: the behaviours of invoking a 1.0 function, read in 2.0 values, are 2.0
  behaviours of the image point with the induced host, at `v2Profile = Profile.spec`;
* **`v10Emb H : (v10own H).Emb (v20own v2Profile H)`**, direction `sub`, with the atlas
  transition `v10Trans`; composed with `V2Core.v20Emb`, 1.0 behaviours are Core 3.0 behaviours
  (`v10_core_obs`);
* `v10_v20_valid`: a valid 1.0 module whose segment offsets read imported globals is a valid
  2.0 module (silmaril's `ModuleValid.toV2`);
* `v10_v20_valid_false` (refutation): without that side condition validity is **not**
  preserved: a 1.0 data segment may offset by a defined immutable global, 2.0 may not;
* `v10_v20_valid_reflect_false` (refutation): validity is not reflected either: a 1.0 type
  with two results is invalid in 1.0 (no multi-value) but its 2.0 image is valid.

New statements over the copied proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V10

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime Silmaril.Wasm.Models Silmaril.Wasm.Atlas
open Silmaril.Wasm.Lime1.Execution (v2Profile)

variable {H : Type}

/-- **1.0 behaviours are 2.0 behaviours** (at `Profile.spec`). -/
theorem v10_v20_beh {p : Pt H} (hp : dom p) (a : FuncAddr) (vs : List Value) :
    Behaviour.mapSet Value.toV2 (Silmaril.Wasm.V1.Execution.behaviours p.2 p.1 a vs) ⊆
      Silmaril.Wasm.V2.Execution.behaviours v2Profile (ptV2 p).2 (ptV2 p).1 a.value
        (vs.map Value.toV2) :=
  Silmaril.Proofs.Wasm.Models.V10.behaviours_sub hp.1
    (Silmaril.Proofs.Wasm.Models.V10.compatL hp.2.1 hp.2.2.1 hp.2.2.2.1) a vs

/-- Valid 1.0 modules (with imported-only segment offsets) are valid 2.0 modules with a Core
image. -/
theorem v10_v20_valid {m : Silmaril.Wasm.V1.Module} (h : (v10own H).Valid m) :
    (V2Core.v20own v2Profile H).Valid m.toV2 :=
  ⟨Silmaril.Wasm.V1.Validation.ModuleValid.toV2 h.1 h.2, by
    simp [Silmaril.Wasm.V1.Module.toV2_toCore]⟩

/-- The observations of the own 1.0 model are observations of `v20own` at the image. -/
theorem obs_sub {p : Pt H} (hp : dom p) (c : Call) :
    obs p c ⊆ V2Core.obs v2Profile (ptV2 p) (callV2 c) := by
  rintro _ ⟨ha, b, hb, rfl⟩
  have hlen : c.1.value < (ptV2 p).1.funcs.length := by
    simpa [ptV2, limeStore, Silmaril.Wasm.Execution.Runtime.Store.toV2, Store.mapCode] using ha
  refine ⟨hlen, Behaviour.map Value.toV2 b, v10_v20_beh hp c.1 c.2 ⟨b, hb, rfl⟩, ?_⟩
  rw [Behaviour.map_map]
  rfl

/-- **The embedding `v10own → v20own`** (direction `sub`). -/
def v10Emb (H : Type) : (v10own H).Emb (V2Core.v20own v2Profile H) where
  mod := Silmaril.Wasm.V1.Module.toV2
  valid _ h := v10_v20_valid h
  pt := ptV2
  call := callV2
  readback := some
  dom _ hp := Silmaril.Proofs.Wasm.Models.V10.ptV2_dom hp
  dir := .sub
  sat _ hp c := fun b hb => ⟨b, obs_sub hp c hb, rfl⟩

theorem v10Emb_dir (H : Type) : (v10Emb H).dir = .sub := rfl

/-- The atlas transition of `v10Emb`. -/
def v10Trans (H : Type) :
    Transition (v10own H).chart ((V2Core.v20own v2Profile H).viewChart some) :=
  (v10Emb H).toTransition

/-- **1.0 behaviours are Core 3.0 behaviours**, through 2.0: the composite of `v10Emb` and
`V2Core.v20Emb`. -/
theorem v10_core_obs {p : Pt H} (hp : dom p) (c : Call) :
    obs p c ⊆ Silmaril.Wasm.Atlas.Core.obs v2Profile (V2Core.ptCore (ptV2 p))
      (V2Core.callCore (callV2 c)) :=
  (obs_sub hp c).trans
    (V2Core.obs_sub v2Profile (Silmaril.Proofs.Wasm.Models.V10.ptV2_dom hp) (callV2 c))

/-- **Validity is not preserved from 1.0 to 2.0 in general.** -/
theorem v10_v20_valid_false :
    ¬ ∀ m : Silmaril.Wasm.V1.Module, Silmaril.Wasm.V1.Validation.ModuleValid m →
      Silmaril.Wasm.V2.Validation.ModuleValid m.toV2 := fun h =>
  Silmaril.Proofs.Wasm.Models.V10.definedGlobalOffset_toV2_invalid
    (h _ Silmaril.Proofs.Wasm.Models.V10.definedGlobalOffset_valid)

/-- **Validity is not reflected from 2.0 to 1.0** (the `←` half of `v10_v20_valid` in §1.4):
1.0 has no multi-value. -/
theorem v10_v20_valid_reflect_false :
    ¬ ∀ m : Silmaril.Wasm.V1.Module, Silmaril.Wasm.V2.Validation.ModuleValid m.toV2 →
      Silmaril.Wasm.V1.Validation.ModuleValid m := fun h =>
  Silmaril.Proofs.Wasm.Models.V10.twoResults_invalid
    (h _ Silmaril.Proofs.Wasm.Models.V10.twoResults_toV2_valid)

end Silmaril.Wasm.Models.V10
