module

public import Silmaril.Wasm.Models.V10Lime1.Thms
public import Silmaril.Wasm.Models.V10Mvp.Thms

/-!
# `InFeatM v10` routed through Lime1: `v10own → lime1own → core‖v10`

`V10Mvp.v10EmbM` takes `v10own` into the MVP profile `core‖v10` along the 2.0 route (points
through `V10.ptV2`, observations by the copied 1.0 → Lime1 → 2.0 → Core simulations). This topic
takes the same target along the Lime1 route, through `V10Lime1.v10Lime1Emb` and the Lime1 → Core
simulation of `Lime1Core`:

* `limeM_valid`: the Core image of the Lime1 image of a valid 1.0 module is `ValidInM v10`
  (`V1.Module.toLime_toCore`, then `V10Mvp.validInM_v10`); so `InFeatM v10` reaches the modules
  of `v10own` through `v10Lime1Emb`'s module map, not only `InFeatM lime1`;
* `limeM_dom`: the Core point of the gated Lime1 point `ptL p` lies in the domain of `core|v10`
  (the store by `Lime1Mvp.v10_storeIn`, the host from `Lime1Core.ptCore_dom_lime1`, and
  `HostThrowsIn` moves from `lime1` to `v10` since neither has exceptions);
* `limeM_obs`: the observations of `v10own` at `p` are Core observations at that point;
* **`v10LimeM H : (v10own H).Emb (coreModelM Profile.spec H v10)`**, direction `sub`;
* `v10LimeM_factor`: its maps are `v10Lime1Emb` followed by `lime1EmbM`, and its module map is
  `v10EmbM`'s (`v10LimeM_mod`). The points differ: `v10EmbM` goes through 2.0 stores and
  `liftHostL`, `v10LimeM` through Lime1 stores and `liftHostC`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V10LimeM

open Silmaril.Wasm Silmaril.Wasm.Numerics
open Silmaril.Wasm.Models Silmaril.Wasm.Models.Lime1Mvp

variable {H : Type}

/-- **The Lime1 route lands valid 1.0 modules in `core‖v10`.** -/
theorem limeM_valid {m : Silmaril.Wasm.V1.Module}
    (hv : Silmaril.Wasm.V1.Validation.ModuleValid m) :
    ValidInM v10 (Silmaril.Wasm.Lime1.Module.toCore m.toLime) := by
  rw [Silmaril.Wasm.V1.Module.toLime_toCore]
  exact V10Mvp.validInM_v10 hv

/-- In particular `InFeatM v10`, through `v10Lime1Emb`'s module map. -/
theorem limeM_inFeatM {m : Silmaril.Wasm.V1.Module}
    (hv : Silmaril.Wasm.V1.Validation.ModuleValid m) :
    InFeatM v10 (Silmaril.Wasm.Lime1.Module.toCore ((V10Lime1.v10Lime1Emb H).mod m)) :=
  (limeM_valid hv).2

/-- The Core point of the gated Lime1 point lies in the domain of `core|v10`. -/
theorem limeM_dom (p : V10.Pt H) : coreDom v10 (Lime1Core.ptCore (V10Lime1.ptL p)) := by
  obtain ⟨-, hk, ht⟩ := Lime1Core.ptCore_dom_lime1 (V10Lime1.ptL p)
  refine ⟨Lime1Mvp.v10_storeIn p.1, hk, ?_⟩
  intro h s vs s' a hh
  exact absurd (ht h s vs s' a hh) (by decide)

/-- The observations of `v10own` are Core observations at the Lime1-routed point. -/
theorem limeM_obs {p : V10.Pt H} (hp : V10.dom p) (c : V10.Call) :
    V10.obs p c ⊆
      Silmaril.Wasm.Atlas.Core.obs Profile.spec (Lime1Core.ptCore (V10Lime1.ptL p))
        (Lime1Core.callCore c) :=
  fun _ hb => Lime1Core.obs_sub ((V10Lime1.v10Lime1Emb H).dom p hp) c
    (V10Lime1.obs_sub hp c hb)

/-- **`v10own → core‖v10` through Lime1** (direction `sub`). -/
def v10LimeM (H : Type) : (V10.v10own H).Emb (coreModelM Profile.spec H v10) where
  mod m := Silmaril.Wasm.Lime1.Module.toCore m.toLime
  valid _ hm := limeM_valid hm.1
  pt p := Lime1Core.ptCore (V10Lime1.ptL p)
  call := Lime1Core.callCore
  readback := some
  dom p _ := limeM_dom p
  dir := .sub
  sat _ hp c := fun b hb => ⟨b, limeM_obs hp c hb, rfl⟩

theorem v10LimeM_dir (H : Type) : (v10LimeM H).dir = .sub := rfl

/-- `v10LimeM` is `v10Lime1Emb` followed by `lime1EmbM`, on modules, points and calls. -/
theorem v10LimeM_factor (H : Type) (m : Silmaril.Wasm.V1.Module) (p : V10.Pt H)
    (c : V10.Call) :
    (v10LimeM H).mod m = (lime1EmbM H).mod ((V10Lime1.v10Lime1Emb H).mod m) ∧
      (v10LimeM H).pt p = (lime1EmbM H).pt ((V10Lime1.v10Lime1Emb H).pt p) ∧
      (v10LimeM H).call c = (lime1EmbM H).call ((V10Lime1.v10Lime1Emb H).call c) :=
  ⟨rfl, rfl, rfl⟩

/-- Its module map is `v10EmbM`'s: the Lime1 and 2.0 routes agree on modules. -/
theorem v10LimeM_mod (H : Type) (m : Silmaril.Wasm.V1.Module) :
    (v10LimeM H).mod m = (V10Mvp.v10EmbM H).mod m :=
  Silmaril.Wasm.V1.Module.toLime_toCore m

/-- The atlas transition of `v10LimeM`: universal sentences of `core‖v10` are reflected. -/
def v10LimeTransM (H : Type) :
    Silmaril.Wasm.Atlas.Transition (V10.v10own H).chart
      ((coreModelM Profile.spec H v10).viewChart some) :=
  (v10LimeM H).toTransition

end Silmaril.Wasm.Models.V10LimeM

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.Models.V10LimeM.v10LimeM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.V10LimeM.v10LimeM

/-- info: 'Silmaril.Wasm.Models.V10LimeM.limeM_inFeatM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.V10LimeM.limeM_inFeatM
