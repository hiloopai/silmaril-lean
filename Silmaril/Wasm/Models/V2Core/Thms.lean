module

public import Silmaril.Proofs.Wasm.Models.V2Core.Behaviours
public import Silmaril.Proofs.Wasm.Models.V2Core.Module
public import Silmaril.Proofs.Wasm.Models.V2Core.Det
public import Silmaril.Proofs.Wasm.Models.V2Core.DetFalse
public import Silmaril.Proofs.Wasm.Models.V2Core.Inst
public import Silmaril.Proofs.Wasm.Models.V2Core.ReflModule

/-!
# `v20own → core|v20`: Wasm 2.0 behaviours are Core 3.0 behaviours

The header of the 2.0 → Core 3.0 port (track E of
[wasm-models.md](../../../../docs/projects/spectec/README.md), §1.4). The execution simulation is the copied
`Silmaril.Wasm.V2.Execution.{Step,Steps,Diverges}.toCore`, `Sim.result` and
`Instantiate.toCore` (`Silmaril/Raw/Wasm/Versions/V2/ToCore/*`, from

* `validIn_image`: the Core image of a valid 2.0 module is a valid module of `v20`
  (`ValidIn v20`: Core-valid and in the feature set);
* `storeIn_image`: the Core image of a 2.0 store is in `v20` (`Rt.StoreIn v20`);
* `liftHost_compatible`: the induced Core host is compatible with the 2.0 host;
* **`v20_core_beh`**: at every profile `P`, the behaviours of invoking an allocated address of a
  well-formed 2.0 point, read in Core values, are Core behaviours of the image point;
* **`v20Emb P H : (v20own P H).Emb (coreModel P H v20)`**, direction `sub`, and the atlas
  transitions `v20Trans` (universal sentences reflected) and `v20TransExist` (existential
  sentences preserved);
* `v20_core_valid_false`: validity is **not** reflected along the embedding, even inside `v20`:
  a module defining two immutable globals, the second initialised by `global.get` of the first,
  is in `v20` and Core-valid but invalid in 2.0 (2.0 constant expressions may only read
  *imported* globals);
* **`v20_core_valid`** (proves `V20CoreValid`): validity *is* reflected for modules
  whose constant `global.get`s read imported globals (`ConstReadsImports`). A Core typing of
  the image of 2.0 code reads back as a 2.0 typing (`Reflect.instrs_refl`, through the read-back
  `Reflect.er` of Core value types, which keeps the reference hierarchy along subtyping), and
  each premise of Core's `Module_ok` reads back as 2.0's (`Reflect.refl_valid`);
* **`v20_core_beh_det_false`** (refutation): the frozen `V20CoreBehDet` (equality at
  `Profile.deterministic g` for every host) is false. A 2.0 null carries its reference type
  and a Core null does not, so the induced host `liftHost src` may answer from a different 2.0
  argument (`DetFalse`);
* **`v20_core_beh_det_of_closed`**: equality at `Profile.deterministic g` when the call's
  closed-host 2.0 run has a behaviour, under any host that preserves well-formedness and keeps
  functions;
* `v20_beh_unalloc`, `core_beh_unalloc`, `obs_unalloc`: at an unallocated address both
  machines are stuck. The 2.0 behaviours and the Core behaviours of the image are empty, so
  the guard `c.1 < len` of `obs` loses nothing;
* **`v20EmbDet g : (v20ownDet g H).Emb (coreModelOk (Profile.deterministic g) H v20)`**,
  direction `eq`, and the equality atlas transition `v20TransDet`. Calls are observed only when
  Core's `$invoke` premises hold on the image (`CallOk`). The domain `domDet` asks that every
  such call's closed-host 2.0 run has a behaviour;
* instantiation as observations: `v20inst P H`, `coreInst P H S`, and
  **`v20InstEmb P H : (v20inst P H).Emb (coreInst P H v20)`** (direction `sub`), from the copied
  `instantiate_sim` under `InstantiationBounds`. A module is observed only when it has no
  defined globals (`noGlobals`; see `Silmaril.Proofs.Wasm.Models.V2Core.Inst`).

New statements over the copied proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2Core

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Atlas
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

theorem validIn_image {m : Silmaril.Wasm.V2.Module} {cm : Silmaril.Wasm.Module}
    (h : Silmaril.Wasm.V2.Validation.ModuleValid m)
    (hc : Silmaril.Wasm.V2.Module.toCore m = some cm) : ValidIn v20 cm :=
  Silmaril.Proofs.Wasm.Models.V2Core.validIn_image h hc

theorem storeIn_image {s : VStore H} {X : CStore H}
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore s = some X) : Rt.StoreIn v20 X :=
  Silmaril.Proofs.Wasm.Models.V2Core.storeIn_image hX

theorem liftHost_compatible {src : VHost H} (hp : Silmaril.Wasm.V2.Execution.HostPreserves src)
    (hk : HostKeepsV src) : Silmaril.Wasm.V2.Execution.HostCompatible src (liftHost src) :=
  Silmaril.Proofs.Wasm.Models.V2Core.compatible hp hk

/-- **2.0 behaviours are Core 3.0 behaviours**, at every profile. -/
theorem v20_core_beh (P : Profile) {s : VStore H} {src : VHost H} {X : CStore H}
    (hwf : Silmaril.Wasm.V2.Execution.StoreWF s)
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore s = some X)
    (hp : Silmaril.Wasm.V2.Execution.HostPreserves src) (hk : HostKeepsV src) {a : Nat}
    (ha : a < s.funcs.length) (vs : List VVal) :
    Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
        (Silmaril.Wasm.V2.Execution.behaviours P src s a vs) ⊆
      Silmaril.Wasm.Execution.Core.behaviours P (liftHost src) X a
        (vs.map Silmaril.Wasm.V2.Execution.Val.toCore) :=
  Silmaril.Proofs.Wasm.Models.V2Core.behaviours_sub P hwf hX hp hk ha vs

theorem ptCore_eq {p : Pt H} {X : CStore H}
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore p.1 = some X) :
    ptCore p = (X, liftHost p.2) := by
  simp [ptCore, hX]

/-- The point map lands in the domain of `core|v20`. -/
theorem ptCore_dom {p : Pt H} (hp : dom p) : coreDom v20 (ptCore p) := by
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp hp.2.1
  rw [ptCore_eq hX]
  exact ⟨storeIn_image hX, Silmaril.Proofs.Wasm.Models.V2Core.keeps p.2,
    Silmaril.Proofs.Wasm.Models.V2Core.throwsIn v20 p.2⟩

/-- The observations of the own model are observations of `core|v20`. -/
theorem obs_sub (P : Profile) {p : Pt H} (hp : dom p) (c : Call) :
    obs P p c ⊆ Silmaril.Wasm.Atlas.Core.obs P (ptCore p) (callCore c) := by
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp hp.2.1
  rintro b ⟨ha, hb⟩
  rw [ptCore_eq hX]
  exact v20_core_beh P hp.1 hX hp.2.2.1 hp.2.2.2 ha c.2 hb

/-- **The embedding `v20own → core|v20`** (direction `sub`). -/
def v20Emb (P : Profile) (H : Type) : (v20own P H).Emb (coreModel P H v20) where
  mod := modCore
  valid m hm := by
    obtain ⟨cm, hcm⟩ := Option.isSome_iff_exists.mp hm.2
    have e : modCore m = cm := by simp [modCore, hcm]
    exact e ▸ validIn_image hm.1 hcm
  pt := ptCore
  call := callCore
  readback := some
  dom _ hp := ptCore_dom hp
  dir := .sub
  sat p hp c := fun b hb => ⟨b, obs_sub P hp c hb, rfl⟩

theorem v20Emb_dir (P : Profile) (H : Type) : (v20Emb P H).dir = .sub := rfl

/-- The atlas transition of `v20Emb`: universal sentences of `core|v20` are reflected. -/
def v20Trans (P : Profile) (H : Type) :
    Transition (v20own P H).chart ((coreModel P H v20).viewChart some) :=
  (v20Emb P H).toTransition

/-- Existential sentences of the own model are preserved into `core|v20`. -/
def v20TransExist (P : Profile) (H : Type) :
    Transition (v20own P H).chart ((coreModel P H v20).viewChart some) :=
  (v20Emb P H).toTransitionExist (by simp [v20Emb_dir])

/-! ## Validity is not reflected -/

/-- **Validity is not reflected along the embedding, even inside `v20`.** -/
theorem v20_core_valid_false :
    ¬ ∀ (m : Silmaril.Wasm.V2.Module) (cm : Silmaril.Wasm.Module),
      Silmaril.Wasm.V2.Module.toCore m = some cm → ValidIn v20 cm →
        Silmaril.Wasm.V2.Validation.ModuleValid m := by
  intro h
  have hin : Module.InFeat v20 Silmaril.Wasm.V2.Validation.Converse.coreSharedGlobal := by
    decide
  exact Silmaril.Wasm.V2.Validation.Converse.sharedGlobalModule_invalid
    (h _ _ Silmaril.Wasm.V2.Validation.Converse.toCore_sharedGlobalModule
      ⟨Silmaril.Wasm.V2.Validation.Converse.coreSharedGlobal_valid, hin⟩)

/-- 2.0 constant `global.get`s read imported globals: every `global.get x` in a global
initialiser or element or data offset of `m` has `x` below the number of imported globals. -/
def ConstReadsImports (m : Silmaril.Wasm.V2.Module) : Prop :=
  ∀ e ∈ m.globals.map (·.init) ++ m.elems.flatMap (·.init) ++
      m.elems.filterMap (fun e => match e.mode with | .active _ off => some off | _ => none) ++
      m.data.filterMap (fun d => match d.mode with | .active _ off => some off | _ => none),
    ∀ x, .globalGet x ∈ e →
      x.toNat < (m.imports.filter fun i => match i.desc with | .global _ => true | _ => false).length

/-- **Target, proved** (`v20_core_valid`): validity is reflected for modules whose constant
`global.get`s read imported globals (the conservative-extension half of §1.4). -/
def V20CoreValid : Prop :=
  ∀ (m : Silmaril.Wasm.V2.Module) (cm : Silmaril.Wasm.Module),
    Silmaril.Wasm.V2.Module.toCore m = some cm → ValidIn v20 cm → ConstReadsImports m →
      Silmaril.Wasm.V2.Validation.ModuleValid m

/-- **Validity is reflected along the embedding** for modules whose constant `global.get`s read
imported globals: the Core image of such a 2.0 module is a valid module of `v20` only if the 2.0
module is valid. -/
theorem v20_core_valid : V20CoreValid :=
  fun _ _ hc hv hcr => Silmaril.Proofs.Wasm.Models.V2Core.Reflect.refl_valid hc hv hcr

/-- The two directions together: on modules whose constant `global.get`s read imported globals,
a 2.0 module with a Core image is valid iff its image is a valid module of `v20`. -/
theorem v20_core_valid_iff {m : Silmaril.Wasm.V2.Module} {cm : Silmaril.Wasm.Module}
    (hc : Silmaril.Wasm.V2.Module.toCore m = some cm) (hcr : ConstReadsImports m) :
    Silmaril.Wasm.V2.Validation.ModuleValid m ↔ ValidIn v20 cm :=
  ⟨fun h => validIn_image h hc, fun h => v20_core_valid m cm hc h hcr⟩

/-- The design's target that, at the deterministic profile, the inclusion `v20_core_beh` is an
equality. It is **false** (`v20_core_beh_det_false`); `v20_core_beh_det_of_closed` is the
corrected statement. -/
def V20CoreBehDet : Prop :=
  ∀ (g : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool) (H : Type) (s : VStore H) (src : VHost H) (X : CStore H),
    Silmaril.Wasm.V2.Execution.StoreWF s →
    Silmaril.Wasm.V2.Execution.Store.toCore s = some X →
    Silmaril.Wasm.V2.Execution.HostPreserves src → HostKeepsV src →
    ∀ a, a < s.funcs.length → ∀ vs : List VVal,
      Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
          (Silmaril.Wasm.V2.Execution.behaviours (Profile.deterministic g) src s a vs) =
        Silmaril.Wasm.Execution.Core.behaviours (Profile.deterministic g) (liftHost src) X a
          (vs.map Silmaril.Wasm.V2.Execution.Val.toCore)

/-! ## Equality at the deterministic profile -/

/-- **The frozen equality target is false.** -/
theorem v20_core_beh_det_false : ¬ V20CoreBehDet := by
  intro hT
  obtain ⟨X, hX⟩ := Silmaril.Proofs.Wasm.Models.V2Core.DetFalse.st_toCore
  exact Silmaril.Proofs.Wasm.Models.V2Core.DetFalse.det_eq_false (fun _ _ _ _ => false) hX
    (hT (fun _ _ _ _ => false) Unit _ _ X Silmaril.Proofs.Wasm.Models.V2Core.DetFalse.st_wf hX
      Silmaril.Proofs.Wasm.Models.V2Core.DetFalse.src_preserves
      Silmaril.Proofs.Wasm.Models.V2Core.DetFalse.src_keeps 0 (by decide) _)

/-- **2.0 and Core behaviours are equal at the deterministic profile** when the closed-host
2.0 run of the call has a behaviour. -/
theorem v20_core_beh_det_of_closed (g : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool)
    {s : VStore H} {src : VHost H} {X : CStore H}
    (hwf : Silmaril.Wasm.V2.Execution.StoreWF s)
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore s = some X)
    (hp : Silmaril.Wasm.V2.Execution.HostPreserves src) (hk : HostKeepsV src) {a : Nat}
    (ha : a < s.funcs.length) (vs : List VVal)
    (htot : (Silmaril.Wasm.V2.Execution.behaviours (Profile.deterministic g) closedV s a
      vs).Nonempty) :
    Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
        (Silmaril.Wasm.V2.Execution.behaviours (Profile.deterministic g) src s a vs) =
      Silmaril.Wasm.Execution.Core.behaviours (Profile.deterministic g) (liftHost src) X a
        (vs.map Silmaril.Wasm.V2.Execution.Val.toCore) :=
  Silmaril.Proofs.Wasm.Models.V2Core.behaviours_det_eq g hwf hX hp hk ha vs htot

/-! ## Unallocated addresses -/

/-- **2.0 behaviours at an unallocated address are empty.** -/
theorem v20_beh_unalloc (P : Profile) (src : VHost H) (s : VStore H) {a : Nat}
    (ha : s.funcs.length ≤ a) (vs : List VVal) :
    Silmaril.Wasm.V2.Execution.behaviours P src s a vs = ∅ :=
  Silmaril.Proofs.Wasm.Models.V2Core.behaviours_unalloc P src s ha vs

/-- **Core behaviours at an unallocated address are empty.** -/
theorem core_beh_unalloc (P : Profile) (host : CHost H) (X : CStore H) {a : Nat}
    (ha : X.funcs.length ≤ a) (vs : List CVal) :
    Silmaril.Wasm.Execution.Core.behaviours P host X a vs = ∅ :=
  Silmaril.Proofs.Wasm.Models.V2Core.core_behaviours_unalloc P host X ha vs

/-- The image store has as many functions as the 2.0 store. -/
theorem funcs_length_image {s : VStore H} {X : CStore H}
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore s = some X) :
    X.funcs.length = s.funcs.length := by
  obtain ⟨fs, hfs, rfl⟩ := Silmaril.Proofs.Wasm.Models.V2Core.toCore_eq_some.mp hX
  exact Silmaril.Wasm.V2.Execution.mapM_length hfs

/-- **Unallocated calls are observed as nothing on both sides.** -/
theorem obs_unalloc (P : Profile) {p : Pt H} (hp : dom p) {c : Call}
    (ha : p.1.funcs.length ≤ c.1) :
    obs P p c = ∅ ∧ Silmaril.Wasm.Atlas.Core.obs P (ptCore p) (callCore c) = ∅ := by
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp hp.2.1
  refine ⟨Set.eq_empty_of_forall_notMem fun b hb => absurd hb.1 (by omega), ?_⟩
  rw [ptCore_eq hX]
  exact core_beh_unalloc P _ X (by rw [funcs_length_image hX]; exact ha) _

/-! ## The equality embedding at the deterministic profile -/

/-- Core's `$invoke` premises on a Core point. -/
def CallOk (x : Silmaril.Wasm.Atlas.Core.Pt H) (c : Silmaril.Wasm.Atlas.Core.Call) : Prop :=
  Silmaril.Wasm.Execution.Core.InvokeOk x.1 c.1 c.2

/-- `core|S` observing only calls that satisfy `$invoke`'s premises. -/
def coreModelOk (P : Profile) (H : Type) (S : FeatureSet) : WasmModel :=
  { coreModel P H S with
    obs := fun x c => {b | CallOk x c ∧ b ∈ Silmaril.Wasm.Atlas.Core.obs P x c} }

/-- The own 2.0 observations of calls whose image satisfies `$invoke`'s premises. -/
def obsOk (P : Profile) (p : Pt H) (c : Call) : Set (Behaviour CVal) :=
  {b | CallOk (ptCore p) (callCore c) ∧ b ∈ obs P p c}

/-- The domain of the equality: every call whose image satisfies `$invoke`'s premises has a
closed-host 2.0 behaviour (it neither gets stuck nor reaches a host call). -/
def domDet (g : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool) (p : Pt H) : Prop :=
  dom p ∧ ∀ c : Call, CallOk (ptCore p) (callCore c) →
    (Silmaril.Wasm.V2.Execution.behaviours (Profile.deterministic g) closedV p.1 c.1
      c.2).Nonempty

/-- The own 2.0 model at `Profile.deterministic g` on `domDet g`, observing `obsOk`. -/
def v20ownDet (g : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool) (H : Type) :
    WasmModel :=
  { v20own (Profile.deterministic g) H with
    obs := obsOk (Profile.deterministic g)
    dom := domDet g }

theorem obsOk_eq (g : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool) {p : Pt H}
    (hp : domDet g p) (c : Call) :
    (coreModelOk (Profile.deterministic g) H v20).view some (ptCore p) (callCore c) =
      obsOk (Profile.deterministic g) p c := by
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp hp.1.2.1
  ext b
  simp only [WasmModel.view, coreModelOk, obsOk, obs, Option.some.injEq, Set.mem_ofPred_eq,
    exists_eq_right]
  refine and_congr_right fun hok => ?_
  have htot := hp.2 c hok
  obtain ⟨fi, -, -, hfi, -⟩ := hok
  have ha : c.1 < p.1.funcs.length := by
    rw [ptCore_eq hX] at hfi
    rw [← funcs_length_image hX]
    exact (List.getElem?_eq_some_iff.mp hfi).1
  rw [ptCore_eq hX]
  simp only [Silmaril.Wasm.Atlas.Core.obs, callCore, ha, true_and]
  rw [v20_core_beh_det_of_closed g hp.1.1 hX hp.1.2.2.1 hp.1.2.2.2 ha c.2 htot]
  exact Iff.rfl

/-- **The equality embedding at the deterministic profile.** -/
def v20EmbDet (g : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool) (H : Type) :
    (v20ownDet g H).Emb (coreModelOk (Profile.deterministic g) H v20) where
  mod := modCore
  valid := (v20Emb (Profile.deterministic g) H).valid
  pt := ptCore
  call := callCore
  readback := some
  dom _ hp := ptCore_dom hp.1
  dir := .eq
  sat _ hp c := obsOk_eq g hp c

theorem v20EmbDet_dir (g : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool)
    (H : Type) : (v20EmbDet g H).dir = .eq := rfl

/-- The equality atlas transition of `v20EmbDet`. -/
def v20TransDet (g : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool) (H : Type) :
    Transition (v20ownDet g H).chart
      ((coreModelOk (Profile.deterministic g) H v20).viewChart some) :=
  (v20EmbDet g H).toTransition

/-! ## Instantiation as observations -/

/-- **The 2.0 instantiation model**: calls are a module and its imports. A call is observed
when the module has a Core image and no defined globals (`InstantiationBounds.noGlobals`). -/
def v20inst (P : Profile) (H : Type) : WasmModel where
  feats := Silmaril.Wasm.Models.v20
  Module := Silmaril.Wasm.V2.Module
  Valid := (v20own P H).Valid
  Pt := Pt H
  Call := Silmaril.Wasm.V2.Module × List Silmaril.Wasm.V2.Execution.ExternAddr
  Obs := Behaviour CVal
  obs p mx := {b | mx.1.globals = [] ∧ (Silmaril.Wasm.V2.Module.toCore mx.1).isSome ∧
    b ∈ Silmaril.Proofs.Wasm.Models.V2Core.instObs P p mx}
  dom := dom

/-- **The Core instantiation model** restricted to `S`. -/
def coreInst (P : Profile) (H : Type) (S : FeatureSet) : WasmModel where
  feats := S
  Module := Silmaril.Wasm.Module
  Valid := ValidIn S
  Pt := Silmaril.Wasm.Atlas.Core.Pt H
  Call := Silmaril.Wasm.Module × List Silmaril.Wasm.Execution.Core.ExternAddr
  Obs := Behaviour CVal
  obs := Silmaril.Proofs.Wasm.Models.V2Core.coreInstObs P
  dom := coreDom S

/-- The call map of instantiation: translate the module and the imports. -/
def instCall (mx : Silmaril.Wasm.V2.Module × List Silmaril.Wasm.V2.Execution.ExternAddr) :
    Silmaril.Wasm.Module × List Silmaril.Wasm.Execution.Core.ExternAddr :=
  (modCore mx.1, mx.2.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore)

/-- **2.0 instantiation observations are Core instantiation observations** of the image. -/
theorem inst_obs_sub (P : Profile) {p : Pt H} (hp : dom p)
    (mx : Silmaril.Wasm.V2.Module × List Silmaril.Wasm.V2.Execution.ExternAddr) :
    (v20inst P H).obs p mx ⊆ Silmaril.Proofs.Wasm.Models.V2Core.coreInstObs P (ptCore p)
      (instCall mx) := by
  rintro b ⟨hg, hsome, hb⟩
  obtain ⟨cm, hcm⟩ := Option.isSome_iff_exists.mp hsome
  have e : modCore mx.1 = cm := by simp [modCore, hcm]
  simp only [instCall, e]
  exact Silmaril.Proofs.Wasm.Models.V2Core.instObs_sub P hp hcm hg mx.2 hb

/-- **The instantiation embedding** `v20inst → coreInst|v20` (direction `sub`). -/
def v20InstEmb (P : Profile) (H : Type) : (v20inst P H).Emb (coreInst P H v20) where
  mod := modCore
  valid := (v20Emb P H).valid
  pt := ptCore
  call := instCall
  readback := some
  dom _ hp := ptCore_dom hp
  dir := .sub
  sat _ hp mx := fun b hb => ⟨b, inst_obs_sub P hp mx hb, rfl⟩

/-- The atlas transition of the instantiation embedding. -/
def v20InstTrans (P : Profile) (H : Type) :
    Transition (v20inst P H).chart ((coreInst P H v20).viewChart some) :=
  (v20InstEmb P H).toTransition

end Silmaril.Wasm.Models.V2Core
