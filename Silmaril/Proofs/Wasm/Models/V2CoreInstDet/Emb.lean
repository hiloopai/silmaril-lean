module

public import Silmaril.Proofs.Wasm.Models.V2CoreInstDet.Det
public import Silmaril.Wasm.Execution.Core.Exec.Instantiate
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# The deterministic instantiation embedding, and why `instCall` cannot be used

* `badModule_not_ok`, `coreInstObs_bad`: `badModule` is not valid, so it has no spec
  instantiation;
* **`obs_eq_det`**: at points of `domInstDet g`, the spec observations of `instCallE mx` are
  `v20instG`'s observations of `mx`, for every call `mx`;
* **`instCall_not_eq`** (refutation): with `instCall`, equality fails at every profile, at the
  empty store with the closed host. `noImg` is a 2.0 module whose one function body holds
  `i32.wrap_i32`, a `cvtop` with no `$cvtop__` equation. It has no Core image, so `instCall`
  sends it to the empty Core module. Core instantiates the empty module, and that run returns
  `[]`, but `v20instG` observes nothing on `noImg`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstDet

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
  Silmaril.Wasm.Models.V2CoreInst Silmaril.Wasm.Models.V2CoreInstDet Silmaril.Proofs.Wasm.Models.V2Core
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type}

/-! ## `badModule` has no instantiation -/

/-- `badModule` is not valid: its start function does not exist. -/
theorem badModule_not_ok {mt : Silmaril.Wasm.Validation.CModuleType} :
    ¬ Silmaril.Wasm.Validation.ModuleOk badModule mt := by
  intro h
  cases h with
  | mk htypes himports hC' hC htags hglobals hmems htables hfuncs hdata helems hstart =>
    simp only [badModule] at himports hfuncs hstart
    cases himports
    cases hfuncs
    subst hC hC'
    obtain ⟨d, hd, -⟩ := hstart ⟨0⟩ rfl
    simp [Silmaril.Wasm.Validation.CExternType.funcs] at hd

/-- The spec observations of the uninstantiable call are empty. -/
theorem coreInstObs_bad (P : Profile) (x : Silmaril.Wasm.Atlas.Core.Pt H) :
    coreInstObs P x (badModule, []) = ∅ := by
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨C, hC, -⟩
  obtain ⟨_, _, hok, -⟩ := hC.valid
  exact badModule_not_ok hok

/-- Reading `coreInst`'s observations back along `some` changes nothing. -/
theorem view_some (P : Profile) (S : FeatureSet) (x : Silmaril.Wasm.Atlas.Core.Pt Nat)
    (c : Silmaril.Wasm.Module × List Silmaril.Wasm.Execution.Core.ExternAddr) :
    (coreInst P Nat S).view some x c = coreInstObs P x c := by
  ext b
  simp [WasmModel.view, coreInst]
  rfl

/-! ## The equality -/

/-- The equality on a call of a 2.0-valid module with a Core image. -/
theorem obs_eq_det_valid (g : GrowKind → Nat → Nat → Nat → Bool) {p : Pt Nat}
    (hp : domInstDet g p) {m : Silmaril.Wasm.V2.Module} {cm : Module}
    (xas : List Silmaril.Wasm.V2.Execution.ExternAddr)
    (hcm : Silmaril.Wasm.V2.Module.toCore m = some cm)
    (hv : Silmaril.Wasm.V2.Validation.ModuleValid m) :
    coreInstObs (Profile.deterministic g) (ptCore p)
        (cm, xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) =
      (v20instG (Profile.deterministic g) Nat).obs p (m, xas) := by
  have hsome : (Silmaril.Wasm.V2.Module.toCore m).isSome := by rw [hcm]; rfl
  have hcall : instCall (m, xas) =
      (cm, xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) := by
    simp [instCall, modCore, hcm]
  ext b
  constructor
  · intro hb
    obtain ⟨D, hD, -⟩ := id hb
    obtain ⟨c, hc, htot⟩ := hp.2 m cm xas hv hcm ⟨D, hD⟩
    exact ⟨hsome, (instObs_eq_det g hp.1 hcm hc htot) ▸ hb⟩
  · intro hb
    have h : b ∈ coreInstObs (Profile.deterministic g) (ptCore p) (instCall (m, xas)) :=
      inst_obs_sub_spec_H (Profile.deterministic g) hp.1.1 hp.1.2.1 hp.1.2.2
        (Silmaril.Wasm.Models.V2CoreSpecImg.specGlobalsImg p hp.1.1) (m, xas) hb
    exact hcall ▸ h

/-- `v20instG` observes nothing on a module that is not 2.0-valid. -/
theorem obs_invalid (P : Profile) (p : Pt Nat) {m : Silmaril.Wasm.V2.Module}
    (xas : List Silmaril.Wasm.V2.Execution.ExternAddr)
    (hv : ¬ Silmaril.Wasm.V2.Validation.ModuleValid m) :
    (v20instG P Nat).obs p (m, xas) = ∅ := by
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, c, hc, -⟩
  obtain ⟨ixt, xt, hok, -⟩ := hc.valid
  exact hv ⟨ixt, xt, hok⟩

/-- `v20instG` observes nothing on a module without a Core image. -/
theorem obs_noImage (P : Profile) (p : Pt Nat) {m : Silmaril.Wasm.V2.Module}
    (xas : List Silmaril.Wasm.V2.Execution.ExternAddr)
    (hcm : Silmaril.Wasm.V2.Module.toCore m = none) :
    (v20instG P Nat).obs p (m, xas) = ∅ := by
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hsome, -⟩
  simp [hcm] at hsome

/-- **The deterministic instantiation equality**: at points of `domInstDet g`, the spec
observations of `instCallE mx` are `v20instG`'s observations of `mx`. -/
theorem obs_eq_det (g : GrowKind → Nat → Nat → Nat → Bool) {p : Pt Nat} (hp : domInstDet g p)
    (mx : Silmaril.Wasm.V2.Module × List Silmaril.Wasm.V2.Execution.ExternAddr) :
    (coreInst (Profile.deterministic g) Nat v20).view some (ptCore p) (instCallE mx) =
      (v20instG (Profile.deterministic g) Nat).obs p mx := by
  rw [view_some]
  obtain ⟨m, xas⟩ := mx
  cases hcm : Silmaril.Wasm.V2.Module.toCore m with
  | none =>
    have e : instCallE (m, xas) = (badModule, []) := by simp [instCallE, hcm]
    rw [e, coreInstObs_bad, obs_noImage _ p xas hcm]
    rfl
  | some cm =>
    by_cases hv : Silmaril.Wasm.V2.Validation.ModuleValid m
    · have e : instCallE (m, xas) =
          (cm, xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) := by
        simp [instCallE, hcm, hv]
      rw [e]
      exact obs_eq_det_valid g hp xas hcm hv
    · have e : instCallE (m, xas) = (badModule, []) := by simp [instCallE, hcm, hv]
      rw [e, coreInstObs_bad, obs_invalid _ p xas hv]
      rfl

/-! ## The refutation with `instCall` -/

/-- A 2.0 module with no Core image: its function body is `i32.wrap_i32`, a `cvtop` with no
`$cvtop__` equation. -/
def noImg : Silmaril.Wasm.V2.Module :=
  { funcs := [⟨⟨0⟩, [], [.cvtOp (.int .i32) (.int .i32) .wrap]⟩] }

theorem noImg_toCore : Silmaril.Wasm.V2.Module.toCore noImg = none := rfl

/-- The empty 2.0 store with the closed host. -/
def emptyPt : Pt Nat := ({}, closedV)

theorem emptyPt_dom (P : Profile) : (v20instHT P).dom emptyPt := by
  refine ⟨⟨⟨fun _ _ h => by simp [emptyPt] at h, fun _ _ h => by simp [emptyPt] at h,
    fun _ _ h => by simp [emptyPt] at h, fun _ _ h => by simp [emptyPt] at h⟩, rfl,
    closedV_preserves, closedV_keeps⟩, hostEmbV_none, ?_⟩
  intro fi hfi
  have e : (ptCore emptyPt).1.funcs = [] := rfl
  rw [e] at hfi
  simp at hfi

/-- Core instantiates the empty module in every store, and that run returns `[]`. -/
theorem empty_returns (P : Profile) (host : HostSemantics H) (X : Store H) :
    Behaviour.returns [] ∈ coreInstObs P (X, host) ({}, []) := by
  have evaluator : EvalSound P host (fun _ _ _ => (none : Option (Store H × Val))) := by
    intro s f code final value impossible
    cases impossible
  have computed : instantiate? (fun _ _ _ => (none : Option (Store H × Val))) X {} [] =
      some ⟨X, {}, []⟩ := by rfl
  have valid : Silmaril.Wasm.Validation.ModuleOk ({} : Module) ⟨[], []⟩ :=
    Silmaril.Wasm.Validation.validate?_sound (by rfl)
  exact ⟨_, instantiate?_sound evaluator computed ⟨[], [], valid, .nil⟩,
    returns_mem_behavioursOf .refl rfl⟩

/-- **Equality fails with `instCall`**, at every profile: at the empty store with the closed host,
the spec observations of `instCall (noImg, [])` contain `returns []`, and `v20instG` observes
nothing on `(noImg, [])`. -/
theorem instCall_not_eq (P : Profile) :
    ∃ p : Pt Nat, (v20instHT P).dom p ∧
      ∃ mx : Silmaril.Wasm.V2.Module × List Silmaril.Wasm.V2.Execution.ExternAddr,
        (coreInst P Nat v20).view some (ptCore p) (instCall mx) ≠ (v20instG P Nat).obs p mx := by
  refine ⟨emptyPt, emptyPt_dom P, (noImg, []), ?_⟩
  rw [view_some]
  intro heq
  have e : instCall (noImg, []) = ({}, []) := by simp [instCall, modCore, noImg_toCore]
  have hmem : Behaviour.returns [] ∈ coreInstObs P (ptCore emptyPt) (instCall (noImg, [])) :=
    e ▸ empty_returns P _ _
  rw [heq] at hmem
  obtain ⟨hsome, -⟩ := hmem
  rw [noImg_toCore] at hsome
  exact absurd hsome (by decide)

/-! ## Why the domain asks for 2.0 validity -/

/-- A 2.0 module with two memories: 2.0 rejects it, its Core image is valid. -/
def twoMem : Silmaril.Wasm.V2.Module :=
  { memories := [⟨⟨0, none⟩⟩, ⟨⟨0, none⟩⟩] }

/-- The Core image of `twoMem`. -/
def twoMemC : Module :=
  { memories := [⟨.i32, ⟨0, none⟩⟩, ⟨.i32, ⟨0, none⟩⟩] }

theorem twoMem_toCore : Silmaril.Wasm.V2.Module.toCore twoMem = some twoMemC := rfl

/-- 2.0 rejects `twoMem`: at most one memory. -/
theorem twoMem_not_ok {ixt xt : List Silmaril.Wasm.V2.ExternType} :
    ¬ Silmaril.Wasm.V2.Validation.ModuleOk twoMem ixt xt := by
  intro h
  cases h with
  | mk htypes himports hglobals htables hmems helems hdatas hfuncs hstart hexports hmems_le
      hnames hC hC' =>
    simp only [twoMem] at himports
    cases himports
    subst hC
    have hl := hmems.length_eq
    simp only [twoMem, List.length_cons, List.length_nil] at hl
    simp [Silmaril.Wasm.V2.ExternType.mems] at hmems_le
    omega

/-- Core instantiates `twoMemC` in every store. -/
theorem twoMemC_inst (P : Profile) (host : HostSemantics H) (X : Store H) :
    ∃ C, Instantiate P host X twoMemC [] C := by
  have evaluator : EvalSound P host (fun _ _ _ => (none : Option (Store H × Val))) := by
    intro s f code final value impossible
    cases impossible
  obtain ⟨c, computed⟩ : ∃ c,
      instantiate? (fun _ _ _ => (none : Option (Store H × Val))) X twoMemC [] = some c :=
    ⟨_, rfl⟩
  have valid : Silmaril.Wasm.Validation.ModuleOk twoMemC ⟨[], []⟩ :=
    Silmaril.Wasm.Validation.validate?_sound (by rfl)
  exact ⟨c, instantiate?_sound evaluator computed ⟨[], [], valid, .nil⟩⟩

/-- **No point satisfies `domInstDet`'s condition without the validity premise.** -/
theorem not_domInstDetU (g : GrowKind → Nat → Nat → Nat → Bool) (p : Pt Nat) :
    ¬ DomInstDetU g p := by
  intro h
  obtain ⟨c, hc, -⟩ := h twoMem twoMemC [] twoMem_toCore
    (twoMemC_inst (Profile.deterministic g) _ _)
  obtain ⟨ixt, xt, hok, -⟩ := hc.valid
  exact twoMem_not_ok hok

end Silmaril.Proofs.Wasm.Models.V2CoreInstDet
