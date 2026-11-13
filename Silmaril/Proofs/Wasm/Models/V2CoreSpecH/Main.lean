module

public import Silmaril.Proofs.Wasm.Models.V2CoreSpecH.InstGen
public import Silmaril.Wasm.Models.V2CoreSpec.Thms
public import Silmaril.Wasm.Models.V2CoreSpecImg.Thms
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateIff

/-!
# Single allocation in the spec's double allocation, at every host type

`Silmaril.Proofs.Wasm.Models.V2CoreSpec.instObs_sub_spec_hostR` is stated at `Pt Nat` because the
residue embedding it goes through (`Silmaril.Proofs.Wasm.Game.SpecGlobals.prepare_residue_emb`,
with the closed forms of `SpecGlobals.Inst`) is stated over `Store Nat`. Those proofs never use
the host type: `Inst.lean` and `InstGen.lean` of this topic are copies of them with
`Store Nat`/`Config Nat`/`FuncInst Nat` replaced by `Store H`/`Config H`/`FuncInst H`, and
elaborate unchanged. The step simulation (`stepHR`, `behavioursOf_embHR_sub`) and the host
transport (`hostEmbR_liftHost`) were already generic. Here:

* `spec_behaviours_sub_residueHRH`: `SpecGlobals.spec_behaviours_sub_residueHR` at every `H`;
* `once_sub_spec_hostRH`, `coreInstObsOnce_sub_spec_hostRH`: the single-allocation inclusions;
* **`instObs_sub_spec_hostRH`**: `instObs_sub_spec_hostR` at every 2.0 point `p : Pt H`;
* **`specGlobalsImgH`**: `Task.specGlobalsImg` at every `H` (the proof  never used
  `Nat`).

New proofs, following `V2CoreSpec/HostR.lean` and `SpecGlobals/StepHostOut.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreSpecH

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Proofs.Wasm.Game.SpecGlobals
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

theorem withStart_storeH (c : Config H) (st : Option FuncIdx) :
    (c.withStart st).store = c.store := by
  cases st <;> rfl

theorem withStart_eqH (c : Config H) (st : Option FuncIdx) :
    c.withStart st = ⟨c.store, c.frame, c.code ++ startCode st⟩ := by
  cases st <;> simp only [Config.withStart, startCode, List.append_nil]

theorem admins_segCodeH (ρ : Nat → Nat) (m : Module) (st : Option FuncIdx) :
    Silmaril.Proofs.Wasm.Game.SpecGlobals.admins ρ (segCode m ++ startCode st) =
      segCode m ++ startCode st := by
  cases st <;> simp only [segCode, startCode, admins_append, admins_expression, admins_cons,
    admins_nil, admin]

/-- The spec configuration with its start call is the renamed residue configuration. -/
theorem withStart_configH {ι : Nat → Nat} {c c₁ : Config H} {m : Module}
    (hcode : c.code = segCode m) (hcode₁ : c₁.code = segCode m)
    (hframe : c.frame = Silmaril.Proofs.Wasm.Game.SpecGlobals.frame ι c₁.frame)
    (st : Option FuncIdx) :
    c.withStart st = config ι c.store (c₁.withStart st) := by
  rw [withStart_eqH, withStart_eqH]
  simp only [config, hcode, hcode₁, hframe, admins_segCodeH]

/-- **Single-allocation residue behaviours are spec behaviours** for a host commuting with the
embeddings on well-behaved targets, at every host type. -/
theorem spec_behaviours_sub_residueHRH {Good : GlobalInst → Prop} {host : HostSemantics H}
    (hh : HostEmbR Good host) {s : Store H}
    (hb : ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module)
    {m : Module} {xas : List ExternAddr} {xts : List CExternType}
    (hxas : List.Forall₂ (ExternAddrOk s) xas xts)
    {s₁ : Store H} {f₁ : Frame} {vs : List Val}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    {c₁ : Config H} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st))
    (hgood : ∀ c st', prepare? evalConst? s m xas = some (c, st') →
      ∀ g ∈ c.store.globals, Good g) :
    ∃ c : Config H, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ P : Profile, behavioursOf P host (c₁.withStart st) ⊆
        behavioursOf P host (c.withStart st) := by
  obtain ⟨c, ι, hc, hcode, hframe, -, he, -, -⟩ :=
    prepare_residue_emb (Emb.refl s) Function.injective_id hb (imports_globals_lt hxas) hg hp
  have hcode₁ : c₁.code = segCode m := residue_code hp
  have hc' : prepare? evalConst? s m xas = some (c, st) := by
    rw [← Silmaril.Proofs.Wasm.Game.SpecGlobals.map_external_id xas]
    exact hc
  have hcfg : c.withStart st = config ι c.store (c₁.withStart st) :=
    withStart_configH (hcode.trans hcode₁) hcode₁ hframe st
  have he' : Emb ι (fun _ => True) (c₁.withStart st).store c.store := by
    rw [withStart_storeH]
    exact he
  have hout : OutG Good ι (fun _ => True) c.store := fun _ g _ hgb =>
    hgood c st hc' g (List.mem_of_getElem? hgb)
  have hdom : CfgDom (fun _ => True) (c₁.withStart st) :=
    ⟨modDom_univ _, adminsDom_univ _⟩
  refine ⟨c, hc', fun P => ?_⟩
  rw [hcfg]
  exact behavioursOf_embHR_sub hh he' hdom hout

/-- **Single allocation is included in the spec's double allocation**, at every host type, for
a host commuting with the embeddings on well-behaved targets. -/
theorem once_sub_spec_hostRH {P : Profile} {Good : GlobalInst → Prop} {host : HostSemantics H}
    (hh : HostEmbR Good host) {s : Store H} (hs : GlobalsNamed s) {m : Module}
    {xas : List ExternAddr} {C : Config H}
    (hgood : ∀ c st', prepare? evalConst? s m xas = some (c, st') → ∀ g ∈ c.store.globals, Good g)
    (h : Silmaril.Wasm.V2.Execution.Once.CoreInstantiateOnce P host s m xas C) :
    ∃ C', Instantiate P host s m xas C' ∧
      ∀ P' : Profile, behavioursOf P' host C ⊆ behavioursOf P' host C' := by
  obtain ⟨xtE, xtI, -, hxas⟩ := h.1
  obtain ⟨s₁, f₁, vs, c₁, st, hg, hp, rfl⟩ :=
    Silmaril.Proofs.Wasm.Models.V2CoreSpec.once_prepare h
  obtain ⟨c, hc, hbeh⟩ := spec_behaviours_sub_residueHRH hh hs hxas hg hp hgood
  have hI : Instantiate P host s m xas (c.withStart st) :=
    (prepare?_iff h.1).mp (by rw [hc]; rfl)
  exact ⟨c.withStart st, hI, hbeh⟩

/-- Single-allocation instantiation observations are spec observations, at every host type. -/
theorem coreInstObsOnce_sub_spec_hostRH (P : Profile) {Good : GlobalInst → Prop} {s : Store H}
    {host : HostSemantics H} (hh : HostEmbR Good host) (hs : GlobalsNamed s) (cm : Module)
    (cxas : List ExternAddr)
    (hgood : ∀ c st', prepare? evalConst? s cm cxas = some (c, st') →
      ∀ g ∈ c.store.globals, Good g) :
    Silmaril.Proofs.Wasm.Models.V2CoreInst.coreInstObsOnce P (s, host) (cm, cxas) ⊆
      Silmaril.Proofs.Wasm.Models.V2Core.coreInstObs P (s, host) (cm, cxas) := by
  rintro b ⟨C, hC, hbm⟩
  obtain ⟨C', hC', hbeh⟩ := once_sub_spec_hostRH hh hs hgood hC
  exact ⟨C', hC', hbeh P hbm⟩

/-- **`Task.specGlobalsImg` at every host type.** -/
theorem specGlobalsImgH (p : Pt H) (hp : dom p) : SpecGlobalsImg (ptCore p).1 := by
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp hp.2.1
  simp only [ptCore, hX, Option.getD_some]
  exact Silmaril.Wasm.Models.V2CoreSpecImg.specGlobalsImg_of_toCore hX

/-- **2.0 instantiation observations are spec observations of the image, with hosts, at every
host type**: at a 2.0 point whose host commutes with the 2.0 embeddings and whose Core store
satisfies `GlobalsNamed`. The `SpecGlobalsImg` hypothesis of the `Nat` form is discharged by
`specGlobalsImgH`. -/
theorem instObs_sub_spec_hostRH (P : Profile) {p : Pt H} (hp : dom p) (hv : HostEmbV p.2)
    (hs : GlobalsNamed (ptCore p).1)
    {m : Silmaril.Wasm.V2.Module} {cm : Module}
    (hcm : Silmaril.Wasm.V2.Module.toCore m = some cm)
    (xas : List Silmaril.Wasm.V2.Execution.ExternAddr) :
    Silmaril.Proofs.Wasm.Models.V2Core.instObs P p (m, xas) ⊆
      Silmaril.Proofs.Wasm.Models.V2Core.coreInstObs P (ptCore p)
        (cm, xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) := by
  intro b hb
  obtain ⟨c, hc, -⟩ := id hb
  obtain ⟨ixt, xt, hok, -⟩ := hc.valid
  have hvalid : Silmaril.Wasm.V2.Validation.ModuleValid m := ⟨ixt, xt, hok⟩
  have hsub := Silmaril.Proofs.Wasm.Models.V2CoreInst.instObs_sub_once P hp hcm xas hb
  exact coreInstObsOnce_sub_spec_hostRH P (hostEmbR_liftHost hv) hs cm _
    (fun c st' hc' => specGlobalsImgH p hp m cm _ c st' hvalid hcm hc') hsub

end Silmaril.Proofs.Wasm.Models.V2CoreSpecH
