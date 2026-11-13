module

public import Silmaril.Wasm.Models.V2CoreSpec.Thms
public import Silmaril.Proofs.Wasm.Models.V2CoreSpecImg.GlobalsImg

/-!
# The reverse inclusion between single allocation and the spec's `$instantiate`, with hosts

An earlier step proved only `behaviours(residue) ⊆ behaviours(spec)` for hosts satisfying `HostEmbR`
(`Silmaril.Proofs.Wasm.Game.SpecGlobals.behavioursOf_embHR_sub`). The reverse inclusion needs no
new simulation: the inverse embedding (`Emb.flip`) has every global of its target in its image,
so its `OutG` condition is vacuous and the same forward simulation applies.

* `outG_flip`: the `OutG` condition of a flipped embedding holds for every `Good`;
* **`behavioursOf_embHR`**: behaviours are equal under an injective global embedding whose
  target satisfies `OutG Good`, for every host satisfying `HostEmbR Good`;
* **`spec_behaviours_eq_residueHR`**: spec preparation and the single-allocation residue have
  equal behaviours with such a host;
* **`once_eq_spec_hostR`**: every single-allocation run has a spec `$instantiate` run with
  equal behaviours;
* **`coreInstObs_eq_once`**: the spec observations of the call are exactly the behaviours of
  that single-allocation run (spec `$instantiate` is deterministic on valid inputs);
* **`instObs_spec_eq_once`**: at every point of `v20instHT`'s domain and every 2.0 instantiation
  run, the spec observations of the image are the Core behaviours of the run's single-allocation
  image `C`, which contain the run's 2.0 behaviours.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreSpecImg

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Proofs.Wasm.Game.SpecGlobals
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- The `OutG` condition of a flipped embedding is vacuous. -/
theorem outG_flip {ι : Nat → Nat} (hinj : Function.Injective ι) (Good : GlobalInst → Prop)
    (s : Store H) : OutG Good (Function.invFun ι) (Img ι) s := by
  intro b g hb _
  exact (hb ⟨ι b, ⟨b, rfl⟩, Function.leftInverse_invFun hinj b⟩).elim

/-- **Behaviours are invariant under an injective global embedding**, for a host commuting with
the embeddings on targets whose globals outside the image are `Good`. -/
theorem behavioursOf_embHR {Good : GlobalInst → Prop} {host : HostSemantics H}
    (hh : HostEmbR Good host) {ι : Nat → Nat} {c : Config H} {t : Store H}
    (stores : Emb ι Univ c.store t) (hinj : Function.Injective ι) (out : OutG Good ι Univ t) :
    behavioursOf P host (config ι t c) = behavioursOf P host c := by
  have hκ : ∀ a, Function.invFun ι (ι a) = a := Function.leftInverse_invFun hinj
  have back : Emb (Function.invFun ι) (Img ι) (config ι t c).store c.store :=
    Emb.flip hκ stores
  have dom : CfgDom (Img ι) (config ι t c) :=
    ⟨modDom_img ι c.frame.module, adminsDom_img ι c.code⟩
  have hinv : config (Function.invFun ι) c.store (config ι t c) = c := config_inv hκ c rfl t
  have hsub : behavioursOf P host (config ι t c) ⊆
      behavioursOf P host (config (Function.invFun ι) c.store (config ι t c)) :=
    behavioursOf_embHR_sub hh back dom (outG_flip hinj Good c.store)
  have hback : behavioursOf P host (config ι t c) ⊆ behavioursOf P host c := by
    rwa [hinv] at hsub
  have hfwd : behavioursOf P host c ⊆ behavioursOf P host (config ι t c) :=
    behavioursOf_embHR_sub hh stores ⟨modDom_univ _, adminsDom_univ _⟩ out
  exact Set.Subset.antisymm hback hfwd

/-- **Spec preparation and the single-allocation residue have equal behaviours** with a host
commuting with the embeddings on well-behaved targets, provided the spec preparation's store
holds only `Good` globals. -/
theorem spec_behaviours_eq_residueHR {Good : GlobalInst → Prop} {host : HostSemantics Nat}
    (hh : HostEmbR Good host) {s : Store Nat}
    (hb : ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module)
    {m : Module} {xas : List ExternAddr} {xts : List CExternType}
    (hxas : List.Forall₂ (ExternAddrOk s) xas xts)
    {s₁ : Store Nat} {f₁ : Frame} {vs : List Val}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    {c₁ : Config Nat} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st))
    (hgood : ∀ c st', prepare? evalConst? s m xas = some (c, st') →
      ∀ g ∈ c.store.globals, Good g) :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ P : Profile, behavioursOf P host (c.withStart st) =
        behavioursOf P host (c₁.withStart st) := by
  obtain ⟨c, ι, hc, hcode, hframe, hinj, he, -, -⟩ :=
    prepare_residue_emb (Emb.refl s) Function.injective_id hb (imports_globals_lt hxas) hg hp
  have hcode₁ : c₁.code = segCode m := residue_code hp
  have hc' : prepare? evalConst? s m xas = some (c, st) := by
    rw [← map_external_id xas]
    exact hc
  have hcfg : c.withStart st = config ι c.store (c₁.withStart st) :=
    withStart_config (hcode.trans hcode₁) hcode₁ hframe st
  have he' : Emb ι Univ (c₁.withStart st).store c.store := by
    rw [withStart_store]
    exact he
  have hout : OutG Good ι Univ c.store := fun _ g _ hgb =>
    hgood c st hc' g (List.mem_of_getElem? hgb)
  refine ⟨c, hc', fun P => ?_⟩
  rw [hcfg]
  exact behavioursOf_embHR hh he' hinj hout

/-- **Every single-allocation run has a spec `$instantiate` run with equal behaviours**, for a
host commuting with the embeddings on well-behaved targets. -/
theorem once_eq_spec_hostR {Good : GlobalInst → Prop} {host : HostSemantics Nat}
    (hh : HostEmbR Good host) {s : Store Nat} (hs : GlobalsNamed s) {m : Module}
    {xas : List ExternAddr} {C : Config Nat}
    (hgood : ∀ c st', prepare? evalConst? s m xas = some (c, st') → ∀ g ∈ c.store.globals, Good g)
    (h : Silmaril.Wasm.V2.Execution.Once.CoreInstantiateOnce P host s m xas C) :
    ∃ C', Instantiate P host s m xas C' ∧
      ∀ P' : Profile, behavioursOf P' host C' = behavioursOf P' host C := by
  obtain ⟨xtE, xtI, -, hxas⟩ := h.1
  obtain ⟨s₁, f₁, vs, c₁, st, hg, hp, rfl⟩ :=
    Silmaril.Proofs.Wasm.Models.V2CoreSpec.once_prepare h
  obtain ⟨c, hc, hbeh⟩ := spec_behaviours_eq_residueHR hh hs hxas hg hp hgood
  have hI : Instantiate P host s m xas (c.withStart st) :=
    (prepare?_iff h.1).mp (by rw [hc]; rfl)
  exact ⟨c.withStart st, hI, hbeh⟩

/-- **The spec observations are the behaviours of a single-allocation run**: spec
`$instantiate` is deterministic on valid inputs, and its run has the behaviours of the
single-allocation run. -/
theorem coreInstObs_eq_once {Good : GlobalInst → Prop} {host : HostSemantics Nat}
    (hh : HostEmbR Good host) {s : Store Nat} (hs : GlobalsNamed s) {m : Module}
    {xas : List ExternAddr} {C : Config Nat}
    (hgood : ∀ c st', prepare? evalConst? s m xas = some (c, st') → ∀ g ∈ c.store.globals, Good g)
    (h : Silmaril.Wasm.V2.Execution.Once.CoreInstantiateOnce P host s m xas C) :
    Silmaril.Proofs.Wasm.Models.V2Core.coreInstObs P (s, host) (m, xas) = behavioursOf P host C := by
  obtain ⟨C', hC', hbeh⟩ := once_eq_spec_hostR hh hs hgood h
  have huniq : ∀ D, Instantiate P host s m xas D → D = C' := by
    intro D hD
    have hD' := (prepare?_iff (P := P) (host := host) h.1).mpr hD
    have hC'' := (prepare?_iff (P := P) (host := host) h.1).mpr hC'
    exact Option.some.inj (hD'.symm.trans hC'')
  ext b
  constructor
  · rintro ⟨D, hD, hb⟩
    rw [huniq D hD, hbeh P] at hb
    exact hb
  · intro hb
    exact ⟨C', hC', (hbeh P).symm ▸ hb⟩

/-- **The reverse direction, up to the call-level simulation**: at every point of
`v20instHT`'s domain, every 2.0 instantiation run `c` of a module with a Core image has a
single-allocation image `C` such that the spec observations of the image call are exactly the
Core behaviours of `C`, and these contain the mapped 2.0 behaviours of `c`. -/
theorem instObs_spec_eq_once {p : Pt Nat} (hp : dom p) (hv : HostEmbV p.2)
    (hs : GlobalsNamed (ptCore p).1) {m : Silmaril.Wasm.V2.Module} {cm : Module}
    (hcm : Silmaril.Wasm.V2.Module.toCore m = some cm)
    {xas : List Silmaril.Wasm.V2.Execution.ExternAddr} {c : Silmaril.Wasm.V2.Execution.Config Nat}
    (hc : Silmaril.Wasm.V2.Execution.Instantiate P p.2 p.1 m xas c) :
    ∃ C, Silmaril.Proofs.Wasm.Models.V2Core.coreInstObs P (ptCore p)
        (cm, xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) =
        behavioursOf P (liftHost p.2) C ∧
      Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
        (Silmaril.Wasm.V2.Execution.behavioursOf P p.2 c) ⊆ behavioursOf P (liftHost p.2) C := by
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp hp.2.1
  have hpt : ptCore p = (X, liftHost p.2) := by simp [ptCore, hX]
  obtain ⟨C, hC, hsub⟩ := Silmaril.Proofs.Wasm.Models.V2CoreInst.instantiate_behaviours_sub_once P
    hp.1 hX hcm hp.2.2.1 hp.2.2.2 hc
  have hsX : GlobalsNamed X := by rw [hpt] at hs; exact hs
  have himg : SpecGlobalsImg X := specGlobalsImg_of (gsImg_toCore hX)
  obtain ⟨ixt, xt, hok, -⟩ := hc.valid
  have hvalid : Silmaril.Wasm.V2.Validation.ModuleValid m := ⟨ixt, xt, hok⟩
  have heq := coreInstObs_eq_once (hostEmbR_liftHost hv) hsX
    (fun c' st' hc' => himg m cm _ c' st' hvalid hcm hc') hC
  rw [hpt]
  exact ⟨C, heq, hsub⟩

end Silmaril.Proofs.Wasm.Models.V2CoreSpecImg
