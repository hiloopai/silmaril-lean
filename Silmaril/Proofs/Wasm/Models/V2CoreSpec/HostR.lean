module

public import Silmaril.Proofs.Wasm.Models.V2CoreSpec.Spec
public import Silmaril.Proofs.Wasm.Models.V2CoreSpec.LiftHost

/-!
# Single allocation in the spec's double allocation, with hosts induced from 2.0 hosts

`once_sub_spec_host` (`Host.lean`) needs a Core host blind to globals and functions, which
`liftHost src` is not once it answers. Here the host only needs to commute with the embeddings
whose targets hold `Good` globals outside the image (`HostEmbR Good`), and the spec
preparation's store must hold only `Good` globals:

* **`once_sub_spec_hostR`**: every single-allocation instantiation run has a spec
  `$instantiate` run whose behaviours (with that host) include its behaviours, at every profile;
* `coreInstObsOnce_sub_spec_hostR`: so single-allocation instantiation observations are spec
  observations;
* **`instObs_sub_spec_hostR`**: 2.0 instantiation observations of a module with a Core image are
  spec observations of the image, at every 2.0 point whose host commutes with the 2.0
  embeddings (`HostEmbV`), whose Core store satisfies `GlobalsNamed`, and whose spec
  preparations hold only images of 2.0 globals (`SpecGlobalsImg`). The Core host is
  `liftHost`, through `hostEmbR_liftHost`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreSpec

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Proofs.Wasm.Game.SpecGlobals (HostEmbR)
open Silmaril.Wasm.Numerics (Profile)

/-- **Single allocation is included in the spec's double allocation with a host commuting with
the embeddings on well-behaved targets**, with included behaviours at every profile. -/
theorem once_sub_spec_hostR {P : Profile} {Good : GlobalInst → Prop} {host : HostSemantics Nat}
    (hh : HostEmbR Good host) {s : Store Nat} (hs : GlobalsNamed s) {m : Module}
    {xas : List ExternAddr} {C : Config Nat}
    (hgood : ∀ c st', prepare? evalConst? s m xas = some (c, st') → ∀ g ∈ c.store.globals, Good g)
    (h : Silmaril.Wasm.V2.Execution.Once.CoreInstantiateOnce P host s m xas C) :
    ∃ C', Instantiate P host s m xas C' ∧
      ∀ P' : Profile, behavioursOf P' host C ⊆ behavioursOf P' host C' := by
  obtain ⟨xtE, xtI, -, hxas⟩ := h.1
  obtain ⟨s₁, f₁, vs, c₁, st, hg, hp, rfl⟩ := once_prepare h
  obtain ⟨c, hc, hbeh⟩ :=
    Silmaril.Wasm.Game.spec_behaviours_sub_residue_hostR hh hs hxas hg hp hgood
  have hI : Instantiate P host s m xas (c.withStart st) :=
    (prepare?_iff h.1).mp (by rw [hc]; rfl)
  exact ⟨c.withStart st, hI, hbeh⟩

/-- **Single-allocation instantiation observations are spec observations**, for a host
commuting with the embeddings on well-behaved targets. -/
theorem coreInstObsOnce_sub_spec_hostR (P : Profile) {Good : GlobalInst → Prop} {s : Store Nat}
    {host : HostSemantics Nat} (hh : HostEmbR Good host) (hs : GlobalsNamed s) (cm : Module)
    (cxas : List ExternAddr)
    (hgood : ∀ c st', prepare? evalConst? s cm cxas = some (c, st') →
      ∀ g ∈ c.store.globals, Good g) :
    Silmaril.Proofs.Wasm.Models.V2CoreInst.coreInstObsOnce P (s, host) (cm, cxas) ⊆
      Silmaril.Proofs.Wasm.Models.V2Core.coreInstObs P (s, host) (cm, cxas) := by
  rintro b ⟨C, hC, hbm⟩
  obtain ⟨C', hC', hbeh⟩ := once_sub_spec_hostR hh hs hgood hC
  exact ⟨C', hC', hbeh P hbm⟩

/-- **2.0 instantiation observations are spec observations of the image, with hosts**: at a 2.0
point whose host commutes with the 2.0 embeddings, whose Core store satisfies `GlobalsNamed`,
and whose spec preparations hold only images of 2.0 globals. -/
theorem instObs_sub_spec_hostR (P : Profile) {p : Pt Nat} (hp : dom p) (hv : HostEmbV p.2)
    (hs : GlobalsNamed (ptCore p).1) (himg : SpecGlobalsImg (ptCore p).1)
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
  exact coreInstObsOnce_sub_spec_hostR P (hostEmbR_liftHost hv) hs cm _
    (fun c st' hc' => himg m cm _ c st' hvalid hcm hc') hsub

end Silmaril.Proofs.Wasm.Models.V2CoreSpec
