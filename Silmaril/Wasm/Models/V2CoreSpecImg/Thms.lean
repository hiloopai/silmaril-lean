module

public import Silmaril.Wasm.Models.V2CoreSpec.Thms
import Silmaril.Proofs.Wasm.Models.V2CoreSpecImg.GlobalsImg
import Silmaril.Proofs.Wasm.Models.V2CoreSpecImg.Reverse

/-!
# `Task.specGlobalsImg` is proved

An earlier step froze `Silmaril.Wasm.Models.V2CoreSpec.Task.specGlobalsImg`: at every point of the 2.0
domain, the spec preparation (`prepare?`, the double allocation of `$instantiate`) of every
valid 2.0 module's Core image holds only images of 2.0 globals (`SpecGlobalsImg`). This header
proves it, so the instantiation embedding with hosts holds unconditionally:

* **`specGlobalsImg_of_toCore`**: `SpecGlobalsImg X` for the Core image `X` of every 2.0 store.
  Neither module validity nor `StoreWF` is used, and the extern addresses are arbitrary: the
  store's own globals are images; constant evaluation never changes the globals; an image
  instruction pushes only image values (the GC allocations and the extern/any conversions,
  which could produce non-image references, are not images of 2.0 instructions); and the global
  types of the image module are closed images of 2.0 global types.
* **`specGlobalsImg : Task.specGlobalsImg`**.
* **`v20InstEmbHU P : (v20instHT P).Emb (coreInst P Nat v20)`**, direction `sub`:
  `v20InstEmbHT` with the task discharged. Its points are those of the 2.0 domain whose host
  commutes with 2.0 global embeddings (`HostEmbV`) and whose Core store satisfies
  `GlobalsNamed`.
* `v20instH_dom_iff`: the `SpecGlobalsImg` conjunct of `v20instH`'s domain is redundant.

The reverse direction (spec observations inside 2.0 observations), as far as it goes:

* **`once_eq_spec_hostR`**: with a host commuting with the embeddings on well-behaved targets
  (`HostEmbR Good`), every single-allocation run has a spec `$instantiate` run with **equal**
  behaviours. The inverse embedding (`Emb.flip`) needs no `OutG` condition, so
  's forward simulation gives the other inclusion.
* **`instObs_spec_eq_once`**: at every point of `v20instHT`'s domain and every 2.0
  instantiation run `c` of a module with a Core image, the spec observations of the image call
  are exactly the Core behaviours of `c`'s single-allocation image `C`, and they contain `c`'s
  mapped 2.0 behaviours.

What is still missing for `coreInst ⊆ v20instG`: Core behaviours of `C` inside the mapped 2.0
behaviours of `c` (the backward 2.0→Core simulation at the instantiation configuration, which
the call model has only at the deterministic profile with the closed host, `v20EmbDet`), and
calls on which the 2.0 instantiation has no run but the Core one has.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreSpecImg

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models Silmaril.Wasm.Atlas Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Wasm.Numerics (Profile)

/-- **The spec preparations into the Core image of a 2.0 store hold only 2.0 globals.** -/
theorem specGlobalsImg_of_toCore {H : Type} {s : Silmaril.Wasm.V2.Execution.Store H}
    {X : Store H} (h : Silmaril.Wasm.V2.Execution.Store.toCore s = some X) :
    SpecGlobalsImg X :=
  Silmaril.Proofs.Wasm.Models.V2CoreSpecImg.specGlobalsImg_of
    (Silmaril.Proofs.Wasm.Models.V2CoreSpecImg.gsImg_toCore h)

/-- **`Task.specGlobalsImg` holds.** -/
theorem specGlobalsImg : Task.specGlobalsImg := by
  intro p hp
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp hp.2.1
  simp only [ptCore, hX, Option.getD_some]
  exact specGlobalsImg_of_toCore hX

/-- The `SpecGlobalsImg` conjunct of `v20instH`'s domain is redundant. -/
theorem v20instH_dom_iff (P : Profile) (p : Pt Nat) :
    (v20instH P).dom p ↔ (v20instHT P).dom p :=
  ⟨fun ⟨hd, hh, hs, _⟩ => ⟨hd, hh, hs⟩, fun ⟨hd, hh, hs⟩ => ⟨hd, hh, hs, specGlobalsImg p hd⟩⟩

/-- **The instantiation embedding with hosts, unconditionally** (direction `sub`). -/
def v20InstEmbHU (P : Profile) : (v20instHT P).Emb (coreInst P Nat v20) :=
  v20InstEmbHT specGlobalsImg P

theorem v20InstEmbHU_dir (P : Profile) : (v20InstEmbHU P).dir = .sub := rfl

/-- **Single allocation and the spec's `$instantiate` have equal behaviours** with hosts
commuting with the embeddings on well-behaved targets. -/
theorem once_eq_spec_hostR {P : Profile} {Good : GlobalInst → Prop} {host : HostSemantics Nat}
    (hh : Silmaril.Proofs.Wasm.Game.SpecGlobals.HostEmbR Good host) {s : Store Nat}
    (hs : GlobalsNamed s) {m : Module} {xas : List ExternAddr} {C : Config Nat}
    (hgood : ∀ c st', prepare? evalConst? s m xas = some (c, st') → ∀ g ∈ c.store.globals, Good g)
    (h : Silmaril.Wasm.V2.Execution.Once.CoreInstantiateOnce P host s m xas C) :
    ∃ C', Instantiate P host s m xas C' ∧
      ∀ P' : Profile, behavioursOf P' host C' = behavioursOf P' host C :=
  Silmaril.Proofs.Wasm.Models.V2CoreSpecImg.once_eq_spec_hostR hh hs hgood h

/-- **Spec observations of a 2.0 image are the Core behaviours of the single-allocation image
of the 2.0 run**, which contain the run's 2.0 behaviours. -/
theorem instObs_spec_eq_once {P : Profile} {p : Pt Nat} (hp : (v20instHT P).dom p)
    {m : Silmaril.Wasm.V2.Module} {cm : Module}
    (hcm : Silmaril.Wasm.V2.Module.toCore m = some cm)
    {xas : List Silmaril.Wasm.V2.Execution.ExternAddr} {c : Silmaril.Wasm.V2.Execution.Config Nat}
    (hc : Silmaril.Wasm.V2.Execution.Instantiate P p.2 p.1 m xas c) :
    ∃ C, Silmaril.Proofs.Wasm.Models.V2Core.coreInstObs P (ptCore p)
        (cm, xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) =
        behavioursOf P (liftHost p.2) C ∧
      Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
        (Silmaril.Wasm.V2.Execution.behavioursOf P p.2 c) ⊆ behavioursOf P (liftHost p.2) C :=
  Silmaril.Proofs.Wasm.Models.V2CoreSpecImg.instObs_spec_eq_once hp.1 hp.2.1 hp.2.2 hcm hc

/--
info: 'Silmaril.Wasm.Models.V2CoreSpecImg.instObs_spec_eq_once' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms instObs_spec_eq_once

/--
info: 'Silmaril.Wasm.Models.V2CoreSpecImg.specGlobalsImg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms specGlobalsImg

/--
info: 'Silmaril.Wasm.Models.V2CoreSpecImg.v20InstEmbHU' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms v20InstEmbHU

end Silmaril.Wasm.Models.V2CoreSpecImg
