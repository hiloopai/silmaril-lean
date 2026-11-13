module

public import Silmaril.Proofs.Wasm.Models.V2CoreSpec.Spec
import Silmaril.Proofs.Wasm.Models.V2CoreSpec.Host
import Silmaril.Proofs.Wasm.Models.V2CoreSpec.Named
import Silmaril.Proofs.Wasm.Models.V2CoreSpec.HostR

/-!
# Instantiation observations with defined globals, against the spec's `$instantiate`

`Silmaril.Wasm.Models.V2CoreInst` removed `noGlobals` against **single allocation**
(`coreInstOnce`), and left open the inclusion into the specification's double-allocating
`$instantiate` (`coreInst`). This header proves it **for host-free runs**:

* **`once_sub_spec`**: without host calls, every single-allocation instantiation run has a spec
  `$instantiate` run with the same behaviours, at every profile, for a store whose functions
  name only existing globals (`GlobalsNamed`). The spec store holds every global twice; the
  global-address embedding of `Silmaril.Wasm.Game.SpecGlobals` relates the two
  (`Silmaril.Wasm.Game.spec_behaviours_eq_residue`);
* `coreInstOnce_obs_sub_spec`: so at host-free points `coreInstOnce` observes no more than
  `coreInst`;
* **`v20InstEmbNH P : (v20instNH P).Emb (coreInst P Nat v20)`**, direction `sub`: the 2.0
  instantiation model on every module with a Core image (no `globals = []` guard), restricted to
  host-free points whose Core store satisfies `GlobalsNamed`, embeds into the spec's Core
  instantiation model.

Not covered: points with host functions. A host call on the spec store sees `n` unreachable
`$evalglobals` copies, so the inclusion needs hosts invariant under global-address embeddings,
and the step simulation `Silmaril.Proofs.Wasm.Game.SpecGlobals.step` is stated host-free. The
store is `Store Nat` (the instantiation embedding of `Silmaril.Wasm.Game.SpecGlobals` is stated
there).

An earlier step (hosts, and where `GlobalsNamed` comes from):

* **`once_sub_spec_host`**, `coreInstOnce_obs_sub_spec_host`: the same inclusion, with equal
  behaviours **with the host**, for every Core host blind to globals and functions
  (`GlobalsBlind`: it keeps them and does not read them). `noHostC_blind` and
  `pureHost_blind` show the hypothesis holds for the empty host and for every host that leaves
  the store unchanged. The step simulation is `Silmaril.Proofs.Wasm.Game.SpecGlobals.stepH`, for
  hosts commuting with the embeddings.
* **`dom_not_globalsNamed`**: `GlobalsNamed` does **not** follow from the 2.0 domain
  (`StoreWF` constrains function addresses only); **`dom_globalsNamed_iff`**: on the 2.0
  domain it is `GlobalsNamedV` of the 2.0 store, so `v20instNH`'s domain can be read on the
  2.0 store.

Not covered: `GlobalsBlind` asks that calls survive *any* replacement of globals and
functions, which the induced host `liftHost` of a 2.0 host does not satisfy once it answers at
all (the replaced store need not be a 2.0 image). The 2.0 model at points with hosts needs the
weaker condition of `stepH` (`HostEmb`: commuting with the embeddings only), transported through
`liftHost`.

An earlier step (2.0 hosts through `liftHost`):

* **`hostEmbR_liftHost`**: for a 2.0 host commuting with the 2.0 global embeddings
  (`HostEmbV`), the induced Core host `liftHost src` commutes with every Core embedding whose
  target holds images of 2.0 globals outside the embedding (`HostEmbR GImg`, the relativised
  `HostEmb` of `Silmaril.Proofs.Wasm.Game.SpecGlobals.StepHostOut`). `hostEmbV_blind` and
  `pureHostV_blind`: 2.0 hosts that keep and do not read globals and functions, in particular
  every store-preserving 2.0 host, satisfy `HostEmbV`;
* **`v20InstEmbH P : (v20instH P).Emb (coreInst P Nat v20)`**, direction `sub`: the 2.0
  instantiation model at points whose host satisfies `HostEmbV` (no longer only the empty
  host), whose Core store satisfies `GlobalsNamed`, and whose spec preparations hold only
  images of 2.0 globals (`SpecGlobalsImg`);
* `Task.specGlobalsImg` (frozen): `SpecGlobalsImg` holds at every point of the 2.0 domain.
  Under it, **`v20InstEmbHT`** drops that condition; its domain contains `v20instNH`'s
  (`v20instNH_dom_sub`) and points with answering hosts (`exists_domHT_answers`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreSpec

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Atlas Silmaril.Wasm.Models.V2Core
open Silmaril.Wasm.Models.V2CoreInst
open Silmaril.Wasm.Numerics (Profile)

/-- **Single allocation is included in the spec's double allocation without host calls**, with
equal behaviours at every profile. -/
theorem once_sub_spec {P : Profile} {host : Silmaril.Wasm.Execution.Core.HostSemantics Nat}
    {s : Silmaril.Wasm.Execution.Core.Store Nat} (hs : GlobalsNamed s) {m : Module}
    {xas : List Silmaril.Wasm.Execution.Core.ExternAddr}
    {C : Silmaril.Wasm.Execution.Core.Config Nat}
    (h : Silmaril.Wasm.V2.Execution.Once.CoreInstantiateOnce P host s m xas C) :
    ∃ C', Silmaril.Wasm.Execution.Core.Instantiate P host s m xas C' ∧
      ∀ P' : Profile, Silmaril.Wasm.Execution.Core.behavioursOf P' noHostC C' =
        Silmaril.Wasm.Execution.Core.behavioursOf P' noHostC C :=
  Silmaril.Proofs.Wasm.Models.V2CoreSpec.once_sub_spec hs h

/-- At host-free points, single-allocation observations are spec observations. -/
theorem coreInstOnce_obs_sub_spec (P : Profile) (S : FeatureSet)
    {s : Silmaril.Wasm.Execution.Core.Store Nat} (hs : GlobalsNamed s) (cm : Module)
    (cxas : List Silmaril.Wasm.Execution.Core.ExternAddr) :
    (coreInstOnce P Nat S).obs (s, noHostC) (cm, cxas) ⊆
      (coreInst P Nat S).obs (s, noHostC) (cm, cxas) :=
  Silmaril.Proofs.Wasm.Models.V2CoreSpec.coreInstObsOnce_sub_spec P hs cm cxas

/-- **The 2.0 instantiation model at host-free points**: `v20instG` (every module with a Core
image) with points restricted to the empty host and a Core store satisfying `GlobalsNamed`. -/
def v20instNH (P : Profile) : WasmModel where
  feats := (v20instG P Nat).feats
  Module := (v20instG P Nat).Module
  Valid := (v20instG P Nat).Valid
  Pt := (v20instG P Nat).Pt
  Call := (v20instG P Nat).Call
  Obs := (v20instG P Nat).Obs
  obs := (v20instG P Nat).obs
  dom p := dom p ∧ p.2 = (fun _ _ _ _ => False) ∧ GlobalsNamed (ptCore p).1

/-- 2.0 instantiation observations at host-free points are spec observations of the image. -/
theorem inst_obs_sub_spec (P : Profile) {p : Pt Nat} (hp : (v20instNH P).dom p)
    (mx : Silmaril.Wasm.V2.Module × List Silmaril.Wasm.V2.Execution.ExternAddr) :
    (v20instNH P).obs p mx ⊆ (coreInst P Nat v20).obs (ptCore p) (instCall mx) := by
  have hpt : ptCore p = ((ptCore p).1, noHostC) := by
    rw [ptCore, hp.2.1, Silmaril.Proofs.Wasm.Models.V2CoreSpec.liftHost_noHost]
  have hsub := inst_obs_sub_once P hp.1 mx
  rw [hpt] at hsub ⊢
  exact hsub.trans (coreInstOnce_obs_sub_spec P v20 hp.2.2 _ _)

/-- **The instantiation embedding into the spec's `$instantiate`, defined globals included**,
at host-free points (direction `sub`). -/
def v20InstEmbNH (P : Profile) : (v20instNH P).Emb (coreInst P Nat v20) where
  mod := modCore
  valid := (v20Emb P Nat).valid
  pt := ptCore
  call := instCall
  readback := some
  dom _ hp := ptCore_dom hp.1
  dir := .sub
  sat _ hp mx := fun b hb => ⟨b, inst_obs_sub_spec P hp mx hb, rfl⟩

theorem v20InstEmbNH_dir (P : Profile) : (v20InstEmbNH P).dir = .sub := rfl

/--
info: 'Silmaril.Wasm.Models.V2CoreSpec.v20InstEmbNH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms v20InstEmbNH

/--
info: 'Silmaril.Wasm.Models.V2CoreSpec.once_sub_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms once_sub_spec

/-- **Single allocation is included in the spec's double allocation with a host blind to
globals and functions**, with equal behaviours (with that host) at every profile. -/
theorem once_sub_spec_host {P : Profile}
    {host : Silmaril.Wasm.Execution.Core.HostSemantics Nat} (hb : GlobalsBlind host)
    {s : Silmaril.Wasm.Execution.Core.Store Nat} (hs : GlobalsNamed s) {m : Module}
    {xas : List Silmaril.Wasm.Execution.Core.ExternAddr}
    {C : Silmaril.Wasm.Execution.Core.Config Nat}
    (h : Silmaril.Wasm.V2.Execution.Once.CoreInstantiateOnce P host s m xas C) :
    ∃ C', Silmaril.Wasm.Execution.Core.Instantiate P host s m xas C' ∧
      ∀ P' : Profile, Silmaril.Wasm.Execution.Core.behavioursOf P' host C' =
        Silmaril.Wasm.Execution.Core.behavioursOf P' host C :=
  Silmaril.Proofs.Wasm.Models.V2CoreSpec.once_sub_spec_host hb hs h

/-- With a host blind to globals, single-allocation observations are spec observations. -/
theorem coreInstOnce_obs_sub_spec_host (P : Profile) (S : FeatureSet)
    {s : Silmaril.Wasm.Execution.Core.Store Nat}
    {host : Silmaril.Wasm.Execution.Core.HostSemantics Nat} (hb : GlobalsBlind host)
    (hs : GlobalsNamed s) (cm : Module) (cxas : List Silmaril.Wasm.Execution.Core.ExternAddr) :
    (coreInstOnce P Nat S).obs (s, host) (cm, cxas) ⊆ (coreInst P Nat S).obs (s, host) (cm, cxas) :=
  Silmaril.Proofs.Wasm.Models.V2CoreSpec.coreInstObsOnce_sub_spec_host P hb hs cm cxas

/-- The empty host is blind to globals. -/
theorem noHostC_blind {H : Type} : GlobalsBlind (noHostC : Silmaril.Wasm.Execution.Core.HostSemantics H) :=
  Silmaril.Proofs.Wasm.Models.V2CoreSpec.noHostC_blind

/-- Hosts that leave the store unchanged are blind to globals. -/
theorem pureHost_blind {H : Type}
    (F : H → List Silmaril.Wasm.Execution.Core.Val → Silmaril.Wasm.Execution.Core.Result → Prop)
    (G : H → List Silmaril.Wasm.Execution.Core.Val → Prop) : GlobalsBlind (pureHost F G) :=
  Silmaril.Proofs.Wasm.Models.V2CoreSpec.pureHost_blind F G

/-- **`GlobalsNamed` does not follow from the 2.0 domain.** -/
theorem dom_not_globalsNamed : ∃ p : Pt Nat, dom p ∧ ¬ GlobalsNamed (ptCore p).1 :=
  Silmaril.Proofs.Wasm.Models.V2CoreSpec.dom_not_globalsNamed

/-- On the 2.0 domain, `GlobalsNamed` of the Core point is `GlobalsNamedV` of the 2.0 store. -/
theorem dom_globalsNamed_iff {H : Type} {p : Pt H} (hp : dom p) :
    GlobalsNamed (ptCore p).1 ↔ GlobalsNamedV p.1 :=
  Silmaril.Proofs.Wasm.Models.V2CoreSpec.dom_globalsNamed_iff hp

/--
info: 'Silmaril.Wasm.Models.V2CoreSpec.once_sub_spec_host' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms once_sub_spec_host

/--
info: 'Silmaril.Wasm.Models.V2CoreSpec.dom_not_globalsNamed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dom_not_globalsNamed

/--
info: 'Silmaril.Wasm.Models.V2CoreSpec.dom_globalsNamed_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dom_globalsNamed_iff

/-! ## hosts induced from 2.0 hosts -/

/-- **The induced Core host commutes with the Core embeddings on image targets.** -/
theorem hostEmbR_liftHost {H : Type} {src : VHost H} (hv : HostEmbV src) :
    Silmaril.Proofs.Wasm.Game.SpecGlobals.HostEmbR GImg (liftHost src) :=
  Silmaril.Proofs.Wasm.Models.V2CoreSpec.hostEmbR_liftHost hv

/-- A 2.0 host blind to globals and functions commutes with the 2.0 embeddings. -/
theorem hostEmbV_blind {H : Type} {src : VHost H} (hb : GlobalsBlindV src) : HostEmbV src :=
  Silmaril.Proofs.Wasm.Models.V2CoreSpec.hostEmbV_blind hb

/-- Store-preserving 2.0 hosts are blind to globals and functions. -/
theorem pureHostV_blind {H : Type}
    (F : H → List Silmaril.Wasm.V2.Execution.Val → Silmaril.Wasm.V2.Execution.Result → Prop)
    (G : H → List Silmaril.Wasm.V2.Execution.Val → Prop) :
    GlobalsBlindV (pureHostV F G) :=
  Silmaril.Proofs.Wasm.Models.V2CoreSpec.pureHostV_blind F G

/-- **The 2.0 instantiation model at points with hosts commuting with the 2.0 embeddings.** -/
def v20instH (P : Profile) : WasmModel where
  feats := (v20instG P Nat).feats
  Module := (v20instG P Nat).Module
  Valid := (v20instG P Nat).Valid
  Pt := (v20instG P Nat).Pt
  Call := (v20instG P Nat).Call
  Obs := (v20instG P Nat).Obs
  obs := (v20instG P Nat).obs
  dom p := dom p ∧ HostEmbV p.2 ∧ GlobalsNamed (ptCore p).1 ∧ SpecGlobalsImg (ptCore p).1

/-- 2.0 instantiation observations at points with hosts commuting with the 2.0 embeddings are
spec observations of the image. -/
theorem inst_obs_sub_spec_H (P : Profile) {p : Pt Nat} (hp : dom p) (hv : HostEmbV p.2)
    (hs : GlobalsNamed (ptCore p).1) (himg : SpecGlobalsImg (ptCore p).1)
    (mx : Silmaril.Wasm.V2.Module × List Silmaril.Wasm.V2.Execution.ExternAddr) :
    (v20instG P Nat).obs p mx ⊆ (coreInst P Nat v20).obs (ptCore p) (instCall mx) := by
  rintro b ⟨hsome, hb⟩
  obtain ⟨cm, hcm⟩ := Option.isSome_iff_exists.mp hsome
  have e : modCore mx.1 = cm := by simp [modCore, hcm]
  simp only [instCall, e]
  exact Silmaril.Proofs.Wasm.Models.V2CoreSpec.instObs_sub_spec_hostR P hp hv hs himg hcm mx.2 hb

/-- **The instantiation embedding into the spec's `$instantiate` with hosts** (direction `sub`):
defined globals included, at points whose 2.0 host commutes with the 2.0 embeddings. -/
def v20InstEmbH (P : Profile) : (v20instH P).Emb (coreInst P Nat v20) where
  mod := modCore
  valid := (v20Emb P Nat).valid
  pt := ptCore
  call := instCall
  readback := some
  dom _ hp := ptCore_dom hp.1
  dir := .sub
  sat _ hp mx := fun b hb =>
    ⟨b, inst_obs_sub_spec_H P hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 mx hb, rfl⟩

theorem v20InstEmbH_dir (P : Profile) : (v20InstEmbH P).dir = .sub := rfl

/-- **Frozen target**: at every point of the 2.0 domain, the spec preparation of every valid
2.0 module's image holds only images of 2.0 globals. Expected true: the store's own globals are
images, and the two new copies of the module's globals have closed 2.0 global types and values
of 2.0 constant expressions (`t.const`, `ref.null`, `ref.func`, `global.get` of an image
global). Not proved. -/
def Task.specGlobalsImg : Prop := ∀ p : Pt Nat, dom p → SpecGlobalsImg (ptCore p).1

/-- The 2.0 instantiation model at points with hosts commuting with the 2.0 embeddings, without
the `SpecGlobalsImg` condition (used under `Task.specGlobalsImg`). -/
def v20instHT (P : Profile) : WasmModel where
  feats := (v20instG P Nat).feats
  Module := (v20instG P Nat).Module
  Valid := (v20instG P Nat).Valid
  Pt := (v20instG P Nat).Pt
  Call := (v20instG P Nat).Call
  Obs := (v20instG P Nat).Obs
  obs := (v20instG P Nat).obs
  dom p := dom p ∧ HostEmbV p.2 ∧ GlobalsNamed (ptCore p).1

/-- **Under `Task.specGlobalsImg`, the instantiation embedding with hosts** (direction `sub`). -/
def v20InstEmbHT (hT : Task.specGlobalsImg) (P : Profile) :
    (v20instHT P).Emb (coreInst P Nat v20) where
  mod := modCore
  valid := (v20Emb P Nat).valid
  pt := ptCore
  call := instCall
  readback := some
  dom _ hp := ptCore_dom hp.1
  dir := .sub
  sat p hp mx := fun b hb =>
    ⟨b, inst_obs_sub_spec_H P hp.1 hp.2.1 hp.2.2 (hT p hp.1) mx hb, rfl⟩

/-- The empty 2.0 host commutes with the 2.0 embeddings. -/
theorem hostEmbV_none {H : Type} : HostEmbV (fun _ _ _ _ => False : VHost H) :=
  ⟨fun _ h => h.elim, fun _ h => h.elim⟩

/-- `v20instHT` extends the host-free model `v20instNH`. -/
theorem v20instNH_dom_sub (P : Profile) {p : Pt Nat} (hp : (v20instNH P).dom p) :
    (v20instHT P).dom p := by
  obtain ⟨hd, hh, hs⟩ := hp
  refine ⟨hd, ?_, hs⟩
  rw [hh]
  exact hostEmbV_none

/-- **`v20instHT` has points whose host answers**: the empty 2.0 store with the host that
returns no values on every call. -/
theorem exists_domHT_answers (P : Profile) :
    ∃ p : Pt Nat, (v20instHT P).dom p ∧ ∃ h s vs s' r, p.2 h s vs (.returned s' r) := by
  let src : VHost Nat :=
    pureHostV (fun _ _ r => r = .values []) (fun _ _ => False)
  refine ⟨({}, src), ⟨⟨?_, ?_, ?_, ?_⟩, hostEmbV_blind (pureHostV_blind (H := Nat) _ _), ?_⟩,
    0, {}, [], {}, .values [], Or.inl ⟨_, rfl, rfl⟩⟩
  · simp [Silmaril.Wasm.V2.Execution.StoreWF]
  · rfl
  · rintro h s args s' r (⟨r', -, he⟩ | ⟨hf, -⟩) hwf
    · cases he
      exact ⟨hwf, Silmaril.ListExt.refl _ _⟩
    · exact hf.elim
  · rintro h s args s' r (⟨r', -, he⟩ | ⟨hf, -⟩)
    · cases he
      rfl
    · exact hf.elim
  · intro fi hfi
    simp [ptCore, Silmaril.Wasm.V2.Execution.Store.toCore] at hfi

/--
info: 'Silmaril.Wasm.Models.V2CoreSpec.v20InstEmbH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms v20InstEmbH

/--
info: 'Silmaril.Wasm.Models.V2CoreSpec.hostEmbR_liftHost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hostEmbR_liftHost

/--
info: 'Silmaril.Wasm.Models.V2CoreSpec.exists_domHT_answers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_domHT_answers

end Silmaril.Wasm.Models.V2CoreSpec
