module

public import Silmaril.Wasm.Models.V2CoreInstGen.Defs
public import Silmaril.Wasm.Models.V2CoreSpecImg.Thms
import Silmaril.Proofs.Wasm.Models.V2CoreSpecH.Main

/-!
# The instantiation embedding with hosts, at every host type

the earlier `V2CoreSpec.v20InstEmbHT` (and its unconditional form `V2CoreSpecImg.v20InstEmbHU`)
embeds the 2.0 instantiation model with hosts into the spec's Core instantiation model
`coreInst P Nat v20`, at points `Pt Nat`. An earlier step  stated the model at every host type
(`V2CoreInstGen.v20instHTG P H`) but not the embedding. This header lifts it:

* **`specGlobalsImgH`**: `Task.specGlobalsImg` at every host type: at every point `p : Pt H` of
  the 2.0 domain, `SpecGlobalsImg (ptCore p).1`. 's proof never used `Nat`.
* **`instObs_sub_spec_hostRH`**: the earlier `instObs_sub_spec_hostR` at every `H`, without the
  `SpecGlobalsImg` hypothesis. The residue embedding it goes through
  (`SpecGlobals.prepare_residue_emb`) was stated over `Store Nat`; the proof modules of this
  topic re-elaborate it, unchanged, over `Store H`.
* **`v20InstEmbHTG P H : (v20instHTG P H).Emb (coreInst P H v20)`**, direction `sub`, for every
  host type `H`, with no frozen hypothesis. At `H = Nat` it is `v20InstEmbHU P`
  (`v20InstEmbHTG_nat`, by `rfl`). `exists_domHTG_answers`: its domain has points whose host
  answers, at every inhabited `H`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreSpecH

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Atlas Silmaril.Wasm.Models.V2Core
open Silmaril.Wasm.Models.V2CoreSpec Silmaril.Wasm.Models.V2CoreInst Silmaril.Wasm.Models.V2CoreInstGen
open Silmaril.Wasm.Numerics (Profile)

/-- **`Task.specGlobalsImg` at every host type.** -/
theorem specGlobalsImgH {H : Type} (p : Pt H) (hp : dom p) : SpecGlobalsImg (ptCore p).1 :=
  Silmaril.Proofs.Wasm.Models.V2CoreSpecH.specGlobalsImgH p hp

/-- **2.0 instantiation observations are spec observations of the image, at every host type**,
at points whose host commutes with the 2.0 embeddings and whose Core store satisfies
`GlobalsNamed`. -/
theorem inst_obs_sub_spec_HG (P : Profile) {H : Type} {p : Pt H} (hp : (v20instHTG P H).dom p)
    (mx : Silmaril.Wasm.V2.Module × List Silmaril.Wasm.V2.Execution.ExternAddr) :
    (v20instG P H).obs p mx ⊆ (coreInst P H v20).obs (ptCore p) (instCall mx) := by
  rintro b ⟨hsome, hb⟩
  obtain ⟨cm, hcm⟩ := Option.isSome_iff_exists.mp hsome
  have e : modCore mx.1 = cm := by simp [modCore, hcm]
  simp only [instCall, e]
  exact Silmaril.Proofs.Wasm.Models.V2CoreSpecH.instObs_sub_spec_hostRH P hp.1 hp.2.1 hp.2.2 hcm
    mx.2 hb

/-- **The instantiation embedding with hosts, at every host type** (direction `sub`). -/
def v20InstEmbHTG (P : Profile) (H : Type) : (v20instHTG P H).Emb (coreInst P H v20) where
  mod := modCore
  valid := (v20Emb P H).valid
  pt := ptCore
  call := instCall
  readback := some
  dom _ hp := ptCore_dom hp.1
  dir := .sub
  sat _ hp mx := fun b hb => ⟨b, inst_obs_sub_spec_HG P hp mx hb, rfl⟩

theorem v20InstEmbHTG_dir (P : Profile) (H : Type) : (v20InstEmbHTG P H).dir = .sub := rfl

/-- At `H = Nat` the embedding is the earlier `v20InstEmbHU`. -/
theorem v20InstEmbHTG_nat (P : Profile) :
    (v20InstEmbHTG P Nat : (Silmaril.Wasm.Models.V2CoreSpec.v20instHT P).Emb (coreInst P Nat v20)) =
      Silmaril.Wasm.Models.V2CoreSpecImg.v20InstEmbHU P := rfl

/-- **`v20instHTG P H` has points whose host answers**, at every inhabited host type: the empty
2.0 store with the host that returns no values on every call. -/
theorem exists_domHTG_answers (P : Profile) {H : Type} (h₀ : H) :
    ∃ p : Pt H, (v20instHTG P H).dom p ∧ ∃ h s vs s' r, p.2 h s vs (.returned s' r) := by
  let src : VHost H :=
    pureHostV (fun _ _ r => r = .values []) (fun _ _ => False)
  refine ⟨({}, src), ⟨⟨?_, ?_, ?_, ?_⟩, hostEmbV_blind (pureHostV_blind (H := H) _ _), ?_⟩,
    h₀, {}, [], {}, .values [], Or.inl ⟨_, rfl, rfl⟩⟩
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
info: 'Silmaril.Wasm.Models.V2CoreSpecH.v20InstEmbHTG' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms v20InstEmbHTG

/--
info: 'Silmaril.Wasm.Models.V2CoreSpecH.specGlobalsImgH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms specGlobalsImgH

end Silmaril.Wasm.Models.V2CoreSpecH
