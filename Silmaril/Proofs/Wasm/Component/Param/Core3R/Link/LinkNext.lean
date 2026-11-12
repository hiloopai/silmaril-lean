module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkNext
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallKI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallPhaseI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallPhaseKI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.FloatPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Inst
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpDefs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLink
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLinkCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLinkDefs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLinkNames
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstNest
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkCallout
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkExp
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkPlay
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkSeg
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkSegs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqBase
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqCall
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Seq
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Sound
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.SoundSeqI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.LinkNext` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.LinkNext` that the
soundness of linked components (`linked2_sound`, `linked2_sound_seq`) uses and whose statements
mention the engine `core3R P V IR`, with `core3R P V IR` replaced by `core3R P V IR` (Core 3.0 with
validity `V` and an internal step `IR` contained in `InternalP P`, `Core3R.Sub`). The other
declarations of that module are engine-generic and reused from it. Proofs are unchanged except
where a core step of the machine is read as an `InternalP P` step (through `Sub P IR`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Proofs.Wasm.Component.Reference

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst Config)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload sigN)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Rel4)

variable {P : Profile}

/-! ## The invariant between calls -/

/-- **The invariant between linked calls** at the shared core store `cs`, the importer's store
`u` and the exporter's `π`: the ownerships are those of `rel4_init` at the stores `s₀`, `u₀`
after instantiation. -/
structure LReady (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (l : Linked2) (Ie Ii : Silmaril.Wasm.Game.ScalarInstance)
    (s₀ u₀ : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P V IR))))
    (cs : Store (CanonHost (E3 P V IR))) (u π : Store Nat) : Prop where
  rel : ∃ ρp Op ρc Oc, Rel4 (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) ρp Op ρc Oc
    (Store.mapH (gL P V IR l) cs) π (reloc s₀ u)
  fnE : FnPre ({} : Store Nat) (Store.mapH (gL P V IR l) cs) π
  fnC : FnPre s₀ (Store.mapH (gL P V IR l) cs) u
  wfE : Ie.WellFormed π
  wfI : Ii.WellFormed u
  funcs : cs.funcs = F₀
  ufuncs : u.funcs = u₀.funcs
  good : SGoodSt (ownOf u₀).fn u

section Ready

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ u π : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P V IR)))}

/-- **The invariant at the importer's export call**, from the invariant between calls: the
shared thread invokes the relocated address of the export question `f` on flat arguments. -/
theorem linv_ready {y : CoreSt (E3 P V IR)} (hR : LReady P V IR l Ie Ii s₀ u₀ F₀ y.1 u π) {f : Ii.F.Op}
    {xs : List Flat} (hxs : f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat)
    (hth : y.2 = Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (s₀.funcs.length + Ii.addr f.1) xs) :
    LInv P V IR l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y (u, Ii.initThread f) π := by
  obtain ⟨ρp, Op, ρc, Oc, hR4⟩ := hR.rel
  obtain ⟨fi, hfi, -⟩ := hR.wfI.export_type f.1
  have ha : Ii.addr f.1 < u.funcs.length := (List.getElem?_eq_some_iff.mp hfi).1
  have ha₀ : Ii.addr f.1 < u₀.funcs.length := hR.ufuncs ▸ ha
  have hvs : ∀ v ∈ f.2.1, ∀ r, v ≠ .ref r := hxs ▸ ofFlat_scalar xs
  have hO : Oc.fn (s₀.funcs.length + Ii.addr f.1) := by
    rw [hR4.fnc]
    exact ⟨Nat.le_add_right _ _, by simpa [ownOf] using ha₀⟩
  have hg : SplitGood (Silmaril.Wasm.Execution.Core.invoke u (Ii.addr f.1) f.2.1) :=
    (sgood_invoke hR.good (show (ownOf u₀).fn (Ii.addr f.1) from ha₀)
      (fun _ => goodVal_of_hasVal f.2.2)).splitGood
  have hL := linkSt_invoke hR4.rc hR.fnC ha hO hvs hg
  have hshared : (Store.mapH (gL P V IR l) y.1, y.2) = (Store.mapH (gL P V IR l) y.1,
      Silmaril.Wasm.SingleThreaded.Thread.pending (s₀.funcs.length + Ii.addr f.1) f.2.1) := by
    rw [hth, hxs]
    rfl
  exact ⟨⟨_, _, _, _, hshared ▸ hL, hR4⟩, hR.fnE, hR.wfE, hR.funcs, .refl⟩

/-- **The invariant after instantiation**: the shared core store renames under `gL` to the
exporter's store `s₀` followed by the importer's `u₀`, relocated, both good. -/
theorem lready_init {cs : Store (CanonHost (E3 P V IR))} (hg₀ : StoreGood s₀) (hgu : StoreGood u₀)
    (hy : Store.mapH (gL P V IR l) cs = reloc s₀ u₀) (hF : cs.funcs = F₀) (hwe : Ie.WellFormed s₀)
    (hwi : Ii.WellFormed u₀) : LReady P V IR l Ie Ii s₀ u₀ F₀ cs u₀ s₀ where
  rel := by
    rw [hy]
    exact ⟨_, _, _, _, rel4_init hg₀ hgu⟩
  fnE := hy ▸ fnPre_prefix s₀ u₀
  fnC := hy ▸ fnPre_refl s₀ u₀
  wfE := hwe
  wfI := hwi
  funcs := hF
  ufuncs := rfl
  good := sgoodSt_of_storeGood hgu

/-- **The invariant between calls from the invariant along a call**: at any point of a call
started from `LReady` at the part's store `u`, the shared store, the part's store and the
exporter's store satisfy `LReady`. -/
theorem lready_after {cs : Store (CanonHost (E3 P V IR))} (hR : LReady P V IR l Ie Ii s₀ u₀ F₀ cs u π)
    {f : Ii.F.Op} {y : CoreSt (E3 P V IR)}
    {x : Store Nat × Silmaril.Wasm.SingleThreaded.Thread} {π' : Store Nat}
    (hI : LInv P V IR l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x π') :
    LReady P V IR l Ie Ii s₀ u₀ F₀ y.1 x.1 π' := by
  obtain ⟨ρp, Op, ρc, Oc, hL, hR4⟩ := hI.rel
  have hx1 : (x.2.config x.1).store = x.1 := Silmaril.Wasm.SingleThreaded.Thread.config_store _ _
  obtain ⟨ts, hg₀⟩ := SEnvTyping.good_invoke hR.wfI f
  have hg := SEnvTyping.good_ssteps (P := P) hR.wfI (valEnv_throwsBelow Ii _)
    (x := (_, ())) (y := (x.2.config x.1, ())) hg₀ hI.run
  have hs : Silmaril.Wasm.Execution.Core.StoreOk x.1 := by
    have h := Silmaril.Wasm.SingleThreaded.ConfigOk.storeOk hg.ok
    rwa [hx1] at h
  have hfx : x.1.funcs = u.funcs := hx1 ▸ hg.inv.funcs
  obtain ⟨fi, hfi, -⟩ := hR.wfI.export_type f.1
  have ha₀ : (ownOf u₀).fn (Ii.addr f.1) := by
    have ha : Ii.addr f.1 < u.funcs.length := (List.getElem?_eq_some_iff.mp hfi).1
    show Ii.addr f.1 < u₀.funcs.length
    exact hR.ufuncs ▸ ha
  have hsg := sgood_ssteps (P := P) (x := (_, ())) (y := (x.2.config x.1, ())) hI.run
    (sgood_invoke hR.good ha₀ (fun _ => goodVal_of_hasVal f.2.2))
  refine ⟨⟨ρp, Op, ρc, Oc, hR4⟩, hI.fnE, hL.fn, hI.wf, wellFormed_of_funcs' hR.wfI hs hfx,
    hI.funcs, hfx.trans hR.ufuncs, hx1 ▸ hsg.st⟩

end Ready

end Silmaril.Proofs.Wasm.Component.Param.Core3R
