module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkExp
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
# `Silmaril.Proofs.Wasm.Component.Reference.LinkExp` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.LinkExp` that the
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

/-! ## The exporter's run -/

section Run

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Execution.Core (Store Config)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch Rel4)

variable {P : Profile} {c : Simple} {Ie : Silmaril.Wasm.Game.ScalarInstance} {x : SimpleExport}
  {vs : List Silmaril.Wasm.Component.Val}

/-- **The exporter's run in the shared store.** A shared run, renamed by `g`, of the invocation
of export `x` of the exporter's instance `Ie` on the lowered arguments `vs`, where the shared
store relates the exporter's store `π` and the importer's `κ` (`Rel4`, the exporter's function
owned): the run never stops at a callout; a returned run has flat values of the result types,
is a `coreAt` outcome at `π` and a returned call `RetAt` whenever its lift succeeds, `Ie` well
formed after it; a trapped run is the `coreAt` outcome `none`. The relation holds again at the
end, for a new exporter store `π'` (`Rel4.after_p`), with `FnPre`. -/
theorem exp_run [Fact (Sub P IR)] (hI : c.mod.IsInst Ie) (hcore : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat))
    (typed : ValTy.checkList x.ty.params vs = true) {π κ : Store Nat} (hw : Ie.WellFormed π)
    {Op₀ Oc₀ : Own} {ρp ρc : Ren} {Op Oc : Own} (g : CanonHost (E3 P V IR) → Nat)
    {σ : (E3 P V IR).Store (CanonHost (E3 P V IR))}
    (hR : Rel4 Op₀ Oc₀ ρp Op ρc Oc (Store.mapH g σ) π κ)
    (hF : FnPre ({} : Store Nat) (Store.mapH g σ) π) (hO : Op₀.fn (Ie.addrs.getD x.core 0))
    {e : CoreSt (E3 P V IR)}
    (he : Relation.ReflTransGen (CoreStep (E3 P V IR))
      (σ, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) e) :
    ∃ (π' : Store Nat) (ρp' : Ren) (Op' : Own),
      Rel4 Op₀ Oc₀ ρp' Op' ρc Oc (Store.mapH g e.1) π' κ ∧
      FnPre ({} : Store Nat) (Store.mapH g e.1) π' ∧
      (∀ h ys, (E3 P V IR).status e.1 e.2 ≠ .callout h ys) ∧
      (∀ zs, (E3 P V IR).status e.1 e.2 = .returned (.values zs) →
        zs.map (·.type) = ValTy.flatList x.ty.results ∧
        some zs ∈ coreAt P Ie x.core (lowerArgs x.ty.params vs) π ∧
        ∀ ws, liftArgs x.ty.results zs = some ws → RetAt P c Ie x vs π ws π' ∧ Ie.WellFormed π') ∧
      ((E3 P V IR).status e.1 e.2 = .returned .trap →
        none ∈ coreAt P Ie x.core (lowerArgs x.ty.params vs) π) := by
  obtain ⟨nm, hcx⟩ := hcore
  have hk : x.core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcx).1
  have hO' : Op.fn (Ie.addrs.getD x.core 0) := hR.fnp ▸ hO
  have hL₀ := exp_invoke hR.rp hF hO' (lowerArgs x.ty.params vs)
  obtain ⟨ts, htyped, -⟩ := Silmaril.Wasm.Game.ScalarInstance.invoke_typed hw
    (opAt hI hk (exp_hxs hcx typed hk))
  have hrun : Silmaril.Wasm.Game.Reach P (Store.mapH g σ,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) (Store.mapH g e.1, e.2) :=
    reach_mapH g (coreSteps_internalP he)
  obtain ⟨⟨π', t'⟩, ρp', Op', prun, hL, hgr, htc, hs', ht'⟩ :=
    reach_link_back hrun hL₀ hw.storeOk htyped
  have B : ExpBack P c Ie x vs π π' t' (Store.mapH g e.1, e.2) :=
    ⟨hI, ⟨nm, hcx⟩, typed, hw, prun, ⟨ρp', Op', hL⟩, hs', ⟨ts, ht'⟩⟩
  have hcode : ((e.2).config (Store.mapH g e.1)).code = ((e.2).config e.1).code :=
    config_code_mapH g e.1 e.2
  have hrel : PartRel ρp' Op' π' (Store.mapH g e.1) := by
    have h := hL.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store, reloc_empty] at h
  refine ⟨π', ρp', Op', Rel4.after_p hR hrel hgr htc, hL.fn, ?_, ?_, ?_⟩
  · intro h ys hst
    obtain ⟨E, a', h', args', hd⟩ := status_callout hst
    obtain ⟨E', hd'⟩ := decompose?_mapH g hd
    exact B.no_callout (hcode ▸ hd')
  · intro zs hst
    obtain ⟨cvs, hc, hm⟩ := status_values hst
    exact B.values (hcode ▸ hc) hm
  · intro hst
    exact B.trap (hcode ▸ status_trap hst)

/-- **The exporter's half of a link site**: from any shared store related as in `exp_run`, the
exporter's runs on the lowering of lifted arguments never call out and return values of the flat
result types. -/
theorem exp_site_run [Fact (Sub P IR)] (hI : c.mod.IsInst Ie)
    (hcore : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat)) {π κ : Store Nat}
    (hw : Ie.WellFormed π) {Op₀ Oc₀ : Own} {ρp ρc : Ren} {Op Oc : Own}
    (g : CanonHost (E3 P V IR) → Nat) {σ : (E3 P V IR).Store (CanonHost (E3 P V IR))}
    (hR : Rel4 Op₀ Oc₀ ρp Op ρc Oc (Store.mapH g σ) π κ)
    (hF : FnPre ({} : Store Nat) (Store.mapH g σ) π) (hO : Op₀.fn (Ie.addrs.getD x.core 0))
    {ys : List Flat} :
    ∀ ws, liftArgs x.ty.params ys = some ws → ∀ e,
      Relation.ReflTransGen (CoreStep (E3 P V IR))
        (σ, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD x.core 0)
          (lowerArgs x.ty.params ws)) e →
      (∀ h' ys', (E3 P V IR).status e.1 e.2 ≠ .callout h' ys') ∧
      ∀ zs, (E3 P V IR).status e.1 e.2 = .returned (.values zs) →
        zs.map (·.type) = ValTy.flatList x.ty.results := by
  intro ws hws e he
  have typed : ValTy.checkList x.ty.params ws = true :=
    Silmaril.Wasm.Component.checkList_of_liftArgs hws
  obtain ⟨π', ρp', Op', -, -, hco, hval, -⟩ :=
    exp_run (vs := ws) hI hcore typed hw g hR hF hO he
  exact ⟨hco, fun zs hz => (hval zs hz).1⟩

/-- **A link site from the exporter's facts**: a callout of the importer to the trampoline of
the exporter's lifted export `x` (core address `Ie.addrs.getD x.core 0`), at IR types within
the flat arities, from a shared store related as in `exp_run`. -/
theorem linkSite_exp [Fact (Sub P IR)] {σ' : Type} {B : Machine.Config (E3 P V IR) σ'} {y : CoreSt (E3 P V IR)}
    {f : FuncId} {ys : List Flat}
    (hf : ArenaField.funcs.get? B.store f =
      some (.lifted (Ie.addrs.getD x.core 0) (witFt x.ty) {} ⟨1⟩))
    (hpf : floatFreeList x.ty.params = true) (hys : ys.map (·.type) = ValTy.flatList x.ty.params)
    (hmaxp : (ValTy.flatList x.ty.params).length ≤ 16) (hres : x.ty.results.length ≤ 1)
    (hrf : floatFreeList x.ty.results = true) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hI : c.mod.IsInst Ie) (hcore : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat))
    {π κ : Store Nat} (hw : Ie.WellFormed π) {Op₀ Oc₀ : Own} {ρp ρc : Ren} {Op Oc : Own}
    (g : CanonHost (E3 P V IR) → Nat)
    (hR : Rel4 Op₀ Oc₀ ρp Op ρc Oc (Store.mapH g y.1) π κ)
    (hF : FnPre ({} : Store Nat) (Store.mapH g y.1) π) (hO : Op₀.fn (Ie.addrs.getD x.core 0)) :
    LinkSite B y (.lowered f (witFt x.ty) {} ⟨2⟩) ys :=
  ⟨⟨f, Ie.addrs.getD x.core 0, x.ty, rfl, hf, hpf, hys, hmaxp, hres, hrf, hmaxr,
    exp_site_run hI hcore hw g hR hF hO⟩⟩

end Run

end Silmaril.Proofs.Wasm.Component.Param.Core3R
