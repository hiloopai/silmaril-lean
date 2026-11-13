module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkPlay
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
# `Silmaril.Proofs.Wasm.Component.Reference.LinkPlay` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.LinkPlay` that the
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
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload sigN)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Rel4)

variable {P : Profile} {σ : Type}

section Ends

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ π₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P V IR)))} {B : Machine.Config (E3 P V IR) σ} {Op₀ Oc₀ : Own}
  {f : Ii.F.Op} {y₀ : CoreSt (E3 P V IR)}

/-- **A segmented run to a result is a play**: when the part's thread at every point satisfying
`LInv` at the end `y` is at a result `r` with `Φ r`, the run is a play answering `r`. -/
theorem lplay_result [Fact (Sub P IR)] (S : LStat P V IR l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P V IR l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y₀ (u₀, Ii.initThread f) π₀)
    {recs : List (LRec P V IR)} {y : CoreSt (E3 P V IR)} (hseg : LSeg B y₀ recs y)
    {Φ : Silmaril.Wasm.Execution.Core.Result → Prop}
    (hres : ∀ x π, LInv P V IR l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π →
      ∃ r, Silmaril.Wasm.Game.ResultAt x.1 x.2 r ∧ Φ r) :
    ∃ (w : Ii.F.Ar f) (r : Silmaril.Wasm.Execution.Core.Result), LPlay P l Ie Ii u₀ π₀ f w ∧
      Φ r ∧ Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) r = some w := by
  obtain ⟨⟨zs, zt⟩, π', rounds, dss, hIz, hrel, hexp, hpath⟩ := lseg_path S hseg hI
  obtain ⟨r, hr, hΦ⟩ := hres _ _ hIz
  obtain ⟨w, hw, -⟩ := Silmaril.Wasm.Game.ScalarInstance.sanswer_of_run S.impWf
    (valEnv_throwsBelow Ii _) hIz.run hr
  have hp := hpath [.inr (.ans f w)] (.idle zs) (fun _ _ hr' => .cons (.oret hr' hr hw) (.nil _))
  have hrun := hexp.run (.nil π')
  rw [List.append_nil] at hrun
  exact ⟨w, r, ⟨rounds, _, dss, .cons (.call u₀ f) hp, hrel, hrun⟩, hΦ, hw⟩

/-- **A returned activation is a play** answering the part's values, whose flat view is the
shared thread's. -/
theorem lplay_values [Fact (Sub P IR)] (S : LStat P V IR l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P V IR l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y₀ (u₀, Ii.initThread f) π₀)
    {recs : List (LRec P V IR)} {y : CoreSt (E3 P V IR)} (hseg : LSeg B y₀ recs y) {zs : List Flat}
    (hst : (E3 P V IR).status y.1 y.2 = .returned (.values zs)) :
    ∃ (w : Ii.F.Ar f) (cvs : List Silmaril.Wasm.Execution.Core.Val),
      LPlay P l Ie Ii u₀ π₀ f w ∧ cvs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some zs ∧
      Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) (.values cvs) = some w := by
  obtain ⟨cvs, hcode, hm⟩ := status_values hst
  have hres : ∀ x π, LInv P V IR l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π → ∃ r,
      Silmaril.Wasm.Game.ResultAt x.1 x.2 r ∧ r = .values cvs := by
    intro x π hIx
    obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hIx.rel
    obtain ⟨ts, hs, ht⟩ := hIx.typed S
    have hc : (y.2.config (Store.mapH (gL P V IR l) y.1)).code = Silmaril.Wasm.Execution.Core.vals cvs :=
      (config_code_mapH (gL P V IR l) y.1 y.2).trans hcode
    obtain ⟨vs, hv, hvm⟩ := values_back P hL hs ht hc
    have hm' : (vs.map (linkMap s₀ ρc).val).mapM Silmaril.Wasm.SingleThreaded.toFlat? = some zs := by
      rw [hvm]
      exact hm
    have hid := map_val_of_mapM _ hm'
    have hvs : vs = cvs := hid.symm.trans hvm
    exact ⟨.values cvs, hvs ▸ hv, rfl⟩
  obtain ⟨w, r, hP, rfl, hw⟩ := lplay_result S hI hseg hres
  exact ⟨w, cvs, hP, hm, hw⟩

/-- **A trapped activation is a play** answering a trap: its lifted answer is `none`. -/
theorem lplay_trap [Fact (Sub P IR)] (S : LStat P V IR l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P V IR l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y₀ (u₀, Ii.initThread f) π₀)
    {recs : List (LRec P V IR)} {y : CoreSt (E3 P V IR)} (hseg : LSeg B y₀ recs y)
    (hst : (E3 P V IR).status y.1 y.2 = .returned .trap) :
    ∃ w : Ii.F.Ar f, LPlay P l Ie Ii u₀ π₀ f w ∧ ∀ x : SimpleExport,
      (answerPayload w).bind (Silmaril.Wasm.Component.Adapter.up (.lift x.ty)) = none := by
  have hres : ∀ x π, LInv P V IR l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π → ∃ r,
      Silmaril.Wasm.Game.ResultAt x.1 x.2 r ∧ r = .trap := by
    intro x π hIx
    obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hIx.rel
    obtain ⟨ts, hs, ht⟩ := hIx.typed S
    rcases status_trap hst with hc | ⟨a, hc⟩
    · exact ⟨.trap, trap_back P hL hs ht ((config_code_mapH (gL P V IR l) y.1 y.2).trans hc), rfl⟩
    · exact (throwing_back P hL hs ht ((config_code_mapH (gL P V IR l) y.1 y.2).trans hc)).elim
  obtain ⟨w, r, hP, rfl, hw⟩ := lplay_result S hI hseg hres
  exact ⟨w, hP, fun _ => lifted_trap (fun _ h => by cases h) hw⟩

/-- **A failing nested call is a component import call answered by a trap**: arguments that do
not lift make no component call (`ImpRel` with `[]`); otherwise the exporter's run from the
shared store traps or returns results that do not lift, a trap of its specification at its
current store (`ExpRun.trap`). -/
theorem expRun_fail [Fact (Sub P IR)] (S : LStat P V IR l Ie Ii u₀ F₀ B Op₀) {y : CoreSt (E3 P V IR)}
    {x : Store Nat × Silmaril.Wasm.SingleThreaded.Thread} {π : Store Nat}
    (hI : LInv P V IR l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π) {e : Ii.E.Op} {k w : Nat} {nm : String}
    {xe : SimpleExport} (hk : l.imp.imports[k]? = some (nm, xe.ty)) (hek : e.1.val = k)
    (hw : l.wire[k]? = some w) (hxe : l.exp.exports[w]? = some xe) {ys : List Flat}
    (hys : e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys)
    (hfail : liftArgs xe.ty.params ys = none ∨
      ∃ ws ev, liftArgs xe.ty.params ys = some ws ∧
        Relation.ReflTransGen (CoreStep (E3 P V IR))
          (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
            (lowerArgs xe.ty.params ws)) ev ∧
        ((E3 P V IR).status ev.1 ev.2 = .returned .trap ∨
          ∃ zs, (E3 P V IR).status ev.1 ev.2 = .returned (.values zs) ∧
            liftArgs xe.ty.results zs = none)) :
    ∃ ds, Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii ⟨e, .trap⟩ ds ∧ Linked2.ExpRun P l Ie π ds := by
  have hk' : l.imp.imports[e.1.val]? = some (nm, xe.ty) := hek ▸ hk
  have hkl : e.1.val < l.imp.imports.length := (List.getElem?_eq_some_iff.mp hk').1
  rcases hfail with hl | ⟨ws, ev, hws, hrun, hend⟩
  · refine ⟨[], ⟨nm, xe.ty, none, hk', rfl, ?_⟩, .nil π⟩
    show match liftArgs xe.ty.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) with
      | none => _ | some ws => _
    rw [hys, hl]
    exact ⟨rfl, rfl⟩
  have hmem : xe ∈ l.exp.exports := List.mem_of_getElem? hxe
  have typed : ValTy.checkList xe.ty.params ws = true :=
    Silmaril.Wasm.Component.checkList_of_liftArgs hws
  obtain ⟨ρp, Op, ρc, Oc, -, hR⟩ := hI.rel
  obtain ⟨π₂, ρp₂, Op₂, -, -, -, hval, htr⟩ := exp_run (vs := ws) S.expInst
    (S.expGood.core xe hmem) typed hI.wf (gL P V IR l) hR hI.fnE (S.owned xe hmem) hrun
  have hspec : Outcome.traps ∈ specAt P l.exp Ie xe ws π := by
    unfold specAt
    rw [checkLower_of_check typed]
    rcases hend with htrap | ⟨zs, hzs, hus⟩
    · exact Or.inl ⟨none, htr htrap, rfl⟩
    · exact Or.inl ⟨some zs, (hval zs hzs).2.1, by simp only [liftOutcome, hus]⟩
  have hwl : w < l.exp.exports.length := (List.getElem?_eq_some_iff.mp hxe).1
  have hxw : l.exp.exports[(⟨w, hwl⟩ : Fin l.exp.exports.length)] = xe :=
    (List.getElem?_eq_some_iff.mp hxe).2
  refine ⟨[⟨(⟨e.1.val, hkl⟩, .vals ws), none⟩], ⟨nm, xe.ty, none, hk', rfl, ?_⟩,
    .trap (k := ⟨e.1.val, hkl⟩) ⟨w, hwl⟩ (hek ▸ hw) (hxw ▸ hspec)⟩
  show match liftArgs xe.ty.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) with
    | none => _ | some ws => _
  rw [hys, hws]
  exact ⟨hkl, none, rfl, rfl⟩

/-- **A failing callout at the end of a segmented run is a play** answering a trap: the rounds
of the nested calls, the trap round of the callout, and the trap. -/
theorem lplay_fail [Fact (Sub P IR)] (S : LStat P V IR l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P V IR l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y₀ (u₀, Ii.initThread f) π₀)
    {recs : List (LRec P V IR)} {y : CoreSt (E3 P V IR)} (hseg : LSeg B y₀ recs y) {fid : FuncId}
    {a : (E3 P V IR).FuncAddr} {p : FuncTy} {ys : List Flat}
    (hst : (E3 P V IR).status y.1 y.2 = .callout (.lowered fid (witFt p) {} ⟨2⟩) ys)
    (hf : ArenaField.funcs.get? B.store fid = some (.lifted a (witFt p) {} ⟨1⟩))
    (hp : p.results.length ≤ 1)
    (hfail : liftArgs p.params ys = none ∨
      ∃ ws ev, liftArgs p.params ys = some ws ∧
        Relation.ReflTransGen (CoreStep (E3 P V IR))
          (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) ev ∧
        ((E3 P V IR).status ev.1 ev.2 = .returned .trap ∨
          ∃ zs, (E3 P V IR).status ev.1 ev.2 = .returned (.values zs) ∧
            liftArgs p.results zs = none)) :
    LPlay P l Ie Ii u₀ π₀ f .trap := by
  obtain ⟨⟨zs, zt⟩, π', rounds, dss, hIz, hrel, hexp, hpath⟩ := lseg_path S hseg hI
  obtain ⟨k, nm, p', w, xe, E, a', args, e, heq, hk, hw, hxe, hpx, hdx, hm, he', -⟩ :=
    hIz.callout S hst
  have hfk : fid = l.wireFid k ∧ witFt p = witFt p' := by
    have h' := heq
    simp only [CanonHost.lowered.injEq] at h'
    exact ⟨h'.1, h'.2.1⟩
  have hmi : (nm, p') ∈ l.imp.imports := List.mem_of_getElem? hk
  have hpp : p = xe.ty := (witFt_inj hfk.2 hp (S.arity.2 _ hmi).2.2).trans hpx.symm
  have hfl : ArenaField.funcs.get? B.store fid =
      some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) :=
    hfk.1 ▸ S.lifted k w xe hw hxe
  have ha : a = Ie.addrs.getD xe.core 0 := by
    injection Option.some.inj (hf.symm.trans hfl)
  subst hpp ha
  have hek : e.1.val = k ∧ e.2.1 = args := ifaceOp?_some he'
  have hys : e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys :=
    hek.2 ▸ filterMap_of_mapM hm
  obtain ⟨ds, hds, hrun⟩ := expRun_fail S hIz (hpx ▸ hk) hek.1 hw hxe hys hfail
  have hP := hpath _ _ (path_trap_round hdx he')
  have hmoves : (.inr (.ask f) :: callMoves (rounds ++ [⟨e, .trap⟩]) ++ [.inr (.ans f .trap)] :
      List (Silmaril.Games.Move Ii.E Ii.F)) = .inr (.ask f) :: (callMoves rounds ++
        [.inl (.ask e), .inl (.ans e .trap), .inr (.ans f .trap)]) := by
    rw [callMoves_append, List.cons_append, List.append_assoc]
    rfl
  have hP' : Ii.Path P (.idle u₀) (.inr (.ask f) :: callMoves (rounds ++ [⟨e, .trap⟩]) ++
      [.inr (.ans f .trap)]) (.idle zs) := by
    rw [hmoves]
    exact .cons (.call u₀ f) hP
  refine ⟨rounds ++ [⟨e, .trap⟩], _, dss ++ [ds], hP',
    List.rel_append hrel (.cons hds .nil), ?_⟩
  rw [List.flatten_append, List.flatten_singleton]
  exact hexp.run hrun

end Ends

/-! ## The start -/

section Start

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P V IR)))} {f : Ii.F.Op}

/-- The exporter's core store has no host functions. -/
theorem hostsSat_cse {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cse : (E3 P V IR).Store (CanonHost (E3 P V IR))} {cie : (E3 P V IR).Inst}
    (hFe : CoreFacts (Pf := P) (V := V) (IR := IR) c I cse cie) :
    HostsSat (fun _ => False) (cse : Store (CanonHost (E3 P V IR))) :=
  hostsSat_prepareE (fun a fi _ ha _ => by
    change (({} : Store (CanonHost (E3 P V IR))).funcs)[a]? = some fi at ha
    simp at ha) hFe.prepare

/-- **The shared core store after instantiation, renamed**: under `gL` it is the exporter
instance's store followed by the importer instance's, relocated (`instBehavioursL_inst`). -/
theorem linkStore_mapH {l : Linked2} (hn : l.WireNodup) (hw : l.WireTy)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {cse : (E3 P V IR).Store (CanonHost (E3 P V IR))}
    {cie : (E3 P V IR).Inst} (hFe : CoreFacts (Pf := P) (V := V) (IR := IR) l.exp Ie cse cie)
    {r : Store (CanonHost (E3 P V IR) × Nat)} (hrs : Store.mapH Prod.snd r = Ii.store)
    (hh : HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
      h = (.lowered (l.wireFid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r) :
    Store.mapH (gL P V IR l) (reloc cse (Store.mapH Prod.fst r)) = reloc Ie.store Ii.store := by
  have hcse := hostsSat_cse hFe
  have he : Store.mapH (gL P V IR l) cse = Ie.store :=
    (mapH_congr_hosts hcse (g' := fun _ => 0) fun _ h => h.elim).trans hFe.store
  have hi : Store.mapH (gL P V IR l) (Store.mapH Prod.fst r) = Ii.store := by
    rw [mapH_mapH, ← hrs]
    refine mapH_congr_hosts hh ?_
    rintro _ ⟨k, hk, rfl⟩
    show l.trampIdxL (E := E3 P V IR) (.lowered (l.wireFid k) (witFt l.imp.imports[k].2) {} ⟨2⟩) = k
    exact trampIdxL_wireFid hn (hw.length ▸ hk) _ _ _
  have e := mapH_reloc (gL P V IR l) (cse : Store (CanonHost (E3 P V IR))) (Store.mapH Prod.fst r)
  rw [he, hi] at e
  exact e

/-- A function of the relocated suffix is the shifted, renamed function of the part. -/
theorem reloc_suffix_get {H : Type} {cs : Store (CanonHost (E3 P V IR))} {r : Store H}
    {g : H → CanonHost (E3 P V IR)} {A : Nat} {fi : FuncInst (CanonHost (E3 P V IR))}
    (hge : cs.funcs.length ≤ A) (hA : (reloc cs (Store.mapH g r)).funcs[A]? = some fi) :
    ∃ fr, r.funcs[A - cs.funcs.length]? = some fr ∧ (sh cs).finst (FuncInst.mapH g fr) = fi := by
  have h₁ : ((r.funcs[A - cs.funcs.length]?).map (FuncInst.mapH g)).map (sh cs).finst =
      some fi := by
    rw [← Store.mapH_funcs_getElem?, ← List.getElem?_map, ← List.getElem?_append_right hge]
    exact hA
  cases e : r.funcs[A - cs.funcs.length]? with
  | none => simp [e] at h₁
  | some fr => exact ⟨fr, rfl, by simpa [e] using h₁⟩

/-- **The host functions of the shared core store are the importer's trampolines.** -/
theorem tramp_linkStore {l : Linked2} {cs : Store (CanonHost (E3 P V IR))}
    (hcse : HostsSat (fun _ => False) cs) {r : Store (CanonHost (E3 P V IR) × Nat)}
    (hh : HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
      h = (.lowered (l.wireFid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r) :
    ∀ (A : Nat) (fi : FuncInst (CanonHost (E3 P V IR))) (h : CanonHost (E3 P V IR)),
      (reloc cs (Store.mapH Prod.fst r)).funcs[A]? = some fi →
      fi.code = .host h →
      ∃ k nm p, h = .lowered (l.wireFid k) (witFt p) {} ⟨2⟩ ∧ l.imp.imports[k]? = some (nm, p) := by
  intro A fi h hA hc
  rcases Nat.lt_or_ge A cs.funcs.length with hlt | hge
  · have h₁ : cs.funcs[A]? = some fi :=
      (List.getElem?_append_left (l₂ := (Store.mapH Prod.fst r).funcs.map (sh cs).finst)
        hlt).symm.trans hA
    exact (hcse A fi h h₁ hc).elim
  obtain ⟨fr, hfr, hfe⟩ := reloc_suffix_get hge hA
  have hcf : (FuncInst.mapH Prod.fst fr).code = .host h := by
    rw [← hc, ← hfe]
    rfl
  obtain ⟨hk, hcode, hh'⟩ := mapH_fst_host hcf
  obtain ⟨k, hkl, hke⟩ := hh _ fr hk hfr hcode
  have hkh : h = .lowered (l.wireFid k) (witFt l.imp.imports[k].2) {} ⟨2⟩ := by
    rw [← hh', hke]
  exact ⟨k, l.imp.imports[k].1, l.imp.imports[k].2, hkh, List.getElem?_eq_getElem hkl⟩

/-- The lifted function of the exporter's export `w`, at the front of the component functions. -/
theorem lifted_init {l : Linked2} {Ie : Silmaril.Wasm.Game.ScalarInstance}
    (rest : List (CFuncInst (E3 P V IR))) {k w : Nat} {xe : SimpleExport}
    (hw : l.wire[k]? = some w) (hxe : l.exp.exports[w]? = some xe) :
    (liftedList (Pf := P) (V := V) (IR := IR) (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++ rest)[(l.wireFid k).idx]? =
      some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) := by
  have hwl : w < l.exp.exports.length := (List.getElem?_eq_some_iff.mp hxe).1
  have hidx : (l.wireFid k).idx = w := wire_getD hw
  rw [hidx, List.getElem?_append_left (by simpa [liftedList] using hwl)]
  simp [liftedList, hxe, liftedFt, witFt]

/-- **The static facts of a linked call after instantiation**: from the core facts of the
exporter (`CoreFacts`) and the importer's store `r` of `instBehavioursL_inst`, with the frame's
component functions those of `afterLink`. -/
theorem lstat_init {l : Linked2} (hEg : l.exp.Good) (hIg : l.imp.Good) (hW : l.WireTy)
    (hn : l.WireNodup) (har : l.imp.Arity) (hff : l.imp.FloatFree)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {cse : (E3 P V IR).Store (CanonHost (E3 P V IR))}
    {cie : (E3 P V IR).Inst} (hFe : CoreFacts (Pf := P) (V := V) (IR := IR) l.exp Ie cse cie) (hI : l.imp.mod.IsInst Ii)
    {r : Store (CanonHost (E3 P V IR) × Nat)}
    (hh : HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
      h = (.lowered (l.wireFid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r)
    {B : Machine.Config (E3 P V IR) σ} (rest : List (CFuncInst (E3 P V IR)))
    (hB : B.store.funcs = liftedList (Pf := P) (V := V) (IR := IR) (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++ rest) :
    LStat P V IR l Ie Ii Ii.store (reloc (cse : Store (CanonHost (E3 P V IR))) (Store.mapH Prod.fst r)).funcs
      B (ownOf Ie.store) where
  expGood := hEg
  expInst := hFe.isInst
  impGood := hIg
  impInst := hI
  impWf := hI.1.choose_spec.ok
  wireTy := hW
  nodup := hn
  arity := har
  floats := hff
  tramp := tramp_linkStore (hostsSat_cse hFe) hh
  lifted := fun k w xe hw hxe => by
    simp only [ArenaField.get?, ArenaField.funcs, hB, Arena.get?_eq_getElem?]
    exact lifted_init rest hw hxe
  owned := owned_init hEg hFe.isInst

/-- **The invariant at the importer's export call**: the shared core store renames under
`gL` to the exporter's store `s₀` followed by the importer's `u`, relocated, both good, with the
functions `F₀`; the shared thread invokes the relocated address of the export question `f` on
flat arguments. The part is the pending invocation of `f` from `u`, the exporter's store is
`s₀`, and the ownerships are those of `rel4_init`. -/
theorem linv_init {y : CoreSt (E3 P V IR)} (hg₀ : StoreGood s₀) (hgu : StoreGood u)
    (hy : Store.mapH (gL P V IR l) y.1 = reloc s₀ u) (hF : y.1.funcs = F₀) (hwf : Ie.WellFormed s₀)
    (ha : Ii.addr f.1 < u.funcs.length) {xs : List Flat}
    (hxs : f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat)
    (hth : y.2 = Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (s₀.funcs.length + Ii.addr f.1) xs) :
    LInv P V IR l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u)) f y (u, Ii.initThread f) s₀ := by
  have hR := rel4_init hg₀ hgu
  have hvs : ∀ v ∈ f.2.1, ∀ r, v ≠ .ref r := hxs ▸ ofFlat_scalar xs
  have hO : (shOwn (sh s₀) (ownOf u)).fn (s₀.funcs.length + Ii.addr f.1) :=
    ⟨Nat.le_add_right _ _, by simpa [ownOf] using ha⟩
  have hL := linkSt_invoke hR.rc (fnPre_refl s₀ u) ha hO hvs (splitGood_invoke hgu ha hvs)
  have hshared : (Store.mapH (gL P V IR l) y.1, y.2) = (reloc s₀ u,
      Silmaril.Wasm.SingleThreaded.Thread.pending (s₀.funcs.length + Ii.addr f.1) f.2.1) := by
    rw [hy, hth, hxs]
    rfl
  have hR' : Rel4 (ownOf s₀) (shOwn (sh s₀) (ownOf u)) Ren.id (ownOf s₀) Ren.id
      (shOwn (sh s₀) (ownOf u)) (Store.mapH (gL P V IR l) y.1) s₀ (reloc s₀ u) := by
    rw [hy]
    exact hR
  refine ⟨⟨_, _, _, _, hshared ▸ hL, hR'⟩, hy ▸ fnPre_prefix s₀ u, hwf, hF, ?_⟩
  exact .refl

/-- **The invariant at the importer's export call after instantiation**: the shared core store
of `instBehavioursL_inst`, the shared thread invoking the relocated address of the export
question `f` of `Ii` on flat arguments; the part at the pending invocation from `Ii.store`, the
exporter at `Ie.store`. -/
theorem linv_afterLink {l : Linked2} (hS : l.SplitOk) (hn : l.WireNodup) (hW : l.WireTy)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {cse : (E3 P V IR).Store (CanonHost (E3 P V IR))}
    {cie : (E3 P V IR).Inst} (hFe : CoreFacts (Pf := P) (V := V) (IR := IR) l.exp Ie cse cie) (hI : l.imp.mod.IsInst Ii)
    {r : Store (CanonHost (E3 P V IR) × Nat)} (hrs : Store.mapH Prod.snd r = Ii.store)
    (hh : HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
      h = (.lowered (l.wireFid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r)
    {f : Ii.F.Op} {xs : List Flat} (hxs : f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat) :
    LInv P V IR l Ie Ii Ie.store Ii.store
      (reloc (cse : Store (CanonHost (E3 P V IR))) (Store.mapH Prod.fst r)).funcs (ownOf Ie.store)
      (shOwn (sh Ie.store) (ownOf Ii.store)) f
      (reloc (cse : Store (CanonHost (E3 P V IR))) (Store.mapH Prod.fst r),
        Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.store.funcs.length + Ii.addr f.1) xs)
      (Ii.store, Ii.initThread f) Ie.store := by
  have hwi : Ii.WellFormed Ii.store := hI.1.choose_spec.ok
  have hwe : Ie.WellFormed Ie.store := hFe.isInst.1.choose_spec.ok
  have hg₀ : StoreGood Ie.store := storeGood_inst hS.exp hFe.isInst.1.choose_spec
  have hgu : StoreGood Ii.store := storeGood_inst hS.imp hI.1.choose_spec
  obtain ⟨fi, hfi, -⟩ := hwi.export_type f.1
  exact linv_init hg₀ hgu (linkStore_mapH hn hW hFe hrs hh) rfl hwe
    (List.getElem?_eq_some_iff.mp hfi).1 hxs rfl

end Start

end Silmaril.Proofs.Wasm.Component.Param.Core3R
