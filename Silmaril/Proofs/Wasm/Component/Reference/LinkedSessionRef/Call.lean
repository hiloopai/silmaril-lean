module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.Segs
public import Silmaril.Proofs.Wasm.Component.Reference.LinkSoundSeq
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.Rounds
public import Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.RefSess
public import Silmaril.Wasm.Component.Reference.LinkedSessionRef.Defs

/-!
# The reference side of linked sessions

* `lready_expTrap`: a nested call whose exporter run traps (or returns results that do not lift)
  is a trapped call of the exporter's specification (`TrapAt`) from its store to the store it
  reached, and the invariant between calls (`LReady`) holds at the shared core store of the trap,
  the importer's store at the callout and the exporter's store after the trap;
* `linkCallT`: a trapping linked call between calls (`ReadyL`) is a well-formed session round
  answering `none`: a play of the importer's instance from its store to the store it reached,
  whose component import calls are an `ExpRunT` segment of the exporter, with `LReady` at the
  core store of the trapped configuration. The resolved case is `linkCallK`;
* `sessL_inv`: resumable sessions (`SessCalls`, `resumeCfg` after a trap) from a configuration
  between calls are specification sessions (`Linked2.SessSpec`);
* `linked2_sess_refToSpec`: the sessions of `l.toRef` after instantiation.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Rel4)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## The exporter's returned calls, traps continuing -/

/-- **A returned prefix followed by an `ExpRunT` is an `ExpRunT`.** -/
theorem expSeg_runT {l : Linked2} {I : Silmaril.Wasm.Game.ScalarInstance} {s s' s'' : Store Nat}
    {ds ds' : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
    (h : ExpSeg P l I s ds s') (h' : Linked2.ExpRunT P l I s' ds' s'') :
    Linked2.ExpRunT P l I s (ds ++ ds') s'' := by
  induction h with
  | nil => exact h'
  | ret w hw hr _ ih => exact .ret w hw hr (ih h')

theorem expSeg_toT {l : Linked2} {I : Silmaril.Wasm.Game.ScalarInstance} {s s' : Store Nat}
    {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
    (h : ExpSeg P l I s ds s') : Linked2.ExpRunT P l I s ds s' := by
  simpa only [List.append_nil] using expSeg_runT h (.nil s')

section Trap

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ u π : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B : Machine.Config (E3 P) σ}

/-! ## A nested call that traps -/

/-- **A trapping run of the exporter in a nested call**: from the callout `y` of the importer
(the part at `z`, the exporter at `π'`, `LInv`), the exporter's run on the lowered arguments to a
trap, or to results that do not lift, at `e` is a trapped call (`TrapAt`) of the exporter's
specification from `π'` to some `π₂`, and `LReady` holds at `e.1`, `z.1`, `π₂`. -/
theorem lready_expTrap (S : LStat P l Ie Ii u F₀ B (ownOf s₀))
    {cs : Store (CanonHost (E3 P))} (hR : LReady P l Ie Ii s₀ u₀ F₀ cs u π) {f : Ii.F.Op}
    {y : CoreSt (E3 P)}
    {z : Store Nat × Silmaril.Wasm.SingleThreaded.Thread} {π' : Store Nat}
    (hI : LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y z π')
    {xe : SimpleExport} (hxe : xe ∈ l.exp.exports) {ws : List Silmaril.Wasm.Component.Val}
    (typed : ValTy.checkList xe.ty.params ws = true) {e : CoreSt (E3 P)}
    (he : Relation.ReflTransGen (CoreStep (E3 P))
      (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
        (lowerArgs xe.ty.params ws)) e)
    (hend : (E3 P).status e.1 e.2 = .returned .trap ∨
      ∃ zs, (E3 P).status e.1 e.2 = .returned (.values zs) ∧ liftArgs xe.ty.results zs = none) :
    ∃ π₂, TrapAt P l.exp Ie xe ws π' π₂ ∧ LReady P l Ie Ii s₀ u₀ F₀ e.1 z.1 π₂ := by
  have hR' := lready_after hR hI
  obtain ⟨ρp, Op, ρc, Oc, -, hR4⟩ := hI.rel
  obtain ⟨nm, hcx⟩ := S.expGood.core xe hxe
  have hk : xe.core < l.exp.mod.exports.length := (List.getElem?_eq_some_iff.mp hcx).1
  have hO' : Op.fn (Ie.addrs.getD xe.core 0) := hR4.fnp ▸ S.owned xe hxe
  have hL₀ := exp_invoke hR4.rp hI.fnE hO' (lowerArgs xe.ty.params ws)
  obtain ⟨ts, htyped, -⟩ := Silmaril.Wasm.Game.ScalarInstance.invoke_typed hI.wf
    (opAt S.expInst hk (exp_hxs hcx typed hk))
  have hrun : Silmaril.Wasm.Game.Reach P (Store.mapH (gL P l) y.1,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
        (lowerArgs xe.ty.params ws)) (Store.mapH (gL P l) e.1, e.2) :=
    reach_mapH (gL P l) (coreSteps_internalP he)
  obtain ⟨⟨π₂, t'⟩, ρp', Op', prun, hL, hgr, htc, hs', ht'⟩ :=
    reach_link_back hrun hL₀ hI.wf.storeOk htyped
  have hrel : PartRel ρp' Op' π₂ (Store.mapH (gL P l) e.1) := by
    have h := hL.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store, reloc_empty] at h
  have hcode : ((e.2).config (Store.mapH (gL P l) e.1)).code = ((e.2).config e.1).code :=
    config_code_mapH (gL P l) e.1 e.2
  have htrap : TrapAt P l.exp Ie xe ws π' π₂ := by
    refine ⟨typed, ?_⟩
    rcases hend with hst | ⟨zs, hst, hus⟩
    · rcases status_trap hst with hc | ⟨a, hc⟩
      · exact ⟨t', .trap, prun, trap_back P hL hs' ht' (hcode.trans hc), rfl⟩
      · exact (throwing_back P hL hs' ht' (hcode.trans hc)).elim
    · obtain ⟨cvs, hc, hm⟩ := status_values hst
      obtain ⟨vs', hv', hmap⟩ := values_back P hL hs' ht' (hcode.trans hc)
      have hvv : vs'.map (linkMap ({} : Store Nat) ρp').val = vs' :=
        map_val_flat _ (show (vs'.map (linkMap ({} : Store Nat) ρp').val).mapM
          Silmaril.Wasm.SingleThreaded.toFlat? = some zs by rw [hmap]; exact hm)
      have hcv : vs' = cvs := hvv.symm.trans hmap
      refine ⟨t', .values cvs, prun, hcv ▸ hv', ?_⟩
      simp only [coreRes, hm, liftOutcome, hus]
  have hfe : e.1.funcs = y.1.funcs :=
    reach_funcs' (x := (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (Ie.addrs.getD xe.core 0) (lowerArgs xe.ty.params ws))) (coreSteps_internalP he)
  refine ⟨π₂, htrap, ⟨⟨ρp', Op', ρc, Oc, Rel4.after_p hR4 hrel hgr htc⟩, hL.fn,
    hR'.fnC.congr (mapH_funcs_eq _ hfe) rfl, htrap.wellFormed S.expInst ⟨nm, hcx⟩ hI.wf, hR'.wfI,
    hfe.trans hR'.funcs, hR'.ufuncs, hR'.good⟩⟩

/-- `lplay_result`, with the end: a segmented run to a result is a play of the importer's
instance from `u` to the store of the part's end, where `LInv` holds. -/
theorem lplay_resultT (S : LStat P l Ie Ii u F₀ B (ownOf s₀)) {f : Ii.F.Op} {y₀ : CoreSt (E3 P)}
    (hI : LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y₀ (u, Ii.initThread f)
      π)
    {recs : List (LRec P)} {y : CoreSt (E3 P)} (hseg : LSeg B y₀ recs y)
    {Φ : Silmaril.Wasm.Execution.Core.Result → Prop}
    (hres : ∀ x π', LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x π' →
      ∃ r, Silmaril.Wasm.Game.ResultAt x.1 x.2 r ∧ Φ r) :
    ∃ (w : Ii.F.Ar f) (r : Silmaril.Wasm.Execution.Core.Result) (rounds : List (Round Ii.E))
      (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)))
      (z : Store Nat × Silmaril.Wasm.SingleThreaded.Thread) (π' : Store Nat),
      Ii.Path P (.idle u) (.inr (.ask f) :: callMoves rounds ++ [.inr (.ans f w)]) (.idle z.1) ∧
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) rounds dss ∧ ExpSeg P l Ie π dss.flatten π' ∧
      LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y z π' ∧ Φ r ∧
      Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) r = some w := by
  obtain ⟨⟨zs, zt⟩, π', rounds, dss, hIz, hrel, hexp, hpath⟩ := lseg_path S hseg hI
  obtain ⟨r, hr, hΦ⟩ := hres _ _ hIz
  obtain ⟨w, hw, -⟩ := Silmaril.Wasm.Game.ScalarInstance.sanswer_of_run S.impWf
    (valEnv_throwsBelow Ii _) hIz.run hr
  have hp := hpath [.inr (.ans f w)] (.idle zs) (fun _ _ hr' => .cons (.oret hr' hr hw) (.nil _))
  exact ⟨w, r, rounds, dss, (zs, zt), π', .cons (.call u f) hp, hrel, hexp, hIz, hΦ, hw⟩

end Trap

/-! ## A trapping linked call -/

section Call

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) σ}
  {fs : List (CFuncInst (core3P P))}

/-- **A trapping linked call between calls is a session round answering `none`**: a well-formed
round of the importer (export `j` on `vs`) whose instance play runs from the importer's store `u`
to `u'`, whose component import calls are an `ExpRunT` segment of the exporter from `π` to `π'`,
and `LReady` holds at the core store of the trapped configuration, `u'` and `π'`. -/
theorem linkCallT (S₀ : LStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOk l Ii s₀ fs) {cs : (core3P P).Store (CanonHost (core3P P))}
    {ιe ιi : InstState} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k : Nat} {u π : Store Nat}
    (R : ReadyL P l Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k) (j : Fin l.imp.exports.length)
    {vs : List Silmaril.Wasm.Component.Val}
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    {m' : Machine.Config (E3 P) σ}
    (hcalls : Calls prof (fun _ _ => false) (DI P impl) (readyCfgL cs ιe ιi fs G ST h₀) ⟨k⟩
      ⟨l.exp.exports.length + j⟩ (vs.map toRefVal) m' .trap) :
    ∃ (d : Linked2.SessRound l Ii) (u' π' : Store Nat), d.j = j ∧ d.vs = vs ∧ d.Ok ∧
      d.ans = none ∧ Ii.Path P (.idle u) d.instMoves (.idle u') ∧
      Linked2.ExpRunT P l Ie π d.dss.flatten π' ∧ LReady P l Ie Ii s₀ u₀ F₀ m'.core u' π' := by
  have hx : l.imp.exports[j] ∈ l.imp.exports := List.getElem_mem j.isLt
  obtain ⟨nm, hcore⟩ := S₀.impGood.core _ hx
  have hk : l.imp.exports[j].core < l.imp.mod.exports.length :=
    (List.getElem?_eq_some_iff.mp hcore).1
  have hflat : l.imp.mod.exports[l.imp.exports[j].core] = (nm, l.imp.exports[j].ty.flat) :=
    (List.getElem?_eq_some_iff.mp hcore).2
  have hxs : (lowerArgs l.imp.exports[j].ty.params vs).map (·.type) =
      l.imp.mod.exports[l.imp.exports[j].core].2.params := by
    rw [hflat]
    exact lowerList_types _ _ hvs
  obtain ⟨f, hf₁, hf₂, hft⟩ := typedCallI S₀.impInst hk hxs
  have hft' : Ii.exports.get f.1 = fnOf l.imp.exports[j].ty.flat := by rw [hft, hflat]
  obtain ⟨hmax, hmaxr, hres⟩ := S₀.arity.1 _ hx
  obtain ⟨hpf, hrf⟩ := S₀.floats.1 _ hx
  have ha : Ii.addrs.getD l.imp.exports[j].core 0 = Ii.addr f.1 := by
    rw [← hf₁]
    rfl
  have hfj : fs[l.exp.exports.length + j]? = some (.lifted (s₀.funcs.length + Ii.addr f.1)
      (liftedFt l.imp.exports[j]) {} ⟨2⟩) := ha ▸ hfs j
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atLKT (impl := impl) prof cs ιe ιi fs G
    ST h₀ k (l.exp.exports.length + j) _ l.imp.exports[j] vs hpf hvs hmax hres hmaxr hrf R.thI
    R.leave hfj
  have S : LStat P l Ie Ii u F₀ M₀ (ownOf s₀) := S₀.move R.inv.wfI (hat.funcs.trans hB₀.symm)
  have hI₀ : LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1)
        (lowerArgs l.imp.exports[j].ty.params vs)) (u, Ii.initThread f) π :=
    linv_ready R.inv hf₂ rfl
  have hck : checkLower l.imp.exports[j].ty.params vs =
      some (lowerArgs l.imp.exports[j].ty.params vs) := by
    simp only [checkLower, hvs, ↓reduceIte]
  obtain ⟨tr, hs, hev, -, ho⟩ := hcalls
  obtain ⟨m₂, st, r₁⟩ := Steps.cons_iff.mp hs
  have r₀ : Steps prof (fun _ _ => false) (DI P impl) (invokedAtL cs ιe ιi fs G ST h₀ k
      (l.exp.exports.length + j) (vs.map toRefVal)) tr m' := invoke_invL st ▸ r₁
  rcases hpre.inv r₀ with hl | ⟨tr'', e, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  have r'' : Steps prof (fun _ _ => false) (DI P impl) (coreCfg (extN M₀ ιe [] M₀.conts) th K
      segs rest (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
        (s₀.funcs.length + Ii.addr f.1) (lowerArgs l.imp.exports[j].ty.params vs))) tr'' m' := by
    rw [← hat.start]
    exact r'
  have hev' : ∀ ev, Label.host ev ∈ tr'' → CallHostEvent ⟨k⟩ ev :=
    fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
  obtain ⟨recs, y, hseg, hexit | hfail⟩ := lsegs_invT (cid := ⟨k⟩) hat.frame tr''.length ιe []
    M₀.conts _ tr'' m' .trap le_rfl R.thE (LInv.linkOk S hI₀) r'' ho
  · obtain ⟨ιe', N', C', pre, l', m₁, tr₂, htr, hte, hnco, hx', r₂⟩ := hexit
    have hev₂ : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨k⟩ ev :=
      fun ev hm => hev' ev (htr ▸ List.mem_append_right _ hm)
    rcases hx' with ⟨zs, hst, -, hm₁⟩ | ⟨hst, -, hm₁⟩ | ⟨h', ys', hc'⟩
    · -- the importer returns values; only a failing lift traps
      have r₃ : Steps prof (fun _ _ => false) (DI P impl)
          (retCfg (extN M₀ ιe' N' C') th K segs rest y zs) tr₂ m' := hm₁ ▸ r₂
      obtain ⟨cvs, hcode, hm⟩ := status_values hst
      have hres' : ∀ x π', LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x π' →
          ∃ r, Silmaril.Wasm.Game.ResultAt x.1 x.2 r ∧ r = .values cvs := by
        intro x π' hIx
        obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hIx.rel
        obtain ⟨ts, hs, ht⟩ := hIx.typed S
        have hc : (y.2.config (Store.mapH (gL P l) y.1)).code =
            Silmaril.Wasm.Execution.Core.vals cvs :=
          (config_code_mapH (gL P l) y.1 y.2).trans hcode
        obtain ⟨vs', hv, hvm⟩ := values_back P hL hs ht hc
        have hm' : (vs'.map (linkMap s₀ ρc).val).mapM Silmaril.Wasm.SingleThreaded.toFlat? =
            some zs := by
          rw [hvm]
          exact hm
        have hid := map_val_of_mapM _ hm'
        have hvs' : vs' = cvs := hid.symm.trans hvm
        exact ⟨.values cvs, hvs' ▸ hv, rfl⟩
      obtain ⟨w, r, rounds, dss, ⟨zs', zt⟩, π', hpath, hrel, hexp, hIz, rfl, hw⟩ :=
        lplay_resultT S hI₀ hseg hres'
      have hty : zs.map (·.type) = ValTy.flatList l.imp.exports[j].ty.results :=
        results_typed hft' hw hm
      have hR : (answerPayload w).bind
          (Silmaril.Wasm.Component.Adapter.up (.lift l.imp.exports[j].ty)) =
            (liftArgs l.imp.exports[j].ty.results zs).map .vals :=
        lifted_answer hw hm
      cases hl : liftArgs l.imp.exports[j].ty.results zs with
      | some ws =>
        obtain ⟨C'', hRes⟩ := hat.ret ιe' N' C' y zs ws hty hl
        obtain ⟨hout, -⟩ := out_of_resolvesL hRes
          (result?_nextL R.fresh _ _ _ _ _ _ _ _ _ _ _ _) r₃ hev₂ ho
        cases hout
      | none =>
        obtain ⟨-, hcore'⟩ := (hat.trap ιe' N' C' y zs hty hl).out r₃ ho
        refine ⟨⟨j, vs, f, rounds, w, dss⟩, zs', π', rfl, rfl,
          ⟨_, hck, hf₁, hf₂, hrel⟩, ?_, hpath, (expSeg_toT hexp), ?_⟩
        · show (answerPayload w).bind (Silmaril.Wasm.Component.Adapter.up (.lift _)) = none
          rw [hR, hl]
          rfl
        · rw [hcore']
          exact lready_after R.inv hIz
    · -- the importer's core activation traps
      have r₃ : Steps prof (fun _ _ => false) (DI P impl)
          (trapCfg (coreCfg (extN M₀ ιe' N' C') th K segs rest y)) tr₂ m' := hm₁ ▸ r₂
      have e₃ := steps_of_locked rfl rfl r₃
      subst e₃
      have hres' : ∀ x π', LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x π' →
          ∃ r, Silmaril.Wasm.Game.ResultAt x.1 x.2 r ∧ r = .trap := by
        intro x π' hIx
        obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hIx.rel
        obtain ⟨ts, hs, ht⟩ := hIx.typed S
        rcases status_trap hst with hc | ⟨a, hc⟩
        · exact ⟨.trap, trap_back P hL hs ht ((config_code_mapH (gL P l) y.1 y.2).trans hc), rfl⟩
        · exact (throwing_back P hL hs ht ((config_code_mapH (gL P l) y.1 y.2).trans hc)).elim
      obtain ⟨w, r, rounds, dss, ⟨zs', zt⟩, π', hpath, hrel, hexp, hIz, rfl, hw⟩ :=
        lplay_resultT S hI₀ hseg hres'
      exact ⟨⟨j, vs, f, rounds, w, dss⟩, zs', π', rfl, rfl, ⟨_, hck, hf₁, hf₂, hrel⟩,
        lifted_trap (fun _ h => by cases h) hw, hpath, (expSeg_toT hexp), lready_after R.inv hIz⟩
    · exact absurd hc' (hnco h' ys')
  · -- a failing nested call
    obtain ⟨fid, a, p, ys, hst, hf, hp, -, hfl⟩ := hfail
    obtain ⟨⟨zs, zt⟩, π', rounds, dss, hIz, hrel, hexp, hpath⟩ := lseg_path S hseg hI₀
    obtain ⟨k', nm', p', w, xe, E, a', args, e, heq, hk', hw, hxe, hpx, hdx, hm, he', -⟩ :=
      hIz.callout S hst
    have hfk : fid = l.wireFid k' ∧ witFt p = witFt p' := by
      have h' := heq
      simp only [CanonHost.lowered.injEq] at h'
      exact ⟨h'.1, h'.2.1⟩
    have hmi : (nm', p') ∈ l.imp.imports := List.mem_of_getElem? hk'
    have hpp : p = xe.ty := (witFt_inj hfk.2 hp (S.arity.2 _ hmi).2.2).trans hpx.symm
    have hfl' : ArenaField.funcs.get? M₀.store fid =
        some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) :=
      hfk.1 ▸ S.lifted k' w xe hw hxe
    have ha' : a = Ie.addrs.getD xe.core 0 := by
      injection Option.some.inj (hf.symm.trans hfl')
    subst hpp ha'
    have hek : e.1.val = k' ∧ e.2.1 = args := ifaceOp?_some he'
    have hys : e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys :=
      hek.2 ▸ filterMap_of_mapM hm
    have hk₂ : l.imp.imports[e.1.val]? = some (nm', xe.ty) := hek.1 ▸ (hpx ▸ hk')
    have hkl : e.1.val < l.imp.imports.length := (List.getElem?_eq_some_iff.mp hk₂).1
    have hP := hpath _ _ (path_trap_round hdx he')
    have hmoves : (.inr (.ask f) :: callMoves (rounds ++ [⟨e, .trap⟩]) ++ [.inr (.ans f .trap)] :
        List (Silmaril.Games.Move Ii.E Ii.F)) = .inr (.ask f) :: (callMoves rounds ++
          [.inl (.ask e), .inl (.ans e .trap), .inr (.ans f .trap)]) := by
      rw [callMoves_append, List.cons_append, List.append_assoc]
      rfl
    have hP' : Ii.Path P (.idle u) (.inr (.ask f) :: callMoves (rounds ++ [⟨e, .trap⟩]) ++
        [.inr (.ans f .trap)]) (.idle zs) := by
      rw [hmoves]
      exact .cons (.call u f) hP
    rcases hfl with ⟨hws, hcore'⟩ | ⟨ws, ev, hws, hrun, hend, hcore'⟩
    · -- the arguments do not lift: no component import call
      have hds : Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii ⟨e, .trap⟩ [] := by
        refine ⟨nm', xe.ty, none, hk₂, rfl, ?_⟩
        show match liftArgs xe.ty.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) with
          | none => _ | some ws => _
        rw [hys, hws]
        exact ⟨rfl, rfl⟩
      refine ⟨⟨j, vs, f, rounds ++ [(⟨e, .trap⟩ : Round Ii.E)], .trap, dss ++ [[]]⟩, zs, π',
        rfl, rfl,
        ⟨_, hck, hf₁, hf₂, List.rel_append hrel (.cons hds .nil)⟩, rfl, hP', ?_, ?_⟩
      · show Linked2.ExpRunT P l Ie π (dss ++ [[]]).flatten π'
        rw [List.flatten_append, List.flatten_singleton, List.append_nil]
        exact (expSeg_toT hexp)
      · rw [hcore']
        exact lready_after R.inv hIz
    · -- the exporter traps, or its results do not lift
      have hxm : xe ∈ l.exp.exports := List.mem_of_getElem? hxe
      obtain ⟨π₂, htrap, hR₂⟩ := lready_expTrap S R.inv hIz hxm
        (Silmaril.Wasm.Component.checkList_of_liftArgs hws) hrun hend
      have hds := LinkedSessionIR.impRel_trap hk₂ (hys ▸ hws)
      have hwl : w < l.exp.exports.length := (List.getElem?_eq_some_iff.mp hxe).1
      have hxw : l.exp.exports[(⟨w, hwl⟩ : Fin l.exp.exports.length)] = xe :=
        (List.getElem?_eq_some_iff.mp hxe).2
      refine ⟨⟨j, vs, f, rounds ++ [(⟨e, .trap⟩ : Round Ii.E)], .trap,
        dss ++ [[⟨(⟨e.1.val, hkl⟩, .vals ws), none⟩]]⟩, zs, π₂, rfl, rfl,
        ⟨_, hck, hf₁, hf₂, List.rel_append hrel (.cons hds .nil)⟩, rfl, hP', ?_, ?_⟩
      · dsimp only
        rw [List.flatten_append, List.flatten_singleton]
        exact expSeg_runT hexp (.trap ⟨w, hwl⟩ (hek.1 ▸ hw) (hxw ▸ htrap) (.nil π₂))
      · rw [hcore']
        exact hR₂

end Call

/-! ## Sessions -/

section Sess

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) σ}
  {fs : List (CFuncInst (core3P P))}

theorem fresh_succL {G : Garb P σ} {k : Nat} (h : G.Fresh k) : G.Fresh (k + 1) :=
  ⟨fun x hx => Nat.lt_succ_of_lt (h.pending x hx), fun x hx => Nat.lt_succ_of_lt (h.results x hx)⟩

/-- Resuming between linked calls is between calls, at the core store and host state of the
trapped configuration. -/
theorem resumeCfg_readyL (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) (h₀ : σ)
    (m' : Machine.Config (E3 P) σ) :
    resumeCfg (readyCfgL cs ιe ιi fs G ST h₀) m' = readyCfgL m'.core ιe ιi fs G ST m'.host :=
  rfl

/-- **Resumable linked sessions between calls are specification sessions.** -/
theorem sessL_inv (S₀ : LStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOk l Ii s₀ fs) :
    ∀ (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
      (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState) (G : Garb P σ)
      (ST : List Subtask) (h₀ : σ) (u π : Store Nat) (k : Nat)
      (outs : List (Option (List Silmaril.Wasm.Component.Reference.Val))),
      ReadyL P l Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k → SimpleI.TypedCalls l.imp calls →
      SessCalls prof (linkHost impl) (readyCfgL cs ιe ιi fs G ST h₀) k (callArgsL l calls) outs →
      ∃ (outs' : List (Option (List Silmaril.Wasm.Component.Val))) (u' π' : Store Nat),
        Linked2.SessSpec P l Ie Ii u π calls outs' u' π' ∧ outs = refOuts outs'
  | [], cs, ιe, ιi, G, ST, h₀, u, π, k, outs, _, _, hS => by
    cases hS
    exact ⟨[], u, π, .nil u π, rfl⟩
  | (j, vs) :: calls, cs, ιe, ιi, G, ST, h₀, u, π, k, outs, R, ht, hS => by
    have hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true := ht _ List.mem_cons_self
    have ht' : SimpleI.TypedCalls l.imp calls := fun q hq => ht q (List.mem_cons_of_mem _ hq)
    cases hS with
    | ret hcall hS' =>
      obtain ⟨r, uc, q, hu, -, hpath, hobs, hnext⟩ := linkCallK S₀ hB₀ hfs R j hvs hcall
      obtain ⟨ws, rfl, hua⟩ : ∃ ws : List Silmaril.Wasm.Component.Val,
          _ = ws.map toRefVal ∧ uc.a = some (.vals ws) := hobs
      obtain ⟨cs₁, ιe₁, ιi₁, G₁, ST₁, u₁, π₁, rfl, hexp₁, rfl, R₁⟩ := hnext _ rfl
      obtain ⟨outs', u', π', hspec, rfl⟩ :=
        sessL_inv S₀ hB₀ hfs calls cs₁ ιe₁ ιi₁ G₁ ST₁ h₀ u₁ π₁ (k + 1) _ R₁ ht' hS'
      obtain ⟨xs, dss, hcl, hq₁, hq₂, hrel, rfl⟩ := hu
      exact ⟨some ws :: outs', u', π',
        .round ⟨j, vs, r.q, r.cs, r.a, dss⟩ ⟨xs, hcl, hq₁, hq₂, hrel⟩ hpath (expSeg_toT hexp₁) hua hspec,
        rfl⟩
    | trap hcall hS' =>
      obtain ⟨d, u₁, π₁, rfl, rfl, hok, hans, hpath, hexp, hR⟩ :=
        linkCallT S₀ hB₀ hfs R j hvs hcall
      have R₁ : ReadyL P l Ie Ii s₀ u₀ F₀ _ ιe ιi G u₁ π₁ (k + 1) :=
        ⟨hR, R.thE, R.thI, R.leave, fresh_succL R.fresh⟩
      obtain ⟨outs', u', π', hspec, rfl⟩ :=
        sessL_inv S₀ hB₀ hfs calls _ ιe ιi G ST _ u₁ π₁ (k + 1) _ R₁ ht' hS'
      exact ⟨none :: outs', u', π', .round d hok hpath hexp hans hspec, rfl⟩

end Sess

/-! ## Assembly -/

/-- **Reference sessions of a linked component are specification sessions** (every profile and
component choice profile): under `Linked2.Adequate`, every resumable-session outcome list of
`l.toRef` for typed calls, under `linkHost impl` from any host state, is the list of reference
images of the outcomes of a `Linked2.SessSpec` session from the instances' stores. -/
theorem linked2_sess_refToSpec (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (ht : SimpleI.TypedCalls l.imp calls)
    {o : List (Option (List Silmaril.Wasm.Component.Reference.Val))}
    (ho : o ∈ Linked2.sessObs prof l impl h₀ calls) :
    ∃ (Ie Ii : Silmaril.Wasm.Game.ScalarInstance)
      (outs : List (Option (List Silmaril.Wasm.Component.Val))) (u' π' : Store Nat),
      l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
      Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π' ∧ o = refOuts outs := by
  obtain ⟨hEg, hEi, hIg, hIi, har, hff, hW, hN, hn, hS⟩ := hl
  obtain ⟨Ie, cse, cie, hFe, hall⟩ := instBehavioursL_inst (Pf := P) (σ := σ) hEg hEi hIg hIi har
    ⟨hS.imp.data, hS.imp.elems⟩ hW hN
  obtain ⟨Ii, hI⟩ := hIi.inst
  obtain ⟨r, hrs, hh, hres⟩ := hall Ii hI
  obtain ⟨m₀, inst, es, fs, hr, hfs, hSq⟩ := ho
  have he : m₀ = afterLink P (reloc cse (Store.mapH Prod.fst r))
      (fun k => Ie.addrs.getD k 0) (addrL (cse : Store _).funcs.length Ii) l h₀ ∧
      inst = ⟨0⟩ ∧ es = exportMapL l := by
    simpa only [InstResult.instance.injEq] using hres prof (linkHost impl) h₀ _ hr
  have hfs' : fs = calls.map fun q => (⟨l.exp.exports.length + q.1⟩ : FuncId) :=
    Option.some.inj (hfs.symm.trans (he.2.2 ▸ mapM_lookupL hIg calls))
  have hSq₁ : SessCalls prof (linkHost impl) (readyCfgL (σ := σ)
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)) {} {}
        (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
          liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) Garb.empty [] h₀)
      0 (callArgsL l calls) o := by
    have hS₀ : SessCalls prof (linkHost impl) (afterLink P (reloc cse (Store.mapH Prod.fst r))
        (fun k => Ie.addrs.getD k 0) (addrL (cse : Store _).funcs.length Ii) l h₀) 0
        (fs.zip ((calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal)).map
          Prod.snd)) o := he.1 ▸ hSq
    rw [← zip_callArgsL, ← hfs']
    exact hS₀
  have S₀ : LStat P l Ie Ii Ii.store
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)).funcs
      (readyCfgL (σ := σ) (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)) {} {}
        (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
          liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) Garb.empty [] h₀)
      (ownOf Ie.store) :=
    lstat_init hEg hIg hW hn har hff hFe hI hh _ rfl
  have hg₀ : StoreGood Ie.store := storeGood_inst hS.exp hFe.isInst.1.choose_spec
  have hgu : StoreGood Ii.store := storeGood_inst hS.imp hI.1.choose_spec
  have R₀ : ReadyL P l Ie Ii Ie.store Ii.store
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)).funcs
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)) {} {}
      (Garb.empty : Garb P σ) Ii.store Ie.store 0 :=
    { inv := lready_init hg₀ hgu (linkStore_mapH hn hW hFe hrs hh) rfl
        hFe.isInst.1.choose_spec.ok hI.1.choose_spec.ok
      thE := threadsOk_empty
      thI := threadsOk_empty
      leave := rfl
      fresh := { pending := (fun _ h => nomatch h), results := (fun _ h => nomatch h) } }
  have hok : LiftedOk l Ii Ie.store (liftedList (Pf := P) (fun k => Ie.addrs.getD k 0) ⟨1⟩
      l.exp.exports ++ liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) :=
    liftedOk_afterLink hI hIg hFe
  obtain ⟨outs, u', π', hspec, rfl⟩ :=
    sessL_inv S₀ rfl hok calls _ _ _ _ _ h₀ _ _ 0 o R₀ ht hSq₁
  exact ⟨Ie, Ii, outs, u', π', hFe.isInst, hI, hspec, rfl⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
