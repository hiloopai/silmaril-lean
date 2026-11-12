module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkCallK
public import Silmaril.Proofs.Wasm.Component.Reference.LinkNext
public import Silmaril.Proofs.Wasm.Component.Reference.SeqIRI

/-!
# A linked call between other calls

`linkCallK`: from a configuration between linked calls (`readyCfgL`) satisfying `ReadyL` (the
semantic invariant `LReady` at the shared core store, the importer's store `u` and the
exporter's `π`; reusable thread tables; fresh call ids), every terminating run of top-level call
`k` of the importer's export `j` is an IR round of the importer's instance from `u`
(`IRRoundI`), its component import calls answered by the exporter's specification from `π`
(`Linked2.ExpRun`), and the outcome is the round's lifted answer (`ObsAns`); a resolved call is
a complete activation from `u` to the next importer store `u'`, its import calls returned
calls of the exporter from `π` to `π'` (`ExpSeg`), and ends in the next configuration between
calls with `ReadyL` at `u'`, `π'` (`CallFactsL`).

The core ends come from `lsegs_inv` as in `linkCallPhase`; `lplay_valuesS` is `lplay_values`
keeping the invariant at the end, from which `lready_after` gives `LReady` for the next call.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## The end of a returned call -/

section Ends

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ π₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B : Machine.Config (E3 P) σ} {Op₀ Oc₀ : Own}
  {f : Ii.F.Op} {y₀ : CoreSt (E3 P)}

/-- **A returned activation is a complete activation** of the importer from `u₀`, answering the
part's values, its nested calls returned calls of the exporter from `π₀` to `π'`, the invariant
holding at the end. -/
theorem lplay_valuesS (S : LStat P l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y₀ (u₀, Ii.initThread f) π₀)
    {recs : List (LRec P)} {y : CoreSt (E3 P)} (hseg : LSeg B y₀ recs y) {zs : List Flat}
    (hst : (E3 P).status y.1 y.2 = .returned (.values zs)) :
    ∃ (w : Ii.F.Ar f) (cvs : List Silmaril.Wasm.Execution.Core.Val) (rounds : List (Round Ii.E))
      (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)))
      (z : Store Nat × Silmaril.Wasm.SingleThreaded.Thread) (π' : Store Nat),
      Ii.Activation P u₀ (cplay [⟨f, rounds, w⟩]) z.1 ∧
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) rounds dss ∧
      ExpSeg P l Ie π₀ dss.flatten π' ∧ LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y z π' ∧
      cvs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some zs ∧
      Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) (.values cvs) = some w := by
  obtain ⟨cvs, hcode, hm⟩ := status_values hst
  obtain ⟨z, π', rounds, dss, hIz, hrel, hexp, hpath⟩ := lseg_path S hseg hI
  obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hIz.rel
  obtain ⟨ts, hs, ht⟩ := hIz.typed S
  have hc : (y.2.config (Store.mapH (gL P l) y.1)).code = Silmaril.Wasm.Execution.Core.vals cvs :=
    (config_code_mapH (gL P l) y.1 y.2).trans hcode
  obtain ⟨vs, hv, hvm⟩ := values_back P hL hs ht hc
  have hm' : (vs.map (linkMap s₀ ρc).val).mapM Silmaril.Wasm.SingleThreaded.toFlat? = some zs := by
    rw [hvm]
    exact hm
  have hvs : vs = cvs := (map_val_of_mapM _ hm').symm.trans hvm
  have hr : Silmaril.Wasm.Game.ResultAt z.1 z.2 (.values cvs) := hvs ▸ hv
  obtain ⟨w, hw, -⟩ := Silmaril.Wasm.Game.ScalarInstance.sanswer_of_run S.impWf
    (valEnv_throwsBelow Ii _) hIz.run hr
  have hp := hpath [.inr (.ans f w)] (.idle z.1) (fun _ _ hr' => .cons (.oret hr' hr hw) (.nil _))
  exact ⟨w, cvs, rounds, dss, z, π', .cons (.call u₀ f) hp, hrel, hexp, hIz, hm, hw⟩

/-- The static facts at another importer store and another frame with the same functions. -/
theorem LStat.move {u : Store Nat} {B' : Machine.Config (E3 P) σ}
    (S : LStat P l Ie Ii u₀ F₀ B Op₀) (hw : Ii.WellFormed u) (hB : B'.store.funcs = B.store.funcs) :
    LStat P l Ie Ii u F₀ B' Op₀ :=
  { S with
    impWf := hw
    lifted := fun k w xe hw' hxe => by
      have e : ArenaField.funcs.get? B'.store (l.wireFid k) =
          ArenaField.funcs.get? B.store (l.wireFid k) := by
        simp only [ArenaField.get?, ArenaField.funcs, hB]
      rw [e]
      exact S.lifted k w xe hw' hxe }

end Ends

/-! ## Configurations between linked calls -/

theorem result?_nextL {G : Garb P σ} {k : Nat} (h : G.Fresh k) (x : SimpleExport) (j : Nat)
    (args rs : List Val) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
    (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState)
    (fs : List (CFuncInst (core3P P))) (ST : List Subtask) (h₀ : σ) :
    (readyCfgL cs ιe ιi fs (nextGarbL G x k j args rs N C) ST h₀).result? ⟨k⟩ = some (some rs) := by
  unfold Machine.Config.result?
  show ((G.results ++ [((⟨k⟩ : CallId), some rs)]).find? (fun p => p.1 == (⟨k⟩ : CallId))).map
    Prod.snd = _
  rw [List.find?_append, find?_fresh h]
  simp

theorem fresh_nextL {G : Garb P σ} {k : Nat} (h : G.Fresh k) (x : SimpleExport) (j : Nat)
    (args rs : List Val) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ))) :
    (nextGarbL G x k j args rs N C).Fresh (k + 1) where
  pending := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact Nat.lt_succ_of_lt (h.pending y hy)
    · rw [List.mem_singleton.mp hy]
      exact Nat.lt_succ_self k
  results := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact Nat.lt_succ_of_lt (h.results y hy)
    · rw [List.mem_singleton.mp hy]
      exact Nat.lt_succ_self k

/-- After a suffix resolving at a configuration between calls, the only outcome of call `k` is
the resolution there. -/
theorem out_of_resolvesL {m₁ m' : Machine.Config (E3 P) σ}
    {cs : (core3P P).Store (CanonHost (core3P P))} {ιe ιi : InstState}
    {fs : List (CFuncInst (core3P P))} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k : Nat}
    {rs : List Val} (hR : ResolvesAtL prof P impl m₁ (readyCfgL cs ιe ιi fs G ST h₀))
    (hres : (readyCfgL cs ιe ιi fs G ST h₀).result? ⟨k⟩ = some (some rs))
    {tr : List (Label (E3 P) σ)} {out : CallOutcome}
    (hs : Steps prof (fun _ _ => false) (DI P impl) m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨k⟩ ev)
    (ho : out.Holds (fun _ _ => false) ⟨k⟩ m') :
    out = .resolved (some rs) ∧ m' = readyCfgL cs ιe ιi fs G ST h₀ := by
  obtain ⟨tr₃, mE, hlr, rfl⟩ := hR
  rcases hlr.inv hs with hl | ⟨tr₄, e, r⟩
  · exact absurd ho (hl.not_holds _ _)
  have hev' : ∀ ev, Label.host ev ∈ tr₄ → CallHostEvent ⟨k⟩ ev :=
    fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
  have hq := quiet (c := ⟨k⟩) rfl (by rw [hres]; simp) (ready_tickL cs ιe ιi fs G ST h₀) _ tr₄ m'
    le_rfl r hev'
  rcases hq with rfl | hl
  · refine ⟨?_, rfl⟩
    cases out with
    | resolved r => exact congrArg _ (Option.some.inj (ho.2.2.symm.trans hres))
    | trap => exact absurd ho (fun h => Bool.false_ne_true h)
    | deadlock => exact absurd (ho.2.symm.trans hres) (by simp)
  · exact absurd ho (hl.not_holds _ _)

/-- **The invariant between linked calls**: `LReady` at the shared core store, the importer's
store `u` and the exporter's `π`; both instances' thread tables reusable, the importer's instance
may leave; earlier calls have smaller ids than `k`. -/
structure ReadyL (P : Profile) (l : Linked2) (Ie Ii : Silmaril.Wasm.Game.ScalarInstance)
    (s₀ u₀ : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P))))
    (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState) (G : Garb P σ)
    (u π : Store Nat) (k : Nat) : Prop where
  inv : LReady P l Ie Ii s₀ u₀ F₀ cs u π
  thE : ThreadsOk ιe
  thI : ThreadsOk ιi
  leave : ιi.mayLeave = true
  fresh : G.Fresh k

/-- **What a terminating linked call between calls shows**: an IR round of the importer from
`u`, its component import calls answered by the exporter from `π`, the outcome its lifted
answer; a resolved call is a complete activation to `u'`, its import calls returned calls of
the exporter to `π'`, and ends between calls with `ReadyL` at `u'`, `π'`. -/
def CallFactsL (P : Profile) (l : Linked2) (Ie Ii : Silmaril.Wasm.Game.ScalarInstance)
    (s₀ u₀ : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P))))
    (fs : List (CFuncInst (core3P P))) (h₀ : σ) (k : Nat) (j : Fin l.imp.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (u π : Store Nat) (m' : Machine.Config (E3 P) σ)
    (out : CallOutcome) : Prop :=
  ∃ (r : CRound Ii.E Ii.F)
    (uc : CRound (sigN l.imp.imports.length) (sigN l.imp.toComp.exports.length)) (q : Ii.HState),
    IRRoundI l.imp Ii j vs r uc ∧ Linked2.ExpRun P l Ie π uc.cs ∧
    Ii.Path P (.idle u) (cplay [r]) q ∧ ObsAns (Outcome.ofCall out) uc.a ∧
    ∀ rs, out = .resolved (some rs) → ∃ cs' ιe' ιi' G' ST' u' π', q = .idle u' ∧
      ExpSeg P l Ie π uc.cs π' ∧ m' = readyCfgL cs' ιe' ιi' fs G' ST' h₀ ∧
      ReadyL P l Ie Ii s₀ u₀ F₀ cs' ιe' ιi' G' u' π' (k + 1)

theorem removeThread_enter_mayLeave (ι : InstState) (t : ThreadId) :
    (InstState.removeThread 1 (enterInst ι t)).mayLeave = ι.mayLeave := rfl

/-! ## Call `k` -/

section Call

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) σ}
  {fs : List (CFuncInst (core3P P))}

/-- The component functions of the linked component: the importer's export `j` is the lift of
its core export at the relocated address. -/
def LiftedOk (l : Linked2) (Ii : Silmaril.Wasm.Game.ScalarInstance) (s₀ : Store Nat)
    (fs : List (CFuncInst (core3P P))) : Prop :=
  ∀ j : Fin l.imp.exports.length, fs[l.exp.exports.length + j]? =
    some (.lifted (s₀.funcs.length + Ii.addrs.getD l.imp.exports[j].core 0)
      (liftedFt l.imp.exports[j]) {} ⟨2⟩)

/-- **A terminating linked call between calls** (`CallFactsL`). -/
theorem linkCallK (S₀ : LStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOk l Ii s₀ fs) {cs : (core3P P).Store (CanonHost (core3P P))}
    {ιe ιi : InstState} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k : Nat} {u π : Store Nat}
    (R : ReadyL P l Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k) (j : Fin l.imp.exports.length)
    {vs : List Silmaril.Wasm.Component.Val}
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    {m' : Machine.Config (E3 P) σ} {out : CallOutcome}
    (hcalls : Calls prof (fun _ _ => false) (DI P impl) (readyCfgL cs ιe ιi fs G ST h₀) ⟨k⟩
      ⟨l.exp.exports.length + j⟩ (vs.map toRefVal) m' out) :
    CallFactsL P l Ie Ii s₀ u₀ F₀ fs h₀ k j vs u π m' out := by
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
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atLK (impl := impl) prof cs ιe ιi fs G ST
    h₀ k (l.exp.exports.length + j) _ l.imp.exports[j] vs hpf hvs hmax hres hmaxr hrf R.thI
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
  obtain ⟨recs, y, hseg, hexit | hfail⟩ := lsegs_inv (cid := ⟨k⟩) hat.frame tr''.length ιe []
    M₀.conts _ tr'' m' out le_rfl R.thE (LInv.linkOk S hI₀) r'' ho
  · show CallFactsL P l Ie Ii s₀ u₀ F₀ fs h₀ k j vs u π m' out
    obtain ⟨ιe', N', C', pre, l', m₁, tr₂, htr, hte, hnco, hx', r₂⟩ := hexit
    have hev₂ : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨k⟩ ev :=
      fun ev hm => hev' ev (htr ▸ List.mem_append_right _ hm)
    rcases hx' with ⟨zs, hst, -, hm₁⟩ | ⟨hst, -, hm₁⟩ | ⟨h', ys', hc'⟩
    · show CallFactsL P l Ie Ii s₀ u₀ F₀ fs h₀ k j vs u π m' out
      have r₃ : Steps prof (fun _ _ => false) (DI P impl)
          (retCfg (extN M₀ ιe' N' C') th K segs rest y zs) tr₂ m' := hm₁ ▸ r₂
      obtain ⟨w, cvs, rounds, dss, z, π', hact, hrel, hexp, hIz, hm, hw⟩ :=
        lplay_valuesS S hI₀ hseg hst
      have hty : zs.map (·.type) = ValTy.flatList l.imp.exports[j].ty.results :=
        results_typed hft' hw hm
      have hR : (answerPayload w).bind
          (Silmaril.Wasm.Component.Adapter.up (.lift l.imp.exports[j].ty)) =
            (liftArgs l.imp.exports[j].ty.results zs).map .vals :=
        lifted_answer hw hm
      have hrun : Linked2.ExpRun P l Ie π dss.flatten := by
        simpa only [List.append_nil] using hexp.run (.nil π')
      refine ⟨⟨f, rounds, w⟩, _, _, ⟨_, dss, hck, hf₁, hf₂, hrel, rfl⟩, hrun, hact, ?_⟩
      cases hl : liftArgs l.imp.exports[j].ty.results zs with
      | some ws =>
        show ObsAns (Outcome.ofCall out) _ ∧ _
        obtain ⟨C'', hRes⟩ := hat.ret ιe' N' C' y zs ws hty hl
        obtain ⟨hout, hm'⟩ := out_of_resolvesL hRes
          (result?_nextL R.fresh _ _ _ _ _ _ _ _ _ _ _ _) r₃ hev₂ ho
        rw [hout, hm']
        refine ⟨⟨ws, rfl, ?_⟩, fun _ _ => ?_⟩
        · show (answerPayload w).bind (Silmaril.Wasm.Component.Adapter.up (.lift _)) = _
          rw [hR, hl]
          rfl
        · exact ⟨_, _, _, _, _, z.1, π', rfl, hexp, rfl,
            ⟨lready_after R.inv hIz, hte, threadsOk_after _ _,
              (removeThread_enter_mayLeave _ _).trans R.leave, fresh_nextL R.fresh _ _ _ _ _ _⟩⟩
      | none =>
        have hout : out = .trap := (hat.trap ιe' N' C' y zs hty hl).trapsFrom.out r₃ ho
        rw [hout]
        refine ⟨?_, fun rs hrs => nomatch hrs⟩
        show (answerPayload w).bind (Silmaril.Wasm.Component.Adapter.up (.lift _)) = none
        rw [hR, hl]
        rfl
    · show CallFactsL P l Ie Ii s₀ u₀ F₀ fs h₀ k j vs u π m' out
      have r₃ : Steps prof (fun _ _ => false) (DI P impl)
          (trapCfg (coreCfg (extN M₀ ιe' N' C') th K segs rest y)) tr₂ m' := hm₁ ▸ r₂
      have hout : out = .trap := holds_trapCfgD (steps_of_locked rfl rfl r₃ ▸ ho)
      rw [hout]
      obtain ⟨w, ⟨rounds, q, dss, hpath, hrel, hexp⟩, hnone⟩ := lplay_trap S hI₀ hseg hst
      exact ⟨⟨f, rounds, w⟩, _, q, ⟨_, dss, hck, hf₁, hf₂, hrel, rfl⟩, hexp, hpath,
        hnone l.imp.exports[j], fun rs hrs => nomatch hrs⟩
    · exact absurd hc' (hnco h' ys')
  · obtain ⟨fid, a, p, ys, hst, hf, hp, hout, hfl⟩ := hfail
    rw [hout]
    obtain ⟨rounds, q, dss, hpath, hrel, hexp⟩ := lplay_fail S hI₀ hseg hst hf hp hfl
    exact ⟨⟨f, rounds, .trap⟩, _, q, ⟨_, dss, hck, hf₁, hf₂, hrel, rfl⟩, hexp, hpath, rfl,
      fun rs hrs => nomatch hrs⟩

end Call

end Silmaril.Proofs.Wasm.Component.Reference
