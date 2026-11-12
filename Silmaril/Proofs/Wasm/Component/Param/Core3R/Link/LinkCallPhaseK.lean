module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkCallPhaseK
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
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkCall
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkCallK
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkCallout
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkExp
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkNext
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
# `Silmaril.Proofs.Wasm.Component.Reference.LinkCallPhaseK` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.LinkCallPhaseK` that the
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

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P V IR) σ}

/-! ## The end of a returned call -/

section Ends

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ π₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P V IR)))} {B : Machine.Config (E3 P V IR) σ} {Op₀ Oc₀ : Own}
  {f : Ii.F.Op} {y₀ : CoreSt (E3 P V IR)}

/-- **A returned activation is a complete activation** of the importer from `u₀`, answering the
part's values, its nested calls returned calls of the exporter from `π₀` to `π'`, the invariant
holding at the end. -/
theorem lplay_valuesS [Fact (Sub P IR)] (S : LStat P V IR l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P V IR l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y₀ (u₀, Ii.initThread f) π₀)
    {recs : List (LRec P V IR)} {y : CoreSt (E3 P V IR)} (hseg : LSeg B y₀ recs y) {zs : List Flat}
    (hst : (E3 P V IR).status y.1 y.2 = .returned (.values zs)) :
    ∃ (w : Ii.F.Ar f) (cvs : List Silmaril.Wasm.Execution.Core.Val) (rounds : List (Round Ii.E))
      (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)))
      (z : Store Nat × Silmaril.Wasm.SingleThreaded.Thread) (π' : Store Nat),
      Ii.Activation P u₀ (cplay [⟨f, rounds, w⟩]) z.1 ∧
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) rounds dss ∧
      ExpSeg P l Ie π₀ dss.flatten π' ∧ LInv P V IR l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y z π' ∧
      cvs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some zs ∧
      Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) (.values cvs) = some w := by
  obtain ⟨cvs, hcode, hm⟩ := status_values hst
  obtain ⟨z, π', rounds, dss, hIz, hrel, hexp, hpath⟩ := lseg_path S hseg hI
  obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hIz.rel
  obtain ⟨ts, hs, ht⟩ := hIz.typed S
  have hc : (y.2.config (Store.mapH (gL P V IR l) y.1)).code = Silmaril.Wasm.Execution.Core.vals cvs :=
    (config_code_mapH (gL P V IR l) y.1 y.2).trans hcode
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
theorem LStat.move {u : Store Nat} {B' : Machine.Config (E3 P V IR) σ}
    (S : LStat P V IR l Ie Ii u₀ F₀ B Op₀) (hw : Ii.WellFormed u) (hB : B'.store.funcs = B.store.funcs) :
    LStat P V IR l Ie Ii u F₀ B' Op₀ :=
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

theorem result?_nextL {G : Garb P V IR σ} {k : Nat} (h : G.Fresh k) (x : SimpleExport) (j : Nat)
    (args rs : List Val) (N : List (NRec P V IR)) (C : List (Option (Activation (E3 P V IR) σ)))
    (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ιe ιi : InstState)
    (fs : List (CFuncInst (core3R P V IR))) (ST : List Subtask) (h₀ : σ) :
    (readyCfgL cs ιe ιi fs (nextGarbL G x k j args rs N C) ST h₀).result? ⟨k⟩ = some (some rs) := by
  unfold Machine.Config.result?
  show ((G.results ++ [((⟨k⟩ : CallId), some rs)]).find? (fun p => p.1 == (⟨k⟩ : CallId))).map
    Prod.snd = _
  rw [List.find?_append, find?_fresh h]
  simp

theorem fresh_nextL {G : Garb P V IR σ} {k : Nat} (h : G.Fresh k) (x : SimpleExport) (j : Nat)
    (args rs : List Val) (N : List (NRec P V IR)) (C : List (Option (Activation (E3 P V IR) σ))) :
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
theorem out_of_resolvesL {m₁ m' : Machine.Config (E3 P V IR) σ}
    {cs : (core3R P V IR).Store (CanonHost (core3R P V IR))} {ιe ιi : InstState}
    {fs : List (CFuncInst (core3R P V IR))} {G : Garb P V IR σ} {ST : List Subtask} {h₀ : σ} {k : Nat}
    {rs : List Val} (hR : ResolvesAtL prof P impl m₁ (readyCfgL cs ιe ιi fs G ST h₀))
    (hres : (readyCfgL cs ιe ιi fs G ST h₀).result? ⟨k⟩ = some (some rs))
    {tr : List (Label (E3 P V IR) σ)} {out : CallOutcome}
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
structure ReadyL (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (l : Linked2) (Ie Ii : Silmaril.Wasm.Game.ScalarInstance)
    (s₀ u₀ : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P V IR))))
    (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ιe ιi : InstState) (G : Garb P V IR σ)
    (u π : Store Nat) (k : Nat) : Prop where
  inv : LReady P V IR l Ie Ii s₀ u₀ F₀ cs u π
  thE : ThreadsOk ιe
  thI : ThreadsOk ιi
  leave : ιi.mayLeave = true
  fresh : G.Fresh k

/-- **What a terminating linked call between calls shows**: an IR round of the importer from
`u`, its component import calls answered by the exporter from `π`, the outcome its lifted
answer; a resolved call is a complete activation to `u'`, its import calls returned calls of
the exporter to `π'`, and ends between calls with `ReadyL` at `u'`, `π'`. -/
def CallFactsL (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (l : Linked2) (Ie Ii : Silmaril.Wasm.Game.ScalarInstance)
    (s₀ u₀ : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P V IR))))
    (fs : List (CFuncInst (core3R P V IR))) (h₀ : σ) (k : Nat) (j : Fin l.imp.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (u π : Store Nat) (m' : Machine.Config (E3 P V IR) σ)
    (out : CallOutcome) : Prop :=
  ∃ (r : CRound Ii.E Ii.F)
    (uc : CRound (sigN l.imp.imports.length) (sigN l.imp.toComp.exports.length)) (q : Ii.HState),
    IRRoundI l.imp Ii j vs r uc ∧ Linked2.ExpRun P l Ie π uc.cs ∧
    Ii.Path P (.idle u) (cplay [r]) q ∧ ObsAns (Outcome.ofCall out) uc.a ∧
    ∀ rs, out = .resolved (some rs) → ∃ cs' ιe' ιi' G' ST' u' π', q = .idle u' ∧
      ExpSeg P l Ie π uc.cs π' ∧ m' = readyCfgL cs' ιe' ιi' fs G' ST' h₀ ∧
      ReadyL P V IR l Ie Ii s₀ u₀ F₀ cs' ιe' ιi' G' u' π' (k + 1)

/-! ## Call `k` -/

section Call

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P V IR)))} {B₀ : Machine.Config (E3 P V IR) σ}
  {fs : List (CFuncInst (core3R P V IR))}

/-- The component functions of the linked component: the importer's export `j` is the lift of
its core export at the relocated address. -/
def LiftedOk (l : Linked2) (Ii : Silmaril.Wasm.Game.ScalarInstance) (s₀ : Store Nat)
    (fs : List (CFuncInst (core3R P V IR))) : Prop :=
  ∀ j : Fin l.imp.exports.length, fs[l.exp.exports.length + j]? =
    some (.lifted (s₀.funcs.length + Ii.addrs.getD l.imp.exports[j].core 0)
      (liftedFt l.imp.exports[j]) {} ⟨2⟩)

/-- **A terminating linked call between calls** (`CallFactsL`). -/
theorem linkCallK [Fact (Sub P IR)] (S₀ : LStat P V IR l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOk l Ii s₀ fs) {cs : (core3R P V IR).Store (CanonHost (core3R P V IR))}
    {ιe ιi : InstState} {G : Garb P V IR σ} {ST : List Subtask} {h₀ : σ} {k : Nat} {u π : Store Nat}
    (R : ReadyL P V IR l Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k) (j : Fin l.imp.exports.length)
    {vs : List Silmaril.Wasm.Component.Val}
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    {m' : Machine.Config (E3 P V IR) σ} {out : CallOutcome}
    (hcalls : Calls prof (fun _ _ => false) (DI P impl) (readyCfgL cs ιe ιi fs G ST h₀) ⟨k⟩
      ⟨l.exp.exports.length + j⟩ (vs.map toRefVal) m' out) :
    CallFactsL P V IR l Ie Ii s₀ u₀ F₀ fs h₀ k j vs u π m' out := by
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
  have S : LStat P V IR l Ie Ii u F₀ M₀ (ownOf s₀) := S₀.move R.inv.wfI (hat.funcs.trans hB₀.symm)
  have hI₀ : LInv P V IR l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f
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
  · show CallFactsL P V IR l Ie Ii s₀ u₀ F₀ fs h₀ k j vs u π m' out
    obtain ⟨ιe', N', C', pre, l', m₁, tr₂, htr, hte, hnco, hx', r₂⟩ := hexit
    have hev₂ : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨k⟩ ev :=
      fun ev hm => hev' ev (htr ▸ List.mem_append_right _ hm)
    rcases hx' with ⟨zs, hst, -, hm₁⟩ | ⟨hst, -, hm₁⟩ | ⟨h', ys', hc'⟩
    · show CallFactsL P V IR l Ie Ii s₀ u₀ F₀ fs h₀ k j vs u π m' out
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
    · show CallFactsL P V IR l Ie Ii s₀ u₀ F₀ fs h₀ k j vs u π m' out
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

end Silmaril.Proofs.Wasm.Component.Param.Core3R
