module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkFloatCallK
public import Silmaril.Proofs.Wasm.Component.Reference.LinkFloatSound
public import Silmaril.Proofs.Wasm.Component.Reference.LinkSoundSeq

/-!
# Sequences of linked calls with floats in the importer's exports

`linked2_sound_seq` (`LinkSoundSeq`) with floats at every type in the importer's exports and
float-free imports (`Linked2.ImportsFloatFree`), as `linked2_sound_floatV` (`LinkFloatSound`)
is `linked2_sound` with floats.

Each call `k` between calls branches over the NaN choices of lowering its arguments
(`call_trunLK`); each branch runs the importer's core activation on `lowerArgs params vs'` for
an admissible lowering `vs'` and continues as in `linkCallK`, the results reported canonicalised
(`linkCallKV`, `CallFactsLV`, `ObsAnsV`). Sequences of resolved calls are IR rounds on the
admissible lowerings `calls'` (`Linked2.NanCallsV`), reporting canonicalised results
(`seqL_invV`, `Linked2.canonResultsV`).

As in `linkBranchV`, the importer-side invariants (`LStat`, `ReadyL`, `LReady`, `LInv`) are taken
for `l.dropExports` (the importer's exports removed), which ask float-freedom of the imports
only; the importer's IR relation `ImpRel` depends only on the imports, and the exporter's runs
transport back to `l` (`expRun_dropExports`, `expSeg_dropExports`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

theorem expSeg_dropExports {l : Linked2} {Ie : Silmaril.Wasm.Game.ScalarInstance} {s s' : Store Nat}
    {ds : List (Σ _ : (sigN l.dropExports.imp.imports.length).Op, Option Payload)}
    (h : ExpSeg P l.dropExports Ie s ds s') : ExpSeg P l Ie s ds s' := by
  induction h with
  | nil s => exact .nil s
  | ret w hw hr _ ih => exact .ret w hw hr ih

/-- `lplay_valuesS` for the importer without exports, the exporter's returned calls
transported back to `l`. -/
theorem lplay_valuesSD {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    {u₀ s₀ π₀ : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))}
    {B : Machine.Config (E3 P) σ} {Op₀ Oc₀ : Silmaril.Proofs.Wasm.Game.Linking.Split.Own}
    {f : Ii.F.Op} {y₀ : CoreSt (E3 P)} (S : LStat P l.dropExports Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P l.dropExports Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y₀ (u₀, Ii.initThread f) π₀)
    {recs : List (LRec P)} {y : CoreSt (E3 P)} (hseg : LSeg B y₀ recs y) {zs : List Flat}
    (hst : (E3 P).status y.1 y.2 = .returned (.values zs)) :
    ∃ (w : Ii.F.Ar f) (cvs : List Silmaril.Wasm.Execution.Core.Val) (rounds : List (Round Ii.E))
      (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)))
      (z : Store Nat × Silmaril.Wasm.SingleThreaded.Thread) (π' : Store Nat),
      Ii.Activation P u₀ (cplay [⟨f, rounds, w⟩]) z.1 ∧
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) rounds dss ∧
      ExpSeg P l Ie π₀ dss.flatten π' ∧
      LInv P l.dropExports Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y z π' ∧
      cvs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some zs ∧
      Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) (.values cvs) = some w := by
  obtain ⟨w, cvs, rounds, dss, z, π', h₁, h₂, h₃, h₄, h₅, h₆⟩ := lplay_valuesS S hI hseg hst
  exact ⟨w, cvs, rounds, dss, z, π', h₁, h₂, expSeg_dropExports h₃, h₄, h₅, h₆⟩

/-- `ObsAns` with the returned values reported canonicalised at the result types `rts`. -/
def ObsAnsV (rts : List ValTy) : Silmaril.Wasm.Component.Reference.Outcome → Option Payload → Prop
  | .returns (some rs), A => ∃ ws, rs = (canonAtVList rts ws).map toRefVal ∧ A = some (.vals ws)
  | .traps, A => A = none
  | _, _ => False

/-! ## Call `k` with floats -/

section Call

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) σ}
  {fs : List (CFuncInst (core3P P))}

/-- **What a terminating linked call between calls shows, with floats**: `CallFactsL` on the
admissible lowering `vs` of the arguments, the outcome the round's lifted answer canonicalised
(`ObsAnsV`), the invariant between calls for `l.dropExports`. -/
def CallFactsLV (P : Profile) (l : Linked2) (Ie Ii : Silmaril.Wasm.Game.ScalarInstance)
    (s₀ u₀ : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P))))
    (fs : List (CFuncInst (core3P P))) (h₀ : σ) (k : Nat) (j : Fin l.imp.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (u π : Store Nat) (m' : Machine.Config (E3 P) σ)
    (out : CallOutcome) : Prop :=
  ∃ (r : CRound Ii.E Ii.F)
    (uc : CRound (sigN l.imp.imports.length) (sigN l.imp.toComp.exports.length)) (q : Ii.HState),
    IRRoundI l.imp Ii j vs r uc ∧ Linked2.ExpRun P l Ie π uc.cs ∧
    Ii.Path P (.idle u) (cplay [r]) q ∧
    ObsAnsV l.imp.exports[j].ty.results (Outcome.ofCall out) uc.a ∧
    ∀ rs, out = .resolved (some rs) → ∃ cs' ιe' ιi' G' ST' u' π', q = .idle u' ∧
      ExpSeg P l Ie π uc.cs π' ∧ m' = readyCfgL cs' ιe' ιi' fs G' ST' h₀ ∧
      ReadyL P l.dropExports Ie Ii s₀ u₀ F₀ cs' ιe' ιi' G' u' π' (k + 1)

/-- The branching run of call `k` of the importer's export `j` between calls. -/
theorem trunLK_of (har : l.imp.Arity) (hfs : LiftedOk l Ii s₀ fs) {l' : Linked2}
    {cs : (core3P P).Store (CanonHost (core3P P))} {ιe ιi : InstState} {G : Garb P σ}
    {k : Nat} {u π : Store Nat} (R : ReadyL P l' Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k)
    (ST : List Subtask) (h₀ : σ) (j : Fin l.imp.exports.length)
    {vs : List Silmaril.Wasm.Component.Val}
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) :
    TRun prof (fun _ _ => false) (DI P impl)
      (QLK prof P impl cs ιe (enterInst ιi ⟨G.threads.length⟩) fs G ST h₀ k
        (l.exp.exports.length + j) l.imp.exports[j]
        (s₀.funcs.length + Ii.addrs.getD l.imp.exports[j].core 0) vs)
      (invokedAtL cs ιe ιi fs G ST h₀ k (l.exp.exports.length + j) (vs.map toRefVal)) := by
  obtain ⟨hmax, hmaxr, hres⟩ := har.1 _ (List.getElem_mem j.isLt)
  exact call_trunLK prof cs ιe ιi fs G ST h₀ k _ _ l.imp.exports[j] vs hvs hmax hres hmaxr
    R.thI R.leave (hfs j)

set_option maxHeartbeats 400000 in
/-- **A terminating linked call between calls, with floats** (`CallFactsLV` on an admissible
lowering of the arguments). -/
theorem linkCallKV (hIg : l.imp.Good) (har : l.imp.Arity)
    (S₀ : LStat P l.dropExports Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOk l Ii s₀ fs) {cs : (core3P P).Store (CanonHost (core3P P))}
    {ιe ιi : InstState} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k : Nat} {u π : Store Nat}
    (R : ReadyL P l.dropExports Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k) (j : Fin l.imp.exports.length)
    {vs : List Silmaril.Wasm.Component.Val}
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    {m' : Machine.Config (E3 P) σ} {out : CallOutcome}
    (hcalls : Calls prof (fun _ _ => false) (DI P impl) (readyCfgL cs ιe ιi fs G ST h₀) ⟨k⟩
      ⟨l.exp.exports.length + j⟩ (vs.map toRefVal) m' out) :
    ∃ vs', NanAtVList prof l.imp.exports[j].ty.params vs vs' ∧
      ValTy.checkList l.imp.exports[j].ty.params vs' = true ∧
      CallFactsLV P l Ie Ii s₀ u₀ F₀ fs h₀ k j vs' u π m' out := by
  have hT := trunLK_of (prof := prof) (impl := impl) har hfs R ST h₀ j hvs
  obtain ⟨tr, hs, hev, -, ho⟩ := hcalls
  obtain ⟨m₂, st, r₁⟩ := Steps.cons_iff.mp hs
  have r₀ : Steps prof (fun _ _ => false) (DI P impl) (invokedAtL cs ιe ιi fs G ST h₀ k
      (l.exp.exports.length + j) (vs.map toRefVal)) tr m' := invoke_invL st ▸ r₁
  rcases hT.inv r₀ with hl | ⟨M₀, tr₁, tr'', ⟨vs', th, K, segs, rest, hnan, hvs', hat⟩, e, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  refine ⟨vs', hnan, hvs', ?_⟩
  have hx : l.imp.exports[j] ∈ l.imp.exports := List.getElem_mem j.isLt
  obtain ⟨nm, hcore⟩ := hIg.core _ hx
  have hk : l.imp.exports[j].core < l.imp.mod.exports.length :=
    (List.getElem?_eq_some_iff.mp hcore).1
  have hflat : l.imp.mod.exports[l.imp.exports[j].core] = (nm, l.imp.exports[j].ty.flat) :=
    (List.getElem?_eq_some_iff.mp hcore).2
  have hxs : (lowerArgs l.imp.exports[j].ty.params vs').map (·.type) =
      l.imp.mod.exports[l.imp.exports[j].core].2.params := by
    rw [hflat]
    exact lowerList_types _ _ hvs'
  have hIi : l.imp.mod.IsInst Ii := S₀.impInst
  obtain ⟨f, hf₁, hf₂, hft⟩ := typedCallI hIi hk hxs
  have hft' : Ii.exports.get f.1 = fnOf l.imp.exports[j].ty.flat := by rw [hft, hflat]
  have ha : Ii.addrs.getD l.imp.exports[j].core 0 = Ii.addr f.1 := by
    rw [← hf₁]
    rfl
  rw [ha] at hat
  have S : LStat P l.dropExports Ie Ii u F₀ M₀ (ownOf s₀) :=
    S₀.move R.inv.wfI (hat.funcs.trans hB₀.symm)
  have hI₀ : LInv P l.dropExports Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1)
        (lowerArgs l.imp.exports[j].ty.params vs')) (u, Ii.initThread f) π :=
    linv_ready R.inv hf₂ rfl
  have hck : checkLower l.imp.exports[j].ty.params vs' =
      some (lowerArgs l.imp.exports[j].ty.params vs') := by
    simp only [checkLower, hvs', ↓reduceIte]
  have r'' : Steps prof (fun _ _ => false) (DI P impl) (coreCfg (extN M₀ ιe [] M₀.conts) th K
      segs rest (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
        (s₀.funcs.length + Ii.addr f.1) (lowerArgs l.imp.exports[j].ty.params vs'))) tr'' m' := by
    rw [← hat.start]
    exact r'
  have hev' : ∀ ev, Label.host ev ∈ tr'' → CallHostEvent ⟨k⟩ ev :=
    fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
  obtain ⟨recs, y, hseg, hexit | hfail⟩ := lsegs_inv (cid := ⟨k⟩) hat.frame tr''.length ιe []
    M₀.conts _ tr'' m' out le_rfl R.thE (LInv.linkOk S hI₀) r'' ho
  · show CallFactsLV P l Ie Ii s₀ u₀ F₀ fs h₀ k j vs' u π m' out
    obtain ⟨ιe', N', C', pre, l', m₁, tr₂, htr, hte, hnco, hx', r₂⟩ := hexit
    have hev₂ : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨k⟩ ev :=
      fun ev hm => hev' ev (htr ▸ List.mem_append_right _ hm)
    rcases hx' with ⟨zs, hst, -, hm₁⟩ | ⟨hst, -, hm₁⟩ | ⟨h', ys', hc'⟩
    · show CallFactsLV P l Ie Ii s₀ u₀ F₀ fs h₀ k j vs' u π m' out
      have r₃ : Steps prof (fun _ _ => false) (DI P impl)
          (retCfg (extN M₀ ιe' N' C') th K segs rest y zs) tr₂ m' := hm₁ ▸ r₂
      obtain ⟨w, cvs, rounds, dss, z, π', hact, hrel, hexp', hIz, hm, hw⟩ :=
        lplay_valuesSD S hI₀ hseg hst
      have hty : zs.map (·.type) = ValTy.flatList l.imp.exports[j].ty.results :=
        results_typed hft' hw hm
      have hR : (answerPayload w).bind
          (Silmaril.Wasm.Component.Adapter.up (.lift l.imp.exports[j].ty)) =
            (liftArgs l.imp.exports[j].ty.results zs).map .vals :=
        lifted_answer hw hm
      have hrun : Linked2.ExpRun P l Ie π dss.flatten := by
        simpa only [List.append_nil] using hexp'.run (.nil π')
      refine ⟨⟨f, rounds, w⟩, _, _, ⟨_, dss, hck, hf₁, hf₂, hrel, rfl⟩, hrun, hact, ?_⟩
      cases hl : liftArgs l.imp.exports[j].ty.results zs with
      | some ws =>
        show ObsAnsV _ (Outcome.ofCall out) _ ∧ _
        obtain ⟨C'', hRes⟩ := hat.ret ιe' N' C' y zs ws hty hl
        obtain ⟨hout, hm'⟩ := out_of_resolvesL hRes
          (result?_nextL R.fresh _ _ _ _ _ _ _ _ _ _ _ _) r₃ hev₂ ho
        rw [hout, hm']
        refine ⟨⟨ws, rfl, ?_⟩, fun _ _ => ?_⟩
        · show (answerPayload w).bind (Silmaril.Wasm.Component.Adapter.up (.lift _)) = _
          rw [hR, hl]
          rfl
        · exact ⟨_, _, _, _, _, z.1, π', rfl, hexp', rfl,
            ⟨lready_after R.inv hIz, hte, threadsOk_after _ _,
              (removeThread_enter_mayLeave _ _).trans R.leave, fresh_nextL R.fresh _ _ _ _ _ _⟩⟩
      | none =>
        have hout : out = .trap := (hat.trap ιe' N' C' y zs hty hl).trapsFrom.out r₃ ho
        rw [hout]
        refine ⟨?_, fun rs hrs => nomatch hrs⟩
        show (answerPayload w).bind (Silmaril.Wasm.Component.Adapter.up (.lift _)) = none
        rw [hR, hl]
        rfl
    · show CallFactsLV P l Ie Ii s₀ u₀ F₀ fs h₀ k j vs' u π m' out
      have r₃ : Steps prof (fun _ _ => false) (DI P impl)
          (trapCfg (coreCfg (extN M₀ ιe' N' C') th K segs rest y)) tr₂ m' := hm₁ ▸ r₂
      have hout : out = .trap := holds_trapCfgD (steps_of_locked rfl rfl r₃ ▸ ho)
      rw [hout]
      obtain ⟨w, hP, hnone⟩ := lplay_trap S hI₀ hseg hst
      obtain ⟨rounds, q, dss, hpath, hrel, hexp⟩ := lplay_dropExports hP
      exact ⟨⟨f, rounds, w⟩, _, q, ⟨_, dss, hck, hf₁, hf₂, hrel, rfl⟩, hexp, hpath,
        hnone l.imp.exports[j], fun rs hrs => nomatch hrs⟩
    · exact absurd hc' (hnco h' ys')
  · obtain ⟨fid, a, p, ys, hst, hf, hp, hout, hfl⟩ := hfail
    rw [hout]
    obtain ⟨rounds, q, dss, hpath, hrel, hexp⟩ :=
      lplay_dropExports (lplay_fail S hI₀ hseg hst hf hp hfl)
    exact ⟨⟨f, rounds, .trap⟩, _, q, ⟨_, dss, hck, hf₁, hf₂, hrel, rfl⟩, hexp, hpath, rfl,
      fun rs hrs => nomatch hrs⟩

end Call

/-! ## Sequences of resolved calls with floats -/

section Seq

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) σ}
  {fs : List (CFuncInst (core3P P))}

/-- What a sequence of resolved linked calls shows from a configuration between calls, with
floats: `SeqFactsL` on admissible lowerings `calls'` of the calls, results canonicalised. -/
def SeqFactsLV (P : Profile) (prof : ProfileKind) (l : Linked2)
    (Ie Ii : Silmaril.Wasm.Game.ScalarInstance) (s₀ u₀ : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (fs : List (CFuncInst (core3P P))) (h₀ : σ)
    (u π : Store Nat) (k : Nat)
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (rss : List (List Silmaril.Wasm.Component.Reference.Val)) (mₙ : Machine.Config (E3 P) σ) : Prop :=
  ∃ (calls' : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (lr : List (CRound Ii.E Ii.F)) (dss : List (List (Round (sigN l.imp.imports.length))))
    (wss : List (List Silmaril.Wasm.Component.Val)) (cs' : (core3P P).Store (CanonHost (core3P P)))
    (ιe' ιi' : InstState) (G' : Garb P σ) (ST' : List Subtask) (u' π' : Store Nat),
    Linked2.NanCallsV prof l calls calls' ∧ SimpleI.TypedCalls l.imp calls' ∧
    Ii.Activation P u (cplay lr) u' ∧
    List.Forall₂ (fun r uc => ∃ j vs, IRRoundI l.imp Ii j vs r uc) lr
      (seqRoundsI l.imp calls' dss wss) ∧
    ExpSeg P l Ie π ((seqRoundsI l.imp calls' dss wss).flatMap (·.cs)) π' ∧
    rss = Linked2.canonResultsV l calls' wss ∧ calls'.length = dss.length ∧
    calls'.length = wss.length ∧ mₙ = readyCfgL cs' ιe' ιi' fs G' ST' h₀ ∧
    ReadyL P l.dropExports Ie Ii s₀ u₀ F₀ cs' ιe' ιi' G' u' π' (k + calls.length)

/-- **Sequences of resolved linked calls with floats** from a configuration between calls. -/
theorem seqL_invV (hIg : l.imp.Good) (har : l.imp.Arity)
    (S₀ : LStat P l.dropExports Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOk l Ii s₀ fs) (h₀ : σ) :
    ∀ (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
      (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState) (G : Garb P σ)
      (ST : List Subtask) (u π : Store Nat) (k : Nat) (rss : List (List Silmaril.Wasm.Component.Reference.Val))
      (mₙ : Machine.Config (E3 P) σ),
      ReadyL P l.dropExports Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k →
      SimpleI.TypedCalls l.imp calls →
      SeqCalls prof (linkHost impl) (readyCfgL cs ιe ιi fs G ST h₀) k (callArgsL l calls) rss
        mₙ →
      SeqFactsLV P prof l Ie Ii s₀ u₀ F₀ fs h₀ u π k calls rss mₙ
  | [], cs, ιe, ιi, G, ST, u, π, k, rss, mₙ, R, _, hS => by
    cases hS
    exact ⟨[], [], [], [], cs, ιe, ιi, G, ST, u, π, List.Forall₂.nil, (fun _ h => nomatch h),
      .nil _, List.Forall₂.nil, .nil π, rfl, rfl, rfl, rfl, R⟩
  | (j, vs) :: calls, cs, ιe, ιi, G, ST, u, π, k, rss, mₙ, R, ht, hS => by
    cases hS with
    | cons hcall hS' =>
      have hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true := ht _ List.mem_cons_self
      obtain ⟨vs', hnan, hvs', r, uc, q, hu, -, hpath, hobs, hnext⟩ :=
        linkCallKV hIg har S₀ hB₀ hfs R j hvs hcall
      obtain ⟨ws, rfl, hua⟩ : ∃ ws : List Silmaril.Wasm.Component.Val,
          _ = (canonAtVList l.imp.exports[j].ty.results ws).map toRefVal ∧
            uc.a = some (.vals ws) := hobs
      obtain ⟨cs₁, ιe₁, ιi₁, G₁, ST₁, u₁, π₁, rfl, hexp₁, rfl, R₁⟩ := hnext _ rfl
      obtain ⟨calls', lr, dss, wss, cs', ιe', ιi', G', ST', u', π', hN, ht', hact, hrel, hexp,
        rfl, hl₁, hl₂, hm, R'⟩ := seqL_invV hIg har S₀ hB₀ hfs h₀ calls cs₁ ιe₁ ιi₁ G₁ ST₁ u₁
          π₁ (k + 1) _ _ R₁ (fun q hq => ht q (List.mem_cons_of_mem _ hq)) hS'
      have hk : k + 1 + calls.length = k + ((j, vs) :: calls).length := by
        simp only [List.length_cons]
        omega
      have hu' : uc = ⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs'), uc.cs, some (.vals ws)⟩ :=
        hu.eq hua
      refine ⟨(j, vs') :: calls', r :: lr, uc.cs :: dss, ws :: wss, cs', ιe', ιi', G', ST', u',
        π', .cons ⟨rfl, hnan⟩ hN, ?_, ?_, .cons ⟨j, vs', hu' ▸ hu⟩ hrel, ?_, rfl,
        by rw [List.length_cons, hl₁, List.length_cons],
        by rw [List.length_cons, hl₂, List.length_cons], hm, hk ▸ R'⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hvs'
        · exact ht' q hq
      · show Ii.Path P _ (cplay ([r] ++ lr)) _
        rw [cplay_append]
        exact path_append hpath hact
      · rw [show seqRoundsI l.imp ((j, vs') :: calls') (uc.cs :: dss) (ws :: wss) =
          ⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs'), uc.cs, some (.vals ws)⟩ ::
            seqRoundsI l.imp calls' dss wss from rfl, List.flatMap_cons]
        exact hexp₁.append hexp

end Seq

/-! ## Assembly -/

section Assembly

variable {l : Linked2}

/-- The last call's IR observation from its round and the earlier rounds, with floats. -/
theorem seqIRObsLV_of {Ii : Silmaril.Wasm.Game.ScalarInstance}
    {calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)}
    {dss : List (List (Round (sigN l.imp.imports.length)))}
    {wss : List (List Silmaril.Wasm.Component.Val)} (hl₁ : calls.length = dss.length)
    (hl₂ : calls.length = wss.length) {j : Fin l.imp.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {r : CRound Ii.E Ii.F}
    {uc : CRound (sigN l.imp.imports.length) (sigN l.imp.toComp.exports.length)}
    (hu : IRRoundI l.imp Ii j vs r uc) :
    ∀ b : Silmaril.Wasm.Component.Reference.Outcome, ObsAnsV l.imp.exports[j].ty.results b uc.a →
      cplay ((seqRoundsI l.imp calls dss wss ++ [uc]).map (Linked2.linkRound l)) ∈
        l.toComp.den (impSem P) →
      Linked2.SeqIRObsV P l calls wss j vs b
  | .returns (some rs), ⟨ws, hrs, hA⟩, h => by
    refine ⟨ws, hrs, ?_⟩
    rw [hu.eq hA, ← seqRoundsI_append l.imp j vs ws uc.cs calls dss wss hl₁ hl₂,
      cplay_seqRoundsL l _ _ _ (by simp [hl₁]) (by simp [hl₂])] at h
    exact h
  | .traps, hA, h => by
    rw [hu.eq hA, List.map_append, cplay_append,
      cplay_seqRoundsL l calls dss wss hl₁ hl₂] at h
    exact h
  | .returns none, _, _ => trivial
  | .deadlocks, _, _ => trivial
  | .diverges, _, _ => trivial

/-- **Soundness of two linked components for sequences of calls with floats in the importer's
exports** (every profile and component choice profile): `linked2_sound_seq` with
`l.imp.FloatFree` weakened to float-free imports. The linked IR plays the resolved calls on
admissible lowerings `calls'` of their arguments (`Linked2.NanCallsV`), the reference reporting
the IR results canonicalised (`Linked2.canonResultsV`), and the last call on an admissible
lowering `vs'` as `Linked2.SeqIRObsV` prescribes. -/
theorem linked2_sound_seq_floatV (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hEg : l.exp.Good) (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst)
    (har : l.imp.Arity) (hfi : l.ImportsFloatFree) (hW : l.WireTy) (hN : l.NamesOk)
    (hn : l.WireNodup) (hS : l.SplitOk) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Reference.Val) × Silmaril.Wasm.Component.Reference.Outcome)
    (hp : p ∈ seqBehaviours prof (linkHost impl) h₀ l.toRef
      (calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal)) l.imp.exports[j].name
      (vs.map toRefVal)) :
    ∃ (calls' : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
      (wss : List (List Silmaril.Wasm.Component.Val)) (vs' : List Silmaril.Wasm.Component.Val),
      Linked2.NanCallsV prof l calls calls' ∧ SimpleI.TypedCalls l.imp calls' ∧
      NanAtVList prof l.imp.exports[j].ty.params vs vs' ∧
      ValTy.checkList l.imp.exports[j].ty.params vs' = true ∧
      p.1 = Linked2.canonResultsV l calls' wss ∧
      Linked2.seqMoves l calls' wss ∈ l.toComp.den (impSem P) ∧
      Linked2.SeqIRObsV P l calls' wss j vs' p.2 := by
  obtain ⟨Ie, cse, cie, hFe, hall⟩ := instBehavioursL_inst (Pf := P) (σ := σ) hEg hEi hIg hIi har
    ⟨hS.imp.data, hS.imp.elems⟩ hW hN
  obtain ⟨Ii, hI⟩ := hIi.inst
  obtain ⟨r, hrs, hh, hres⟩ := hall Ii hI
  rcases hp with ⟨m₀, inst, es, fs, mₙ, f, hr, hfs, hSq, hl, hb⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  rotate_left
  · exact absurd (hres prof (linkHost impl) h₀ _ hr) (by simp)
  · exact absurd (hres prof (linkHost impl) h₀ _ hr) (by simp)
  have he : m₀ = afterLink P (reloc cse (Store.mapH Prod.fst r))
      (fun k => Ie.addrs.getD k 0) (addrL (cse : Store _).funcs.length Ii) l h₀ ∧
      inst = ⟨0⟩ ∧ es = exportMapL l := by
    simpa only [InstResult.instance.injEq] using hres prof (linkHost impl) h₀ _ hr
  have hfs' : fs = calls.map fun q => (⟨l.exp.exports.length + q.1⟩ : FuncId) :=
    Option.some.inj (hfs.symm.trans (he.2.2 ▸ mapM_lookupL hIg calls))
  have hf' : f = ⟨l.exp.exports.length + j⟩ :=
    Option.some.inj (hl.symm.trans (he.2.2 ▸ exportMapL_lookup hIg j))
  have hSq₁ : SeqCalls prof (linkHost impl) (readyCfgL (σ := σ)
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)) {} {}
        (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
          liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) Garb.empty [] h₀)
      0 (callArgsL l calls) p.1 mₙ := by
    have hS₀ : SeqCalls prof (linkHost impl) (afterLink P (reloc cse (Store.mapH Prod.fst r))
        (fun k => Ie.addrs.getD k 0) (addrL (cse : Store _).funcs.length Ii) l h₀) 0
        (fs.zip ((calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal)).map
          Prod.snd)) p.1 mₙ := he.1 ▸ hSq
    rw [← zip_callArgsL, ← hfs']
    exact hS₀
  -- the static facts and the invariant after instantiation, for the importer without exports
  have S₀ : LStat P l.dropExports Ie Ii Ii.store
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)).funcs
      (readyCfgL (σ := σ) (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)) {} {}
        (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
          liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) Garb.empty [] h₀)
      (ownOf Ie.store) :=
    lstat_init (l := l.dropExports) hEg (good_dropExports hIg) (wireTy_dropExports hW) hn
      (arity_dropExports har) (floatFree_dropExports hfi) hFe hI hh _ rfl
  have hg₀ : StoreGood Ie.store := storeGood_inst hS.exp hFe.isInst.1.choose_spec
  have hgu : StoreGood Ii.store := storeGood_inst hS.imp hI.1.choose_spec
  have R₀ : ReadyL P l.dropExports Ie Ii Ie.store Ii.store
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)).funcs
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)) {} {}
      (Garb.empty : Garb P σ) Ii.store Ie.store 0 :=
    { inv := lready_init (l := l.dropExports) hg₀ hgu
        (linkStore_mapH (l := l.dropExports) hn (wireTy_dropExports hW) hFe hrs hh) rfl
        hFe.isInst.1.choose_spec.ok hI.1.choose_spec.ok
      thE := threadsOk_empty
      thI := threadsOk_empty
      leave := rfl
      fresh := { pending := (fun _ h => nomatch h), results := (fun _ h => nomatch h) } }
  have hok : LiftedOk l Ii Ie.store (liftedList (Pf := P) (fun k => Ie.addrs.getD k 0) ⟨1⟩
      l.exp.exports ++ liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) :=
    liftedOk_afterLink hI hIg hFe
  obtain ⟨calls', lr, dss, wss, cs', ιe', ιi', G', ST', u', π', hNc, ht', hact, hrel, hexp, hrss,
    hl₁, hl₂, hmₙ, R'⟩ := seqL_invV hIg har S₀ rfl hok h₀ calls _ _ _ _ _ _ _ 0 _ _ R₀ ht hSq₁
  have hb' : p.2 ∈ callBehaviours prof (linkHost impl) (readyCfgL cs' ιe' ιi'
      (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
        liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) G' ST' h₀)
      ⟨0 + calls.length⟩ ⟨l.exp.exports.length + j⟩ (vs.map toRefVal) := by
    have hmₙ' : mₙ = readyCfgL cs' ιe' ιi'
        (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
          liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) G' ST' h₀ := hmₙ
    rw [← hmₙ', ← hf', Nat.zero_add, ← List.length_map
      (f := fun q : Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val =>
        (l.imp.exports[q.1].name, q.2.map toRefVal))]
    exact hb
  have hrun : Linked2.ExpRun P l Ie Ie.store
      ((seqRoundsI l.imp calls' dss wss).flatMap (·.cs)) := by
    simpa only [List.append_nil] using hexp.run (.nil π')
  have hpre : Linked2.seqMoves l calls' wss ∈ l.toComp.den (impSem P) := by
    rw [← cplay_seqRoundsL l calls' dss wss hl₁ hl₂]
    exact linked_seq_den hEg hIg hFe.isInst hI hrel (cplay_mem_strategy hact) hrun
  rcases hb' with ⟨m', out, hcalls, hpo⟩ | ⟨hd, m₂, s, hdv⟩
  · show ∃ (calls' : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
      (wss : List (List Silmaril.Wasm.Component.Val)) (vs' : List Silmaril.Wasm.Component.Val), _
    obtain ⟨vs', hnan, hck', r₁, uc, q, hu, hrun₁, hpath, hobs, -⟩ :=
      linkCallKV hIg har S₀ rfl hok R' j hvs hcalls
    refine ⟨calls', wss, vs', hNc, ht', hnan, hck', hrss, hpre, ?_⟩
    have hall : Ii.Path P (.idle Ii.store) (cplay (lr ++ [r₁])) q := by
      rw [cplay_append]
      exact path_append hact hpath
    have hrun' : Linked2.ExpRun P l Ie Ie.store
        ((seqRoundsI l.imp calls' dss wss ++ [uc]).flatMap (·.cs)) := by
      rw [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact hexp.run hrun₁
    have hden : cplay ((seqRoundsI l.imp calls' dss wss ++ [uc]).map (Linked2.linkRound l)) ∈
        l.toComp.den (impSem P) :=
      linked_seq_den hEg hIg hFe.isInst hI (forall₂_append hrel (.cons ⟨j, vs', hu⟩ .nil))
        (cplay_mem_strategy hall) hrun'
    rw [hpo]
    exact seqIRObsLV_of hl₁ hl₂ hu _ (hpo ▸ hobs) hden
  · obtain ⟨mq, hq, -⟩ := (trunLK_of (prof := prof) (impl := impl) har hok R' ST' h₀ j
      hvs).diverges (invoke_invL s ▸ hdv)
    obtain ⟨vs', -, -, -, -, hnan, hck', -⟩ := hq
    refine ⟨calls', wss, vs', hNc, ht', hnan, hck', hrss, hpre, ?_⟩
    rw [hd]
    trivial

/-- Under the deterministic component profile the admissible lowerings of calls are their
canonicalisations. -/
theorem nanCallsL_deterministicV (l : Linked2) :
    ∀ {calls calls' : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)},
      Linked2.NanCallsV .deterministic l calls calls' → calls' = Linked2.canonCallsV l calls
  | [], [], .nil => rfl
  | (j, vs) :: _, (j', vs') :: _, .cons ⟨e, hn⟩ h => by
    obtain rfl : j' = j := e
    have hv : vs' = canonAtVList l.imp.exports[j'].ty.params vs :=
      nanAtVList_deterministic _ _ _ hn
    rw [nanCallsL_deterministicV l h, hv]
    rfl

/-- **Sequences of linked calls with floats under the deterministic component profile**: the
linked IR is called on the canonicalised arguments. -/
theorem linked2_sound_seq_floatV_deterministic (P : Profile) (l : Linked2) (hEg : l.exp.Good)
    (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst) (har : l.imp.Arity)
    (hfi : l.ImportsFloatFree) (hW : l.WireTy) (hN : l.NamesOk) (hn : l.WireNodup)
    (hS : l.SplitOk) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Reference.Val) × Silmaril.Wasm.Component.Reference.Outcome)
    (hp : p ∈ seqBehaviours .deterministic (linkHost impl) h₀ l.toRef
      (calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal)) l.imp.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val),
      p.1 = Linked2.canonResultsV l (Linked2.canonCallsV l calls) wss ∧
      Linked2.seqMoves l (Linked2.canonCallsV l calls) wss ∈ l.toComp.den (impSem P) ∧
      Linked2.SeqIRObsV P l (Linked2.canonCallsV l calls) wss j
        (canonAtVList l.imp.exports[j].ty.params vs) p.2 := by
  obtain ⟨calls', wss, vs', hNc, -, hnan, -, hp1, hpre, hobs⟩ :=
    linked2_sound_seq_floatV P .deterministic l hEg hEi hIg hIi har hfi hW hN hn hS impl h₀
      calls j vs ht hvs p hp
  rw [nanCallsL_deterministicV l hNc] at hp1 hpre hobs
  rw [nanAtVList_deterministic _ _ _ hnan] at hobs
  exact ⟨wss, hp1, hpre, hobs⟩

end Assembly

end Silmaril.Proofs.Wasm.Component.Reference
