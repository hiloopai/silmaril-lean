module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.RefRound

/-!
# Sessions of `HLinked2.toRef`, reference to specification

* `linkCall_invH`: a call of the reference machine between calls (`ReadyL` at `l.toW`), under a
  host that handles the host callouts as a typed `g` prescribes (`HandlesB`), is a well-formed
  specification round of the importer from its store, whose component import calls are an
  `ExpRunH` segment of the exporter from its store and whose host calls form a `HostRun g` from
  the host state of the call; a resolved call ends between calls with `ReadyL` again, a trapped
  call with `LReady` at the trapped core store and the host state of the trap (`BackOutH`). It is
  the backward counterpart of `linkCall_fwdG`, from `rounds_invH`;
* `sessH_inv`: resumable sessions (`SessRun`, `resumeCfg` after a trap) from a configuration
  between calls are specification sessions (`HLinked2.SessSpec`) whose host calls form a
  `HostRun g` to the final host state;
* `hlinked2_sess_refToSpec`: the session observations of `l.toRef` under the logging host
  `answerHostS P (logG g)` (`HLinked2.sessObs`) for typed calls are specification sessions from
  the instances' stores whose host calls form a `HostRun (logG g)` from `(s₀, [])` to the final
  host state and log; `hlinked2_sessObs_eq`: with `hlinked2_sess_specToRef`, the session
  observations are exactly the specification sessions with their `HostRun`;
* `handlesB_silent`: the host that never answers handles the host callouts as `silentG`, the
  call trapping `cannotBlockSync` once the importer's thread blocks;
  `hlinked2_silent_refToSpec`, `hlinked2_silentObs_eq`: the session observations under
  `silentHost` are exactly the specification sessions whose host calls all trap
  (`HostRun silentG`), in the initial host state.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind}
  {g : σ → HostFuncId → List RVal → Option (List RVal × σ)}

/-- What a backward call of an `HLinked2` shows for its outcome, the round answering `o`: a
resolved call answers the reference image of `o = some ws` and ends between calls in host state
`s'` with `ReadyL` at `u₁`, `π₁`; a trapped call answers `o = none`, with `LReady` at the core
store of the trapped configuration, in host state `s'`; no other outcome. -/
def BackOutH (P : Profile) (l : HLinked2) (Ie Ii : Silmaril.Wasm.Game.ScalarInstance)
    (s₀ u₀ : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P))))
    (fs : List (CFuncInst (core3P P))) (k : Nat) (m' : Machine.Config (E3 P) σ)
    (u₁ π₁ : Store Nat) (s' : σ) (o : Option (List IVal)) : CallOutcome → Prop
  | .resolved (some rs) => ∃ ws, o = some ws ∧ rs = ws.map toRefVal ∧
      ∃ (cs' : (core3P P).Store (CanonHost (core3P P))) (ιe' ιi' : InstState) (G' : Garb P σ)
        (ST' : List Subtask), m' = readyCfgL cs' ιe' ιi' fs G' ST' s' ∧
        ReadyL P l.toW Ie Ii s₀ u₀ F₀ cs' ιe' ιi' G' u₁ π₁ (k + 1)
  | .trap => o = none ∧ LReady P l.toW Ie Ii s₀ u₀ F₀ m'.core u₁ π₁ ∧ m'.host = s'
  | _ => False

section Call

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) σ}
  {fs : List (CFuncInst (core3P P))}

/-- **A call of the reference machine between calls is a specification round** (backward
counterpart of `linkCall_fwdH`), its host calls answered by `g` from the call's host state. -/
theorem linkCall_invH {impl : HostImpl (E3 P) σ} (hHd : HandlesB prof P impl g l)
    (hT : l.HostTyped g) (S₀ : HStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀))
    (hB₀ : B₀.store.funcs = fs) (hfs : LiftedOkH l Ii s₀ fs)
    {cs : (core3P P).Store (CanonHost (core3P P))} {ιe ιi : InstState} {G : Garb P σ}
    {ST : List Subtask} {h₀ : σ} {k : Nat} {u π : Store Nat}
    (R : ReadyL P l.toW Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k) (j : Fin l.imp.exports.length)
    {vs : List IVal} (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    {m' : Machine.Config (E3 P) σ} {out : CallOutcome}
    (hcalls : Calls prof (fun _ _ => false) (DI P impl) (readyCfgL cs ιe ιi fs G ST h₀)
      ⟨k⟩ ⟨l.host.length + l.exp.exports.length + j⟩ (vs.map toRefVal) m' out) :
    ∃ (d : Linked2.SessRound l.toL2 Ii) (u₁ π₁ : Store Nat) (s' : σ) (o : Option (List IVal)),
      d.j = j ∧ d.vs = vs ∧ d.Ok ∧ Ii.Path P (.idle u) d.instMoves (.idle u₁) ∧
      HLinked2.ExpRunH P l Ie π d.dss.flatten π₁ ∧ HostRun g h₀ (l.hostCalls d.dss.flatten) s' ∧
      d.ans = o.map .vals ∧ BackOutH P l Ie Ii s₀ u₀ F₀ fs k m' u₁ π₁ s' o out := by
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
  have hfj : fs[l.host.length + l.exp.exports.length + j]? = some (.lifted
      (s₀.funcs.length + Ii.addr f.1) (liftedFt l.imp.exports[j]) {} ⟨2⟩) := ha ▸ hfs j
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atLKTS (impl := impl) prof cs ιe
    ιi fs G ST h₀ k (l.host.length + l.exp.exports.length + j) _ l.imp.exports[j] vs hpf hvs hmax
    hres hmaxr hrf R.thI R.leave hfj
  have S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀) := S₀.move R.inv.wfI (hat.funcs.trans hB₀.symm)
  have hF := gframe_of hat
  have hI₀ : LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1)
        (lowerArgs l.imp.exports[j].ty.params vs)) (u, Ii.initThread f) π :=
    linv_ready R.inv hf₂ rfl
  have hck : checkLower l.imp.exports[j].ty.params vs =
      some (lowerArgs l.imp.exports[j].ty.params vs) := by
    simp only [checkLower, hvs, ↓reduceIte]
  obtain ⟨tr, hs, hev, -, ho⟩ := hcalls
  obtain ⟨m₂, st, r₁⟩ := Steps.cons_iff.mp hs
  have r₀ : Steps prof (fun _ _ => false) (DI P impl) (invokedAtL cs ιe ιi fs G ST h₀ k
      (l.host.length + l.exp.exports.length + j) (vs.map toRefVal)) tr m' := invoke_invL st ▸ r₁
  rcases hpre.inv r₀ with hl | ⟨tr'', e, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  have hstart : M₀ = coreCfg (extG M₀ ιe [] [] [] [] M₀.conts h₀) th K segs rest
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1)
        (lowerArgs l.imp.exports[j].ty.params vs)) := by
    have e := hat.start
    rw [extN_eq_extG] at e
    rw [← hat.host]
    exact e
  rw [hstart] at r'
  have hev' : ∀ ev, Label.host ev ∈ tr'' → CallHostEvent ⟨k⟩ ev :=
    fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
  obtain ⟨rs, dss, π₁, s', hrel, hexp, hhr, hend⟩ := rounds_invH (prof := prof) S hF
    (hHd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hat S.hostFn) hT R.inv
    (cid := ⟨k⟩) tr''.length ιe [] [] [] [] M₀.conts h₀ _ (u, Ii.initThread f) π tr'' m' out
    le_rfl R.thE hI₀ r' ho
  have hok : (⟨j, vs, f, rs, .trap, dss⟩ : Linked2.SessRound l.toL2 Ii).Ok :=
    ⟨_, hck, hf₁, hf₂, hrel⟩
  rcases hend with ⟨ιe', SL', CL', TL', HL', C', pre, lb, m₁, tr₂, y, ⟨zs', zt⟩, htr, hte', hnco,
    hx', r₂, hIz, hk'⟩ | ⟨u₁, hout, hRd, hh, hpath⟩
  swap
  · -- the call traps inside the round
    subst hout
    exact ⟨⟨j, vs, f, rs, .trap, dss⟩, u₁, π₁, s', none, rfl, rfl, hok,
      .cons (.call u f) hpath, hexp, hhr, rfl, rfl, hRd, hh⟩
  have hev₂ : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨k⟩ ev :=
    fun ev hm => hev' ev (htr ▸ List.mem_append_right _ hm)
  obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hIz.rel
  obtain ⟨ts, hs', ht⟩ := LInv.typedH S hIz
  rcases hx' with ⟨zs, hst, -, hm₁⟩ | ⟨hst, -, hm₁⟩ | ⟨h', ys', hc'⟩
  · -- the importer returns values
    have r₃ : Steps prof (fun _ _ => false) (DI P impl)
        (retCfg (extG M₀ ιe' SL' CL' TL' HL' C' s') th K segs rest y zs) tr₂ m' := hm₁ ▸ r₂
    obtain ⟨cvs, hcode, hm⟩ := status_values hst
    have hc : (y.2.config (Store.mapH (gL P l.toW) y.1)).code =
        Silmaril.Wasm.Execution.Core.vals cvs :=
      (config_code_mapH (gL P l.toW) y.1 y.2).trans hcode
    obtain ⟨vs', hv, hvm⟩ := values_back P hL hs' ht hc
    have hm' : (vs'.map (linkMap s₀ ρc).val).mapM Silmaril.Wasm.SingleThreaded.toFlat? =
        some zs := by
      rw [hvm]
      exact hm
    have hid := map_val_of_mapM _ hm'
    have hvs' : vs' = cvs := hid.symm.trans hvm
    have hr : Silmaril.Wasm.Game.ResultAt zs' zt (.values cvs) := hvs' ▸ hv
    obtain ⟨w, hw, -⟩ := Silmaril.Wasm.Game.ScalarInstance.sanswer_of_run S.impWf
      (valEnv_throwsBelow Ii _) hIz.run hr
    have hpath := hk' [.inr (.ans f w)] (.idle zs')
      (fun _ _ hr' => .cons (.oret hr' hr hw) (.nil _))
    have hok' : (⟨j, vs, f, rs, w, dss⟩ : Linked2.SessRound l.toL2 Ii).Ok :=
      ⟨_, hck, hf₁, hf₂, hrel⟩
    have hty : zs.map (·.type) = ValTy.flatList l.imp.exports[j].ty.results :=
      results_typed hft' hw hm
    have hR : (answerPayload w).bind
        (Silmaril.Wasm.Component.Adapter.up (.lift l.imp.exports[j].ty)) =
          (liftArgs l.imp.exports[j].ty.results zs).map .vals :=
      lifted_answer hw hm
    cases hl : liftArgs l.imp.exports[j].ty.results zs with
    | some ws =>
      obtain ⟨C'', hRes⟩ := hat.retG ιe' SL' CL' TL' HL' C' s' y zs ws hty hl
      obtain ⟨hout, rfl⟩ := out_of_resolvesL hRes
        (result?_nextG R.fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _) r₃ hev₂ ho
      subst hout
      refine ⟨⟨j, vs, f, rs, w, dss⟩, zs', π₁, s', some ws, rfl, rfl, hok',
        .cons (.call u f) hpath, hexp, hhr, ?_, ws, rfl, rfl, _, _, _, _, _, rfl,
        ⟨lready_after R.inv hIz, hte', threadsOk_after _ _,
          (removeThread_enter_mayLeave _ _).trans R.leave, fresh_nextG R.fresh _ _ _ _ _ _ _ _⟩⟩
      show (answerPayload w).bind _ = _
      rw [hR, hl]
    | none =>
      obtain ⟨hout, hcore', hhost'⟩ :=
        trapsAtSH_out (hat.trapGH ιe' SL' CL' TL' HL' C' s' y zs hty hl) r₃ ho
      subst hout
      refine ⟨⟨j, vs, f, rs, w, dss⟩, zs', π₁, s', none, rfl, rfl, hok',
        .cons (.call u f) hpath, hexp, hhr, ?_, rfl, ?_, hhost'⟩
      · show (answerPayload w).bind _ = _
        rw [hR, hl]
      · rw [hcore']
        exact lready_after R.inv hIz
  · -- the importer's core activation traps
    have r₃ : Steps prof (fun _ _ => false) (DI P impl)
        (trapCfg (coreCfg (extG M₀ ιe' SL' CL' TL' HL' C' s') th K segs rest y)) tr₂ m' :=
      hm₁ ▸ r₂
    have e₃ := steps_of_locked rfl rfl r₃
    subst e₃
    have hout := holds_trapCfgD ho
    subst hout
    have hr : Silmaril.Wasm.Game.ResultAt zs' zt .trap := by
      rcases status_trap hst with hc | ⟨a, hc⟩
      · exact trap_back P hL hs' ht ((config_code_mapH (gL P l.toW) y.1 y.2).trans hc)
      · exact (throwing_back P hL hs' ht ((config_code_mapH (gL P l.toW) y.1 y.2).trans hc)).elim
    obtain ⟨w, hw, -⟩ := Silmaril.Wasm.Game.ScalarInstance.sanswer_of_run S.impWf
      (valEnv_throwsBelow Ii _) hIz.run hr
    have hpath := hk' [.inr (.ans f w)] (.idle zs')
      (fun _ _ hr' => .cons (.oret hr' hr hw) (.nil _))
    exact ⟨⟨j, vs, f, rs, w, dss⟩, zs', π₁, s', none, rfl, rfl, ⟨_, hck, hf₁, hf₂, hrel⟩,
      .cons (.call u f) hpath, hexp, hhr, lifted_trap (fun _ h => by cases h) hw, rfl,
      lready_after R.inv hIz, rfl⟩
  · exact absurd hc' (hnco h' ys')

end Call

/-! ## Sessions between calls -/

section Sess

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) σ}
  {fs : List (CFuncInst (core3P P))}

/-- **Resumable sessions between calls are specification sessions**, their host calls answered
by `g` from the host state between calls to the final host state. -/
theorem sessH_inv {impl : HostImpl (E3 P) σ} (hHd : HandlesB prof P impl g l)
    (hT : l.HostTyped g) (S₀ : HStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀))
    (hB₀ : B₀.store.funcs = fs) (hfs : LiftedOkH l Ii s₀ fs) :
    ∀ (calls : List (Fin l.imp.exports.length × List IVal))
      (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState) (G : Garb P σ)
      (ST : List Subtask) (h₀ : σ) (u π : Store Nat) (k : Nat) (outs : List (Option (List RVal)))
      (mE : Machine.Config (core3P P) σ),
      ReadyL P l.toW Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k → SimpleI.TypedCalls l.imp calls →
      LinkedSession.SessRun prof (linkHost impl) (readyCfgL cs ιe ιi fs G ST h₀) k
        (callArgsH l calls) outs mE →
      ∃ (outs' : List (Option (List IVal)))
        (hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))) (u' π' : Store Nat),
        HLinked2.SessSpec P l Ie Ii u π calls outs' hs u' π' ∧ HostRun g h₀ hs.flatten mE.host ∧
        outs = refOuts outs'
  | [], cs, ιe, ιi, G, ST, h₀, u, π, k, outs, mE, _, _, hS => by
    cases hS
    exact ⟨[], [], u, π, .nil u π, .nil _, rfl⟩
  | (j, vs) :: calls, cs, ιe, ιi, G, ST, h₀, u, π, k, outs, mE, R, ht, hS => by
    have hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true := ht _ List.mem_cons_self
    have ht' : SimpleI.TypedCalls l.imp calls := fun q hq => ht q (List.mem_cons_of_mem _ hq)
    cases hS with
    | ret hcall hS' =>
      obtain ⟨d, u₁, π₁, s', o, rfl, rfl, hok, hpath, hexp, hhr, hans, hout⟩ :=
        linkCall_invH hHd hT S₀ hB₀ hfs R j hvs hcall
      obtain ⟨ws, rfl, rfl, cs₁, ιe₁, ιi₁, G₁, ST₁, rfl, R₁⟩ := hout
      obtain ⟨outs', hs, u', π', hspec, hhr', rfl⟩ :=
        sessH_inv hHd hT S₀ hB₀ hfs calls cs₁ ιe₁ ιi₁ G₁ ST₁ s' u₁ π₁ (k + 1) _ mE R₁ ht' hS'
      exact ⟨some ws :: outs', l.hostCalls d.dss.flatten :: hs, u', π',
        .round d hok hpath hexp hans hspec, hostRun_append hhr hhr', rfl⟩
    | trap hcall hS' =>
      obtain ⟨d, u₁, π₁, s', o, rfl, rfl, hok, hpath, hexp, hhr, hans, hout⟩ :=
        linkCall_invH hHd hT S₀ hB₀ hfs R j hvs hcall
      obtain ⟨rfl, hR', hhost⟩ := hout
      have R₁ : ReadyL P l.toW Ie Ii s₀ u₀ F₀ _ ιe ιi G u₁ π₁ (k + 1) :=
        ⟨hR', R.thE, R.thI, R.leave, fresh_succL R.fresh⟩
      rw [resumeCfg_readyL, hhost] at hS'
      obtain ⟨outs', hs, u', π', hspec, hhr', rfl⟩ :=
        sessH_inv hHd hT S₀ hB₀ hfs calls _ ιe ιi G ST s' u₁ π₁ (k + 1) _ mE R₁ ht' hS'
      exact ⟨none :: outs', l.hostCalls d.dss.flatten :: hs, u', π',
        .round d hok hpath hexp hans hspec, hostRun_append hhr hhr', rfl⟩

end Sess

/-! ## Assembly -/

/-- **Reference sessions of an `HLinked2` with a typed host are specification sessions**, with
the host state and log: every session observation `(o, st')` of `l.toRef` under the logging
host of `g` from `(s₀, [])` (`HLinked2.sessObs`), for typed calls, is the reference image of the
outcomes of an `HLinked2.SessSpec` session from the instances' stores whose host calls are
answered by the logging host of `g` from `(s₀, [])` to `st'` (`HostRun (logG g)`). -/
theorem hlinked2_sess_refToSpec (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) (s₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal))
    (ht : SimpleI.TypedCalls l.imp calls) {o : List (Option (List RVal))}
    {st' : σ × List HLinked2.HostEvent} (ho : (o, st') ∈ HLinked2.sessObs P prof l g s₀ calls) :
    ∃ (Ie Ii : Silmaril.Wasm.Game.ScalarInstance) (outs : List (Option (List IVal)))
      (hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))) (u' π' : Store Nat),
      l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
      HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u' π' ∧
      HostRun (HLinked2.logG g) (s₀, []) hs.flatten st' ∧ o = refOuts outs := by
  obtain ⟨Ie, cse, cie, hFe⟩ := coreFacts (Pf := P) hl.expGood hl.expInst
  obtain ⟨Ii, hIi⟩ := hl.impInst.inst
  obtain ⟨m, F₀, cs, fs, hmem, rfl, S₀, hfs, R₀⟩ :=
    init_facts P prof hl (answerHostS P (HLinked2.logG g)) (s₀, []) hFe.isInst hIi
  obtain ⟨mU, -, -, -, huniq⟩ :=
    hlinked2_instantiates P prof hl (answerHostS P (HLinked2.logG g)) (s₀, [])
  obtain ⟨m₀, inst, es, fs', mE, hr, hfs', hSq, hst⟩ := ho
  have h₁ := huniq _ hmem
  have h₂ := huniq _ hr
  simp only [InstResult.instance.injEq] at h₁ h₂
  obtain ⟨rfl, rfl, rfl⟩ := h₂
  rw [← h₁.1] at hSq
  have hfs'' : fs' = calls.map fun q => (⟨l.host.length + l.exp.exports.length + q.1⟩ : FuncId) :=
    Option.some.inj (hfs'.symm.trans (mapM_lookupH hl.impGood calls))
  subst hfs''
  rw [zip_callArgsH] at hSq
  obtain ⟨outs, hs, u', π', hspec, hhr, ho'⟩ := sessH_inv (prof := prof)
    (impl := answerImplS (HLinked2.logG g))
    (handlesB_answer hl.impArity hl.impFloatFree hl.wireTy) (HostTyped.logG hT) S₀
    rfl hfs calls _ _ _ _ _ (s₀, []) _ _ 0 _ mE R₀ ht hSq
  exact ⟨Ie, Ii, outs, hs, u', π', hFe.isInst, hIi, hspec, (show st' = mE.host from hst) ▸ hhr, ho'⟩

/-- **The session observations of an `HLinked2` with a typed host are exactly the
specification sessions with their host runs**, for typed calls. -/
theorem hlinked2_sessObs_eq (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) (s₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal))
    (ht : SimpleI.TypedCalls l.imp calls) :
    HLinked2.sessObs P prof l g s₀ calls =
      {p | ∃ (Ie Ii : Silmaril.Wasm.Game.ScalarInstance) (outs : List (Option (List IVal)))
        (hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))) (u' π' : Store Nat),
        l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
        HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u' π' ∧
        HostRun (HLinked2.logG g) (s₀, []) hs.flatten p.2 ∧ p.1 = refOuts outs} := by
  ext ⟨o, st'⟩
  constructor
  · intro ho
    exact hlinked2_sess_refToSpec P prof hl g hT s₀ calls ht ho
  · rintro ⟨Ie, Ii, outs, hs, u', π', hIe, hIi, hspec, hhr, rfl⟩
    exact hlinked2_sess_specToRef P prof hl g hT s₀ hIe hIi hspec hhr

/-! ## A host that never answers -/

/-- **The host that never answers handles the host callouts, backward**: a callout whose
arguments do not lift traps (`hostCall_noLiftGS`); any other is a live deterministic run that
blocks the importer's thread on the unresolved subtask, after which the synchronous lift loop
of the call traps `cannotBlockSync` (`CallAtLKTS.blockH`), at the callout's core store and host
state; `silentG` never answers. -/
theorem handlesB_silent {l : HLinked2} (har : l.imp.Arity) (hff : l.imp.FloatFree)
    (hW : l.WireTy) : HandlesB prof P (HLinked2.silentImpl (σ := σ)) HLinked2.silentG l := by
  intro cs ιe₀ ιi fs G ST h₀ k j x a vs M₀ th K segs rest hat hfn ιe SL CL TL HL C h y i hi ys
    hst hys
  have hF := gframe_of hat
  have hmem := host_mem hW hi
  obtain ⟨hmaxp, -, -⟩ := har.2 _ hmem
  obtain ⟨hpf, -⟩ := hff.2 _ hmem
  obtain ⟨ι₂, hι₂, hleave⟩ := hF.inst2 ιe SL CL TL HL C h
  have hf : ArenaField.funcs.get? (extG M₀ ιe SL CL TL HL C h).store ⟨i⟩ =
      some (.host (witFt l.host[i].2) ⟨i⟩) := (funcs_extG _ _ _ _ _ _ _ _ _).trans (hfn i hi)
  have hentry := hF.entry ⟨i⟩ (witFt l.host[i].2) ιe SL CL TL HL C h
  refine ⟨fun hws => hostCall_noLiftGS (fun _ => ⟨_, rfl⟩) rfl hst hentry hι₂ hleave hf hpf hys
    hmaxp hws, fun ws hws => ⟨fun _ => ?_, fun us s' hg => by cases hg⟩⟩
  have hth := hat.thread
  subst hth
  let M₁ := coreCfg (extG M₀ ιe SL CL TL HL C h) (some ⟨G.threads.length⟩) K segs rest y
  have s₃ : UniqueStep prof (fun _ _ => false) (DI P HLinked2.silentImpl) M₁ .tau
      { M₁ with ctl := ⟨some ⟨G.threads.length⟩,
        .prog (DI P HLinked2.silentImpl
          (.hostCallout (.lowered ⟨i⟩ (witFt l.host[i].2) {} ⟨2⟩) ys)),
        .core y.2 K :: segs⟩ :: rest } :=
    UniqueStep.of_core rfl (callout_status_ne hst) (Step.coreCallout rfl hst)
  obtain ⟨pos, trB, hB⟩ := blocks_callout_silent (t := ⟨G.threads.length⟩) (m := M₁) hentry hι₂
    hleave hf hpf hys hmaxp hws
  obtain ⟨kB, segsB, rB⟩ := hB.lrun (prof := prof) (hr := fun _ _ => false) rfl Prog.pure
    (.core y.2 K :: segs) rest
  rw [Prog.bind_eq, Prog.bind_pure] at rB
  let mB : Machine.Config (E3 P) σ :=
    { M₁ with store := silentSt M₁.store ⟨2⟩ ys l.host[i].2 pos ⟨G.threads.length⟩ }
  have hlB : Live ({ mB with ctl := ⟨some ⟨G.threads.length⟩,
      .prog (.op (S := Eff (E3 P) σ) (.block none) kB), segsB⟩ :: rest } :
        Machine.Config (E3 P) σ) :=
    ⟨List.cons_ne_nil _ _, rfl⟩
  let M₂ : Machine.Config (E3 P) σ :=
    { (mB.setCont ⟨G.threads.length⟩ (some (blockedAct ⟨G.threads.length⟩ kB segsB))) with
      store := threadStatusSt ⟨G.threads.length⟩ .blocked mB.store, ctl := rest }
  have s₄ : UniqueStep prof (fun _ _ => false) (DI P HLinked2.silentImpl)
      { mB with ctl := ⟨some ⟨G.threads.length⟩,
        .prog (.op (S := Eff (E3 P) σ) (.block none) kB), segsB⟩ :: rest } .tau M₂ :=
    UniqueStep.of_prog rfl (notChoose_of rfl) (Step.block rfl)
  have hready : M₂.store.threadReady (fun _ => false) ⟨G.threads.length⟩ = false :=
    threadReady_blocked _ _ _ _ (silent_unresolved M₁.store ⟨2⟩ ys l.host[i].2 pos)
  have hinst : M₂.store.inst? ⟨2⟩ = some (enterInst ιi ⟨G.threads.length⟩) := by
    show (extG M₀ ιe SL CL TL HL C h).store.insts[2]? = _
    simp [extG, hat.insts]
    rfl
  have htasks : M₂.store.tasks = G.tasks ++
      [(taskK₁ x G.callers ⟨G.threads.length⟩).withState .started] ++ TL := by
    show M₀.store.tasks ++ TL = _
    rw [hat.tasks]
  obtain ⟨tr₃, mT, hrun, hl, hu, hc, hh⟩ := hat.blockH M₂ _ _ rfl rfl htasks (by
    intro h
    cases h) (instCandidates_enter hinst hready)
  exact ⟨_, mT, .cannotBlockSync, (fun _ h => by cases h),
    .cons ⟨List.cons_ne_nil _ _, rfl⟩ s₃ (rB.trans (.cons hlB s₄ hrun)), hl, hu, hc, hh⟩

/-- Under `silentG` every host call traps and the host state never changes. -/
theorem hostRun_silentG_eq {n : Nat} {s s' : σ} :
    ∀ {ds : List (Σ _ : (sigN n).Op, Option Payload)}, HostRun HLinked2.silentG s ds s' → s' = s
  | [], h => (hostRun_nil h).symm
  | _ :: _, .cons hd h => by
    obtain ⟨k, ws, -, hans⟩ := hd
    revert hans
    split
    · rintro ⟨-, rfl⟩
      exact hostRun_silentG_eq h
    · intro hans
      cases hans
    · intro hans
      exact hans.elim

/-- **Reference sessions under a host that never answers are specification sessions whose host
calls all trap**, the host state unchanged: every session observation `(o, s)` of `l.toRef`
under `silentHost` from `h₀` (`HLinked2.silentObs`), for typed calls, has `s = h₀` and is the
reference image of the outcomes of an `HLinked2.SessSpec` session from the instances' stores
whose host calls are all answered by a trap (`HostRun silentG`). -/
theorem hlinked2_silent_refToSpec (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (h₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal))
    (ht : SimpleI.TypedCalls l.imp calls) {o : List (Option (List RVal))} {s : σ}
    (ho : (o, s) ∈ HLinked2.silentObs P prof l h₀ calls) :
    ∃ (Ie Ii : Silmaril.Wasm.Game.ScalarInstance) (outs : List (Option (List IVal)))
      (hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))) (u' π' : Store Nat),
      l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
      HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u' π' ∧
      HostRun HLinked2.silentG h₀ hs.flatten h₀ ∧ s = h₀ ∧ o = refOuts outs := by
  obtain ⟨Ie, cse, cie, hFe⟩ := coreFacts (Pf := P) hl.expGood hl.expInst
  obtain ⟨Ii, hIi⟩ := hl.impInst.inst
  obtain ⟨m, F₀, cs, fs, hmem, rfl, S₀, hfs, R₀⟩ :=
    init_facts P prof hl (HLinked2.silentHost P) h₀ hFe.isInst hIi
  obtain ⟨mU, -, -, -, huniq⟩ := hlinked2_instantiates P prof hl (HLinked2.silentHost P) h₀
  obtain ⟨m₀, inst, es, fs', mE, hr, hfs', hSq, hst⟩ := ho
  have h₁ := huniq _ hmem
  have h₂ := huniq _ hr
  simp only [InstResult.instance.injEq] at h₁ h₂
  obtain ⟨rfl, rfl, rfl⟩ := h₂
  rw [← h₁.1] at hSq
  have hfs'' : fs' = calls.map fun q => (⟨l.host.length + l.exp.exports.length + q.1⟩ : FuncId) :=
    Option.some.inj (hfs'.symm.trans (mapM_lookupH hl.impGood calls))
  subst hfs''
  rw [zip_callArgsH] at hSq
  obtain ⟨outs, hs, u', π', hspec, hhr, ho'⟩ := sessH_inv (prof := prof)
    (impl := HLinked2.silentImpl) (handlesB_silent hl.impArity hl.impFloatFree hl.wireTy)
    (HostTyped.silentG l) S₀ rfl hfs calls _ _ _ _ _ h₀ _ _ 0 _ mE R₀ ht hSq
  have hs₀ : mE.host = h₀ := hostRun_silentG_eq hhr
  have hs' : s = h₀ := (show s = mE.host from hst).trans hs₀
  exact ⟨Ie, Ii, outs, hs, u', π', hFe.isInst, hIi, hspec, hs₀ ▸ hhr, hs', ho'⟩

/-- **The session observations under a host that never answers are exactly the specification
sessions whose host calls all trap**, in the initial host state, for typed calls. -/
theorem hlinked2_silentObs_eq (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (h₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal))
    (ht : SimpleI.TypedCalls l.imp calls) :
    HLinked2.silentObs P prof l h₀ calls =
      {p | ∃ (Ie Ii : Silmaril.Wasm.Game.ScalarInstance) (outs : List (Option (List IVal)))
        (hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))) (u' π' : Store Nat),
        l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
        HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u' π' ∧
        HostRun HLinked2.silentG h₀ hs.flatten h₀ ∧ p.2 = h₀ ∧ p.1 = refOuts outs} := by
  ext ⟨o, s⟩
  constructor
  · intro ho
    exact hlinked2_silent_refToSpec P prof hl h₀ calls ht ho
  · rintro ⟨Ie, Ii, outs, hs, u', π', hIe, hIi, hspec, hhr, rfl, rfl⟩
    exact hlinked2_silent_specToRef P prof hl s hIe hIi hspec hhr

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
