module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Round
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Host
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.Call

/-!
# Forward runs of a call of `HLinked2.toRef` with host calls answered

A specification round of the importer (`SessRound.Ok`, the instance's path, the component import
calls an `HLinked2.ExpRunH` segment of the exporter) whose host calls are answered by a host
`impl` as the stateful answering function `g` prescribes (`HostRun g` on `HLinked2.hostCalls`)
is a call of the reference machine. The frame of the call grows by nested calls (`extN`) and by
host callouts, so the configurations along the round are `extG` extensions of it (`TrapH`).

* `HostHandles impl g l M₀ th K segs rest`: what the host does at a host callout of the importer
  in every `extG` extension of the call's frame: arguments that do not lift trap; when `g` has
  no answer the call traps; a well-typed answer of `g` resumes the importer's activation with the
  lowered answer, quietly, in the new host state and with one more subtask and caller record.
  `Handles impl g l` asks this of every call's frame (`CallAtLKTS`); `handles_answer` proves it
  for `answerImplS g`;
* `nest_retG`: a returned nested call to the exporter is a nonempty quiet run between `extG`
  extensions;
* `LInv.expTrap_fwdH`: `LInv.expTrap_fwd` at the host-first layout;
* `rounds_fwdH`: from `LInv`, the round is a quiet run of the machine to the end of the importer's
  part (`LInv` at the exporter's end store, the host state at the end of `HostRun`), or a trap
  (`TrapEndH`, with `LReady` at the trapped core store and the host state of the trap): a trap of
  a nested call, a host call whose arguments do not lift or that the host does not answer;
* `linkCall_fwdG`, `linkCall_fwdH`: one call between calls (`ReadyL` at `l.toW`), as `FwdOutH`:
  a resolved call ending between calls with `ReadyL` again, or a trapped call with `LReady` at the
  trapped core store and the final host state. The host answers must be well typed
  (`HLinked2.HostTyped`): an ill-typed answer is an `internal` fault, not a trap (`Host`).
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
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}
  {g : σ → HostFuncId → List RVal → Option (List RVal × σ)}

/-! ## Host calls of the specification -/

/-- A host call of the importer's import `k` is the host call `k - wire.length`. -/
theorem hostCalls_cons_host {l : HLinked2}
    {d : Σ _ : (sigN l.imp.imports.length).Op, Option Payload}
    {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
    (hw : l.wire.length ≤ d.1.1.val) (hi : d.1.1.val - l.wire.length < l.host.length) :
    l.hostCalls (d :: ds) = ⟨(⟨d.1.1.val - l.wire.length, hi⟩, d.1.2), d.2⟩ :: l.hostCalls ds := by
  have hs : l.hostCall? d = some ⟨(⟨d.1.1.val - l.wire.length, hi⟩, d.1.2), d.2⟩ := by
    unfold HLinked2.hostCall?
    split_ifs with h
    · rfl
    · exact absurd ⟨hw, hi⟩ h
  exact List.filterMap_cons_some hs

/-- A `HostRun` of no calls keeps the host state. -/
theorem hostRun_nil {n : Nat} {s s' : σ}
    (h : HostRun g s ([] : List (Σ _ : (sigN n).Op, Option Payload)) s') : s = s' := by
  cases h
  rfl

/-- A `HostRun` of concatenated calls splits at an intermediate host state. -/
theorem hostRun_split {n : Nat} {s s₂ : σ} :
    ∀ {ds₁ ds₂ : List (Σ _ : (sigN n).Op, Option Payload)},
      HostRun g s (ds₁ ++ ds₂) s₂ → ∃ s₁, HostRun g s ds₁ s₁ ∧ HostRun g s₁ ds₂ s₂
  | [], _, h => ⟨s, .nil s, h⟩
  | _ :: _, _, .cons hd h => by
    obtain ⟨s₁, h₁, h₂⟩ := hostRun_split h
    exact ⟨s₁, .cons hd h₁, h₂⟩

/-! ## What the host does at a host callout -/

/-- **The host at a host callout** of the importer, in every `extG` extension of the frame `M₀`
of a call: a callout of host function `i` whose flat arguments do not lift traps; one that `g`
does not answer traps; a well-typed answer `us` of `g`, moving the host state to `s'`, resumes
the importer's activation with the lowered answer, quietly, in host state `s'` and with one more
subtask and caller record. -/
def HostHandles (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (l : HLinked2)
    (M₀ : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) : Prop :=
  ∀ (ιe : InstState) (SL : List Subtask) (CL : List (Caller (E3 P)))
    (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
    (C : List (Option (Activation (E3 P) σ))) (h : σ) (y : CoreSt (E3 P)) (i : Nat)
    (hi : i < l.host.length) (ys : List Flat),
    (E3 P).status y.1 y.2 = .callout (.lowered ⟨i⟩ (witFt l.host[i].2) {} ⟨2⟩) ys →
    ys.map (·.type) = ValTy.flatList l.host[i].2.params →
    (liftArgs l.host[i].2.params ys = none →
      TrapEndH prof P impl (coreCfg (extG M₀ ιe SL CL TL HL C h) th K segs rest y) y.1 h) ∧
    ∀ ws, liftArgs l.host[i].2.params ys = some ws →
      (g h ⟨i⟩ (ws.map toRefVal) = none →
        TrapEndH prof P impl (coreCfg (extG M₀ ιe SL CL TL HL C h) th K segs rest y) y.1 h) ∧
      ∀ (us : List Silmaril.Wasm.Component.Val) (s' : σ),
        g h ⟨i⟩ (ws.map toRefVal) = some (us.map toRefVal, s') →
        ValTy.checkList l.host[i].2.results us = true →
        ∃ (x : Subtask) (c : Caller (E3 P)) (tr : List (Label (E3 P) σ)), Quiet tr ∧
          Steps prof (fun _ _ => false) (DI P impl)
            (coreCfg (extG M₀ ιe SL CL TL HL C h) th K segs rest y) tr
            (coreCfg (extG M₀ ιe (SL ++ [x]) (CL ++ [c]) TL HL C s') th K segs rest
              (y.1, (E3 P).resume y.1 y.2 (.values (lowerArgs l.host[i].2.results us))))

/-- **The host handles the host callouts of every call**: `HostHandles` at the frame of every
call (`CallAtLKTS`, as `call_atLKTS` gives it) whose component functions `0, …, k - 1` are the
host functions of `l.host`. -/
def Handles (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (l : HLinked2) : Prop :=
  ∀ (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) (h₀ : σ) (k j : Nat)
    (x : SimpleExport) (a : Nat) (vs : List Silmaril.Wasm.Component.Val)
    (M₀ : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)),
    CallAtLKTS prof P impl cs ιe (enterInst ιi ⟨G.threads.length⟩) fs G ST h₀ k j x a vs M₀ th K
      segs rest →
    (∀ (i : Nat) (hi : i < l.host.length),
      ArenaField.funcs.get? M₀.store ⟨i⟩ = some (.host (witFt l.host[i].2) ⟨i⟩)) →
    HostHandles prof P impl g l M₀ th K segs rest

/-- The host import `i` is an import of the importer. -/
theorem host_mem {l : HLinked2} (hW : l.WireTy) {i : Nat} (hi : i < l.host.length) :
    l.host[i] ∈ l.imp.imports := by
  have h₁ : l.host[i] ∈ l.imp.imports.drop l.wire.length := by
    rw [hW.shape.1]
    exact List.getElem_mem hi
  exact List.mem_of_mem_drop h₁

/-- **The answering host handles the host callouts** (`hostCall_fwd`, `hostCall_noAnswerH`,
`hostCall_noLiftG`). -/
theorem handles_answer {l : HLinked2} (har : l.imp.Arity) (hff : l.imp.FloatFree)
    (hW : l.WireTy) : Handles prof P (answerImplS g) g l := by
  intro cs ιe₀ ιi' fs G ST h₀ k j x a vs M₀ th K segs rest hat hfn ιe SL CL TL HL C h y i hi ys
    hst hys
  have hF := gframe_of hat
  have hmem := host_mem hW hi
  obtain ⟨hmaxp, hmaxr, hres⟩ := har.2 _ hmem
  obtain ⟨hpf, hrf⟩ := hff.2 _ hmem
  obtain ⟨ι₂, hι₂, hleave⟩ := hF.inst2 ιe SL CL TL HL C h
  have hf : ArenaField.funcs.get? (extG M₀ ιe SL CL TL HL C h).store ⟨i⟩ =
      some (.host (witFt l.host[i].2) ⟨i⟩) := (funcs_extG _ _ _ _ _ _ _ _ _).trans (hfn i hi)
  have hentry := hF.entry ⟨i⟩ (witFt l.host[i].2) ιe SL CL TL HL C h
  refine ⟨fun hws => hostCall_noLiftG (fun _ => ⟨_, rfl⟩) rfl hst hentry hι₂ hleave hf hpf hys
    hmaxp hws, fun ws hws => ⟨fun hg => hostCall_noAnswerH rfl hst hentry hι₂ hleave hf hpf hys
    hmaxp hws hg, fun us s' hg hus => ?_⟩⟩
  obtain ⟨pos, tr, hq, r⟩ := hostCall_fwd (prof := prof) rfl hst hentry hι₂ hleave hf hpf hys hmaxp
    hws hg hres hrf hus hmaxr
  rw [extG_hostCall] at r
  exact ⟨_, _, tr, hq, r⟩

/-! ## Nested calls between `extG` extensions -/

section Nest

variable {M₀ : Machine.Config (E3 P) σ} {th : Option ThreadId}
  {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
  {rest : List (Activation (E3 P) σ)}

/-- A link site of the frame is a link site of its `extG` extensions. -/
theorem linkSite_extG {y : CoreSt (E3 P)} {h : CanonHost (E3 P)} {ys : List Flat}
    (hS : LinkSite M₀ y h ys) (ιe : InstState) (SL : List Subtask) (CL : List (Caller (E3 P)))
    (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
    (C : List (Option (Activation (E3 P) σ))) (s : σ) :
    LinkSite (extG M₀ ιe SL CL TL HL C s) y h ys := ⟨hS.site⟩

/-- **A returned nested call is a nonempty quiet run between `extG` extensions.** -/
theorem nest_retG (hF : GFrame M₀ th) {ιe : InstState} {SL : List Subtask}
    {CL : List (Caller (E3 P))} {TL : List (Runtime.Task (E3 P))} {HL : List Runtime.Thread}
    {C : List (Option (Activation (E3 P) σ))} {s : σ} (hte : ThreadsOk ιe) {y e : CoreSt (E3 P)}
    {f : FuncId} {a : (E3 P).FuncAddr} {p : FuncTy} {ys zs : List Flat}
    {ws us : List Silmaril.Wasm.Component.Val}
    (hs : (E3 P).status y.1 y.2 = .callout (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hf : ArenaField.funcs.get? M₀.store f = some (.lifted a (witFt p) {} ⟨1⟩))
    (hr : p.results.length ≤ 1) (hS : LinkSite M₀ y (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hws : liftArgs p.params ys = some ws)
    (he : Relation.ReflTransGen (CoreStep (E3 P))
      (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) e)
    (hst : (E3 P).status e.1 e.2 = .returned (.values zs)) (hus : liftArgs p.results zs = some us) :
    ∃ (ιe' : InstState) (SL' : List Subtask) (CL' : List (Caller (E3 P)))
      (TL' : List (Runtime.Task (E3 P))) (HL' : List Runtime.Thread)
      (C' : List (Option (Activation (E3 P) σ))) (tr : List (Label (E3 P) σ)),
      ThreadsOk ιe' ∧ Quiet tr ∧ tr ≠ [] ∧
      Steps prof (fun _ _ => false) (DI P impl)
        (coreCfg (extG M₀ ιe SL CL TL HL C s) th K segs rest y) tr
        (coreCfg (extG M₀ ιe' SL' CL' TL' HL' C' s) th K segs rest
          (e.1, (E3 P).resume e.1 y.2 (.values (lowerArgs p.results us)))) := by
  have hB := hF.lframe ιe SL CL TL HL C s
  obtain ⟨hpf, hys, hmaxp, hrf, hmaxr, hexp⟩ := site_of hS hf hr
  have hf' : ArenaField.funcs.get? (extG M₀ ιe SL CL TL HL C s).store f =
      some (.lifted a (witFt p) {} ⟨1⟩) := (funcs_extG _ _ _ _ _ _ _ _ _).trans hf
  obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe [] C
  have hadd := addThread?_ok hte
    ⟨(extN (extG M₀ ιe SL CL TL HL C s) ιe [] C).store.threads.length⟩
  have hrem := removeThread?_enter ιe
    ⟨(extN (extG M₀ ιe SL CL TL HL C s) ιe [] C).store.threads.length⟩
  obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr₂, hrun, hctl, hcore, hlock, -, hret, -⟩ :=
    nest_atTSH (prof := prof) (impl := impl) (extG M₀ ιe SL CL TL HL C s) ιe _ [] C th K segs rest
      y f a p ys ιi ws hs (hB.entry _ _ _ _ _) hi hleave hf' hB.len hadd hrem hpf hys hmaxp hws
      hr hrf hmaxr
  have hM : M₁ = coreCfg M₁ th' K' segs' rest' (y.1,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) := by
    rw [← hcore]
    exact eq_coreCfg hctl
  obtain ⟨tr₃, htr₃, r₃⟩ := Adequacy.coreCfg_steps_of (prof := prof)
    (hr := fun _ _ => false) (dispatch := DI P impl) (B := M₁) (th := th') (K := K')
    (segs := segs') (rest := rest') he
  have s₄ : Step prof (fun _ _ => false) (DI P impl) (coreCfg M₁ th' K' segs' rest' e) .tau
      (retCfg M₁ th' K' segs' rest' e zs) := Step.coreReturned rfl hst
  have hty : zs.map (·.type) = ValTy.flatList p.results := (hexp ws hws e he).2 zs hst
  obtain ⟨tr₅, h₅⟩ := hret e zs us hty hus
  have hlive₁ : Live M₁ := ⟨by rw [hctl]; exact List.cons_ne_nil _ _, hlock⟩
  have hq : Quiet (tr₂ ++ (tr₃ ++ (.tau :: tr₅))) :=
    (Quiet.of_lrun hrun hlive₁).append ((Quiet.of_core htr₃).append
      ((Quiet.tau (P := P) (σ := σ)).append (Quiet.of_lrun h₅
        (coreCfg_extN_live _ _ _ _ _ _ _ _ _))))
  rw [extN_extG_nil] at hrun
  rw [extN_extG] at h₅
  rw [← hM] at r₃
  have hr := Adequacy.steps_append hrun.steps (Adequacy.steps_append r₃ (.cons s₄ h₅.steps))
  exact ⟨_, _, _, _, _, _, _, threadsOk_after _ _, hq, by simp, hr⟩

end Nest

/-! ## A trapped nested call, forward -/

section Inv

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B : Machine.Config (E3 P) σ} {f : Ii.F.Op}

/-- **A trapped nested call of the specification, forward** (`LInv.expTrap_fwd` at the
`HLinked2` layout). -/
theorem LInv.expTrap_fwdH {u : Store Nat} (S : HStat P l Ie Ii u F₀ B (ownOf s₀))
    {cs : Store (CanonHost (E3 P))} {π : Store Nat} (hR : LReady P l.toW Ie Ii s₀ u₀ F₀ cs u π)
    {y : CoreSt (E3 P)} {x : Store Nat × STh} {π' : Store Nat}
    (hI : LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x π')
    {xe : SimpleExport} (hxe : xe ∈ l.exp.exports) {ws : List Silmaril.Wasm.Component.Val}
    {π₂ : Store Nat} (hT : TrapAt P l.exp Ie xe ws π' π₂) :
    ∃ e : CoreSt (E3 P),
      Relation.ReflTransGen (CoreStep (E3 P))
        (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
          (lowerArgs xe.ty.params ws)) e ∧
      ((E3 P).status e.1 e.2 = .returned .trap ∨
        ∃ zs, (E3 P).status e.1 e.2 = .returned (.values zs) ∧
          zs.map (·.type) = ValTy.flatList xe.ty.results ∧ liftArgs xe.ty.results zs = none) ∧
      LReady P l.toW Ie Ii s₀ u₀ F₀ e.1 x.1 π₂ := by
  have hR' := lready_after hR hI
  obtain ⟨ρp, Op, ρc, Oc, hR4⟩ := hR'.rel
  obtain ⟨t', res, run, final, hout⟩ := hT.run
  obtain ⟨e, ρp', Op', hrun, hLe, hR4', hF', hfe⟩ := exp_fwd (gL P l.toW) (gLInv P l.toW)
    (hostsSat_hstat S hR'.funcs) hR4 hR'.fnE (S.owned xe hxe) (lowerArgs xe.ty.params ws) run
  obtain ⟨nm, hcx⟩ := S.expGood.core xe hxe
  have hk : xe.core < l.exp.mod.exports.length := (List.getElem?_eq_some_iff.mp hcx).1
  have hxs := exp_hxs hcx hT.typed hk
  have steps : Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke π' (Ie.addrs.getD xe.core 0)
        ((lowerArgs xe.ty.params ws).map Silmaril.Wasm.SingleThreaded.ofFlat)) (t'.config π₂) :=
    internalP_steps (H := Nat) run
  have hend : (E3 P).status e.1 e.2 = .returned .trap ∨
      ∃ zs, (E3 P).status e.1 e.2 = .returned (.values zs) ∧
        zs.map (·.type) = ValTy.flatList xe.ty.results ∧ liftArgs xe.ty.results zs = none := by
    cases res with
    | trap => exact .inl (status_of_trap (gL P l.toW) hLe final)
    | throw b => exact (not_result_throw hLe final).elim
    | values cvs =>
      obtain ⟨w, hw⟩ := answer_at S.expInst hR'.wfE hk hxs steps (r := .values cvs) final
      have htyped : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal
          (Ie.exports.get (opAt S.expInst hk hxs).1).results cvs := by
        unfold Silmaril.Wasm.Game.Answer.ofResult? at hw
        dsimp only at hw
        split_ifs at hw with ht
        exact ht
      rw [opAt_type] at htyped
      obtain ⟨zs, hm⟩ : ∃ zs, cvs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some zs :=
        Silmaril.Proofs.Wasm.Component.Core3G.toFlat?_isSome htyped
      have hty : zs.map (·.type) = ValTy.flatList xe.ty.results := by
        have ht := run_typed_at S.expInst hR'.wfE hk hxs steps final hm
        rw [(List.getElem?_eq_some_iff.mp hcx).2] at ht
        exact ht
      have hn : liftArgs xe.ty.results zs = none := by
        simp only [coreRes, hm, liftOutcome] at hout
        revert hout
        cases liftArgs xe.ty.results zs with
        | none => intro _; rfl
        | some _ => intro h; cases h
      exact .inr ⟨zs, status_of_values (gL P l.toW) hLe final hm, hty, hn⟩
  exact ⟨e, hrun, hend, ⟨⟨ρp', Op', ρc, Oc, hR4'⟩, hF',
    hR'.fnC.congr (mapH_funcs_eq _ hfe) rfl, hT.wellFormed S.expInst ⟨nm, hcx⟩ hR'.wfE, hR'.wfI,
    hfe.trans hR'.funcs, hR'.ufuncs, hR'.good⟩⟩

end Inv

/-! ## Rounds -/

/-- How the forward run of a round from `M` ends: a quiet run to the importer's part finished
with the round's answer (`LInv` at the exporter's end store), in an `extG` extension of the frame
in host state `s'`; or a trap (`TrapEndH`, host state `s'`), the round answering a trap and
`LReady` holding at the trapped core store. -/
def RoundEndH (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ) (l : HLinked2)
    (Ie Ii : Silmaril.Wasm.Game.ScalarInstance) (s₀ u₀ u : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (M₀ : Machine.Config (E3 P) σ)
    (th : Option ThreadId) (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P)))
    (segs : List (Seg (E3 P) σ)) (rest : List (Activation (E3 P) σ)) (f : Ii.F.Op)
    (M : Machine.Config (E3 P) σ) (u₁ π₁ : Store Nat) (w : Ii.F.Ar f) (s' : σ) : Prop :=
  (∃ (ιe' : InstState) (SL' : List Subtask) (CL' : List (Caller (E3 P)))
      (TL' : List (Runtime.Task (E3 P))) (HL' : List Runtime.Thread)
      (C' : List (Option (Activation (E3 P) σ))) (tr : List (Label (E3 P) σ)) (yc : CoreSt (E3 P))
      (t' : STh) (r : Silmaril.Wasm.Execution.Core.Result),
    ThreadsOk ιe' ∧ Quiet tr ∧
    Steps prof (fun _ _ => false) (DI P impl) M tr
      (coreCfg (extG M₀ ιe' SL' CL' TL' HL' C' s') th K segs rest yc) ∧
    LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f yc (u₁, t') π₁ ∧
    Silmaril.Wasm.Game.ResultAt u₁ t' r ∧
    Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) r = some w) ∨
  (∃ c, TrapEndH prof P impl M c s' ∧ LReady P l.toW Ie Ii s₀ u₀ F₀ c u₁ π₁ ∧
    Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) .trap = some w)

section Rounds

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ u : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {M₀ : Machine.Config (E3 P) σ}
  {th : Option ThreadId} {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))}
  {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)} {f : Ii.F.Op}

theorem RoundEndH.steps {M M' : Machine.Config (E3 P) σ} {tr : List (Label (E3 P) σ)}
    {u₁ π₁ : Store Nat} {w : Ii.F.Ar f} {s' : σ}
    (H : Steps prof (fun _ _ => false) (DI P impl) M tr M') (hq : Quiet tr)
    (H' : RoundEndH prof P impl l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f M' u₁ π₁ w s') :
    RoundEndH prof P impl l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f M u₁ π₁ w s' := by
  rcases H' with ⟨ιe', SL', CL', TL', HL', C', tr', yc, t', r, hte, hq', r', hI, hr, hw⟩ |
    ⟨c, hT, hRc, hw⟩
  · exact .inl ⟨ιe', SL', CL', TL', HL', C', tr ++ tr', yc, t', r, hte, hq.append hq',
      Adequacy.steps_append H r', hI, hr, hw⟩
  · exact .inr ⟨c, TrapEndH.steps H hq hT, hRc, hw⟩

/-- **A specification round with host calls answered is a forward run of the machine**, ending
as `RoundEndH`. -/
theorem rounds_fwdH (S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀)) (hF : GFrame M₀ th)
    (hH : HostHandles prof P impl g l M₀ th K segs rest) (hT : l.HostTyped g)
    {cs₀ : Store (CanonHost (E3 P))} {π₀ : Store Nat}
    (hR : LReady P l.toW Ie Ii s₀ u₀ F₀ cs₀ u π₀) {w : Ii.F.Ar f} :
    ∀ (rs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)))
      (y : CoreSt (E3 P)) (x : Store Nat × STh) (π π₁ u₁ : Store Nat) (ιe : InstState)
      (SL : List Subtask) (CL : List (Caller (E3 P))) (TL : List (Runtime.Task (E3 P)))
      (HL : List Runtime.Thread) (C : List (Option (Activation (E3 P) σ))) (s s' : σ),
      LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x π →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) rs dss →
      HLinked2.ExpRunH P l Ie π dss.flatten π₁ →
      HostRun g s (l.hostCalls dss.flatten) s' →
      Ii.Path P (.running f x.1 x.2) (callMoves rs ++ [.inr (.ans f w)]) (.idle u₁) →
      ThreadsOk ιe →
      RoundEndH prof P impl l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f
        (coreCfg (extG M₀ ιe SL CL TL HL C s) th K segs rest y) u₁ π₁ w s'
  | [], dss, y, x, π, π₁, u₁, ιe, SL, CL, TL, HL, C, s, s', hI, hrel, hexp, hhr, hpath, hte => by
    cases hrel
    cases hexp
    obtain rfl := hostRun_nil hhr
    obtain ⟨s'', t', r, run, final, hw, hq⟩ := path_ret_inv (by simpa [callMoves] using hpath)
    cases hq
    obtain ⟨yc, hy, hIc⟩ := LInv.reach_fwdH S hI run
    obtain ⟨tr, htr, r'⟩ := Adequacy.coreCfg_steps_of (prof := prof) (hr := fun _ _ => false)
      (dispatch := DI P impl) (B := extG M₀ ιe SL CL TL HL C s) (th := th) (K := K)
      (segs := segs) (rest := rest) hy
    exact .inl ⟨ιe, SL, CL, TL, HL, C, tr, yc, t', r, hte, Quiet.of_core htr, r', hIc, final, hw⟩
  | ⟨e, v⟩ :: rs, dss₀, y, x, π, π₁, u₁, ιe, SL, CL, TL, HL, C, s, s', hI, hrel, hexp, hhr,
      hpath, hte => by
    obtain ⟨ds, dss, hd, hrel', rfl⟩ : ∃ ds dss, Silmaril.Wasm.Component.Reference.ImpRel
        l.imp Ii ⟨e, v⟩ ds ∧ List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii)
          rs dss ∧ dss₀ = ds :: dss := by
      cases hrel with
      | cons h₁ h₂ => exact ⟨_, _, h₁, h₂, rfl⟩
    obtain ⟨s'', t', k, args, run, co, op, hpath'⟩ := path_round_inv (rest := callMoves rs ++
      [.inr (.ans f w)]) (by simpa [callMoves] using hpath)
    obtain ⟨y₁, hy₁, hI₁⟩ := LInv.reach_fwdH S hI run
    obtain ⟨tr₁, htr₁, r₁⟩ := Adequacy.coreCfg_steps_of (prof := prof) (hr := fun _ _ => false)
      (dispatch := DI P impl) (B := extG M₀ ιe SL CL TL HL C s) (th := th) (K := K)
      (segs := segs) (rest := rest) hy₁
    have hq₁ : Quiet tr₁ := Quiet.of_core htr₁
    refine RoundEndH.steps r₁ hq₁ ?_
    obtain ⟨nm, p, ys, E, a, hk, hdx, hys, hst, hyty⟩ := LInv.callout_fwdH S hI₁ co op
    have hek := ifaceOp?_some op
    obtain ⟨nm', ft, A, hk', hA, hm⟩ := hd
    have hA' : payloadAnswer (Ii.imports.get e.1) A = v := hA
    have hft : ft = p := by
      rw [hek.1, hk] at hk'
      simp only [Option.some.injEq, Prod.mk.injEq] at hk'
      exact hk'.2.symm
    subst hft
    have hfilt : e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys :=
      hek.2 ▸ filterMap_of_mapM hys
    have hRdy := lready_after hR hI₁
    rw [hfilt] at hm
    split at hm
    · -- the arguments do not lift: the round ends at once
      next hws =>
      obtain ⟨rfl, rfl⟩ := hm
      have hv : v = .trap := hA.symm
      subst hv
      obtain ⟨rfl, rfl, hw'⟩ := path_doomed co hpath'
      cases hrel'
      have hexp' : HLinked2.ExpRunH P l Ie π [] π₁ := by simpa using hexp
      cases hexp'
      have hhr' : HostRun g s ([] : List (Σ _ : (sigN l.host.length).Op, Option Payload)) s' := by
        simpa [HLinked2.hostCalls] using hhr
      obtain rfl := hostRun_nil hhr'
      refine .inr ⟨y₁.1, ?_, hRdy, hw'⟩
      by_cases hwk : k < l.wire.length
      · obtain ⟨wi, hw⟩ : ∃ wi, l.wire[k]? = some wi := ⟨_, List.getElem?_eq_getElem hwk⟩
        obtain ⟨xe, hxe, hty⟩ := S.wireTy.ty k wi hw
        have hpx : xe.ty = ft := by
          rw [hk] at hty
          simp only [Option.map_some, Option.some.injEq] at hty
          exact hty.symm
        subst hpx
        have hmi : (nm, xe.ty) ∈ l.imp.imports := List.mem_of_getElem? hk
        have hres : xe.ty.results.length ≤ 1 := (S.arity.2 _ hmi).2.2
        have hsite := linkSite_extG (LInv.siteH S hI₁ hk hw hxe hyty) ιe SL CL TL HL C s
        have hT := nest_trapArgsH (prof := prof) (impl := impl) (N := []) (C := C)
          (K := K) (segs := segs) (rest := rest) (hF.lframe ιe SL CL TL HL C s) hte hst
          ((funcs_extG _ _ _ _ _ _ _ _ _).trans (S.lifted k wi xe hw hxe)) hres hsite hws
        rwa [extN_extG_nil] at hT
      · obtain ⟨hi, hhost⟩ := host_get_of S.wireTy hk hwk
        have hfid : l.fid k = ⟨k - l.wire.length⟩ := by
          simp only [HLinked2.fid, hwk, ↓reduceIte]
        have hst' : (E3 P).status y₁.1 y₁.2 = .callout (.lowered ⟨k - l.wire.length⟩
            (witFt l.host[k - l.wire.length].2) {} ⟨2⟩) ys := by
          rw [hhost, ← hfid]
          exact hst
        have hys' : ys.map (·.type) = ValTy.flatList l.host[k - l.wire.length].2.params := by
          rw [hhost]
          exact hyty
        refine (hH ιe SL CL TL HL C s y₁ _ hi ys hst' hys').1 ?_
        rw [hhost]
        exact hws
    · next ws hws =>
      obtain ⟨hkl, R, rfl, hAR⟩ := hm
      have hexp' : HLinked2.ExpRunH P l Ie π
          (⟨(⟨e.1.val, hkl⟩, .vals ws), R⟩ :: dss.flatten) π₁ := by
        simpa only [List.flatten_cons, List.singleton_append] using hexp
      have hhr₀ : HostRun g s
          (l.hostCalls (⟨(⟨e.1.val, hkl⟩, .vals ws), R⟩ :: dss.flatten)) s' := by
        simpa only [List.flatten_cons, List.singleton_append] using hhr
      by_cases hwk : k < l.wire.length
      · -- a wired call
        have hhr' : HostRun g s (l.hostCalls dss.flatten) s' := by
          rwa [hostCalls_cons_wired (by simpa [hek.1] using hwk)] at hhr₀
        obtain ⟨wi, hw⟩ : ∃ wi, l.wire[k]? = some wi := ⟨_, List.getElem?_eq_getElem hwk⟩
        obtain ⟨xe, hxe, hty⟩ := S.wireTy.ty k wi hw
        have hpx : xe.ty = ft := by
          rw [hk] at hty
          simp only [Option.map_some, Option.some.injEq] at hty
          exact hty.symm
        subst hpx
        have hmi : (nm, xe.ty) ∈ l.imp.imports := List.mem_of_getElem? hk
        have hres : xe.ty.results.length ≤ 1 := (S.arity.2 _ hmi).2.2
        have hfl : ArenaField.funcs.get? M₀.store (l.fid k) =
            some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) :=
          S.lifted k wi xe hw hxe
        have hsite : LinkSite M₀ y₁ (.lowered (l.fid k) (witFt xe.ty) {} ⟨2⟩) ys :=
          LInv.siteH S hI₁ hk hw hxe hyty
        have hxm : xe ∈ l.exp.exports := List.mem_of_getElem? hxe
        cases hexp' with
        | @ret _ π₂ _ _ _ us _ w₂ hwire hRet hrest =>
          have hw₂ : w₂.val = wi := by
            rw [hek.1, hw] at hwire
            exact (Option.some.inj hwire).symm
          have hx₂ : l.exp.exports[w₂] = xe :=
            (List.getElem?_eq_some_iff.mp (hw₂.symm ▸ hxe : l.exp.exports[w₂.val]? = some xe)).2
          rw [hx₂] at hRet
          obtain ⟨ev, zs, hrunA, hstA, husA, hI₂⟩ := LInv.resume_fwdH S hI₁ hk hxe hdx op hRet
          have hcheck : ValTy.checkList xe.ty.results us = true :=
            Silmaril.Wasm.Component.checkList_of_liftArgs husA
          have hv : Silmaril.Wasm.Game.Answer.toResult v =
              .values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat) := by
            rw [← hA', hAR]
            have hup : (some (Payload.vals us)).bind
                (Silmaril.Wasm.Component.Adapter.lower xe.ty).up =
                some (.flat (lowerArgs xe.ty.results us)) := by
              simp only [Option.bind_some, Silmaril.Wasm.Component.Adapter.up,
                Silmaril.Wasm.Component.checkLower, hcheck, ite_true, Option.map_some]
            rw [hup, payloadAnswer_flat (w := .values ⟨_, resAnswerH S hk hek.1 hcheck⟩) rfl]
            rfl
          rw [hv] at hpath'
          obtain ⟨ιe₂, SL₂, CL₂, TL₂, HL₂, C₂, tr₂, hte₂, hq₂, -, r₂⟩ :=
            nest_retG (prof := prof) (impl := impl) (K := K) (segs := segs) (rest := rest)
              (SL := SL) (CL := CL) (TL := TL) (HL := HL) (C := C) (s := s) hF hte hst hfl hres
              hsite hws hrunA hstA husA
          exact RoundEndH.steps r₂ hq₂ (rounds_fwdH S hF hH hT hR rs dss _ _ _ π₁ u₁ ιe₂ SL₂ CL₂
            TL₂ HL₂ C₂ s s' hI₂ hrel' hrest hhr' hpath' hte₂)
        | trap w₂ hwire hTr hrest =>
          have hw₂ : w₂.val = wi := by
            rw [hek.1, hw] at hwire
            exact (Option.some.inj hwire).symm
          have hx₂ : l.exp.exports[w₂] = xe :=
            (List.getElem?_eq_some_iff.mp (hw₂.symm ▸ hxe : l.exp.exports[w₂.val]? = some xe)).2
          rw [hx₂] at hTr
          have hv : v = .trap := by
            rw [← hA', hAR]
            rfl
          subst hv
          obtain ⟨rfl, rfl, hw'⟩ := path_doomed co hpath'
          cases hrel'
          cases hrest
          have hhr'' : HostRun g s
              ([] : List (Σ _ : (sigN l.host.length).Op, Option Payload)) s' := by
            simpa [HLinked2.hostCalls] using hhr'
          obtain rfl := hostRun_nil hhr''
          obtain ⟨ev, hrunA, hendA, hRdy'⟩ := LInv.expTrap_fwdH S hR hI₁ hxm hTr
          have hsite' := linkSite_extG hsite ιe SL CL TL HL C s
          have hfl' : ArenaField.funcs.get? (extG M₀ ιe SL CL TL HL C s).store (l.fid k) =
              some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) :=
            (funcs_extG _ _ _ _ _ _ _ _ _).trans hfl
          refine .inr ⟨ev.1, ?_, hRdy', hw'⟩
          rcases hendA with h | ⟨zs, h, -, hn⟩
          · have hT := nest_trapCoreH (prof := prof) (impl := impl) (N := []) (C := C)
              (K := K) (segs := segs) (rest := rest)
              (hF.lframe ιe SL CL TL HL C s) hte hst hfl' hres hsite' hws hrunA h
            rwa [extN_extG_nil] at hT
          · have hT := nest_trapLiftH (prof := prof) (impl := impl) (N := []) (C := C)
              (K := K) (segs := segs) (rest := rest)
              (hF.lframe ιe SL CL TL HL C s) hte hst hfl' hres hsite' hws hrunA h hn
            rwa [extN_extG_nil] at hT
        | host i hn hrest =>
          have h1 := hek.1
          simp only at hn
          omega
      · -- a host call
        obtain ⟨hi, hhost⟩ := host_get_of S.wireTy hk hwk
        have hfid : l.fid k = ⟨k - l.wire.length⟩ := by
          simp only [HLinked2.fid, hwk, ↓reduceIte]
        have hst' : (E3 P).status y₁.1 y₁.2 = .callout (.lowered ⟨k - l.wire.length⟩
            (witFt l.host[k - l.wire.length].2) {} ⟨2⟩) ys := by
          rw [hhost, ← hfid]
          exact hst
        have hys' : ys.map (·.type) = ValTy.flatList l.host[k - l.wire.length].2.params := by
          rw [hhost]
          exact hyty
        have hws' : liftArgs l.host[k - l.wire.length].2.params ys = some ws := by
          rw [hhost]
          exact hws
        have hHk := (hH ιe SL CL TL HL C s y₁ _ hi ys hst' hys').2 ws hws'
        have hrest : HLinked2.ExpRunH P l Ie π dss.flatten π₁ := by
          cases hexp' with
          | ret w₂ hwire _ _ =>
            exfalso
            have hge : l.wire.length ≤ e.1.val := by omega
            rw [List.getElem?_eq_none hge] at hwire
            cases hwire
          | trap w₂ hwire _ _ =>
            exfalso
            have hge : l.wire.length ≤ e.1.val := by omega
            rw [List.getElem?_eq_none hge] at hwire
            cases hwire
          | host _ _ hrest => exact hrest
        have hwl : l.wire.length ≤ (⟨e.1.val, hkl⟩ : Fin l.imp.imports.length).val := by
          simp only [hek.1]
          omega
        have hil : (⟨e.1.val, hkl⟩ : Fin l.imp.imports.length).val - l.wire.length <
            l.host.length := by
          simp only [hek.1]
          exact hi
        rw [hostCalls_cons_host (d := ⟨(⟨e.1.val, hkl⟩, .vals ws), R⟩) hwl hil] at hhr₀
        obtain ⟨s₁, hd₁, hhr'⟩ : ∃ s₁, HostAnswersS g s
            (⟨(⟨e.1.val - l.wire.length, hil⟩, .vals ws), R⟩ :
              Σ _ : (sigN l.host.length).Op, Option Payload) s₁ ∧
            HostRun g s₁ (l.hostCalls dss.flatten) s' := by
          cases hhr₀ with
          | cons hd₁ hhr' => exact ⟨_, hd₁, hhr'⟩
        obtain ⟨k', ws', hkw, hans⟩ := hd₁
        simp only [Prod.mk.injEq, Payload.vals.injEq] at hkw
        obtain ⟨rfl, rfl⟩ := hkw
        have hik : e.1.val - l.wire.length = k - l.wire.length := by rw [hek.1]
        cases R with
        | none =>
          obtain ⟨hg, hs₁⟩ := hans
          subst s₁
          have hv : v = .trap := by
            rw [← hA', hAR]
            rfl
          subst hv
          obtain ⟨rfl, rfl, hw'⟩ := path_doomed co hpath'
          cases hrel'
          have hhr'' : HostRun g s
              ([] : List (Σ _ : (sigN l.host.length).Op, Option Payload)) s' := by
            simpa [HLinked2.hostCalls] using hhr'
          obtain rfl := hostRun_nil hhr''
          cases hrest
          exact .inr ⟨y₁.1, hHk.1 (hik ▸ hg), hRdy, hw'⟩
        | some A₀ =>
          cases A₀ with
          | flat _ => exact hans.elim
          | vals us =>
            have hg : g s ⟨k - l.wire.length⟩ (ws.map toRefVal) = some (us.map toRefVal, s₁) := by
              simpa only [hik] using hans
            obtain ⟨us', hus', hck'⟩ := hT s _ hi ws _ s₁ hg
            obtain rfl := map_toRefVal_inj hus'
            have hcheck : ValTy.checkList ft.results us = true := by
              rw [hhost] at hck'
              exact hck'
            have hv : Silmaril.Wasm.Game.Answer.toResult v =
                .values ((lowerArgs ft.results us).map Silmaril.Wasm.SingleThreaded.ofFlat) := by
              rw [← hA', hAR]
              have hup : (some (Payload.vals us)).bind
                  (Silmaril.Wasm.Component.Adapter.lower ft).up =
                  some (.flat (lowerArgs ft.results us)) := by
                simp only [Option.bind_some, Silmaril.Wasm.Component.Adapter.up,
                  Silmaril.Wasm.Component.checkLower, hcheck, ite_true, Option.map_some]
              rw [hup, payloadAnswer_flat (w := .values ⟨_, resAnswerH S hk hek.1 hcheck⟩) rfl]
              rfl
            rw [hv] at hpath'
            have hI₂ := LInv.resumeHost_fwdH S hI₁ hk hdx op hcheck
            obtain ⟨xS, cS, tr₂, hq₂, r₂⟩ := hHk.2 us s₁ hg (by rw [hhost]; exact hcheck)
            rw [hhost] at r₂
            exact RoundEndH.steps r₂ hq₂ (rounds_fwdH S hF hH hT hR rs dss _ _ _ π₁ u₁ ιe
              (SL ++ [xS]) (CL ++ [cS]) TL HL C s₁ s' hI₂ hrel' hrest hhr' hpath' hte)

end Rounds

/-! ## One call -/

/-- **A trapped end after the invocation is a trapped call**, in the host state of the trap. -/
theorem calls_of_trapEndH {cs : (core3P P).Store (CanonHost (core3P P))} {ιe ιi : InstState}
    {fs : List (CFuncInst (core3P P))} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k j : Nat}
    (hG : G.Fresh k) {args : List Silmaril.Wasm.Component.Reference.Val}
    {c : (E3 P).Store (CanonHost (E3 P))} {s : σ}
    (h : TrapEndH prof P impl (invokedAtL cs ιe ιi fs G ST h₀ k j args) c s) :
    ∃ m', Calls prof (fun _ _ => false) (DI P impl) (readyCfgL cs ιe ιi fs G ST h₀) ⟨k⟩ ⟨j⟩ args
      m' .trap ∧ m'.core = c ∧ m'.host = s := by
  obtain ⟨tr, m', r, hh, hi, hl, hc, hs⟩ := h
  exact ⟨m', ⟨tr, .cons (invoke_stepL hG j args) r, fun ev hm => absurd hm (hh ev),
    fun _ msg => hi msg, hl⟩, hc, hs⟩

/-- What a forward call of an `HLinked2` shows for the outcome `o` of a round: results `ws` are a
resolved call ending between calls in host state `s'` with `ReadyL` at `u₁`, `π₁`; a trap is a
trapped call in host state `s'` with `LReady` at the core store of the trapped configuration. -/
def FwdOutH (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ) (l : HLinked2)
    (Ie Ii : Silmaril.Wasm.Game.ScalarInstance) (s₀ u₀ : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (fs : List (CFuncInst (core3P P)))
    (m : Machine.Config (E3 P) σ) (k j : Nat) (args : List Silmaril.Wasm.Component.Reference.Val)
    (u₁ π₁ : Store Nat) (s' : σ) : Option (List Silmaril.Wasm.Component.Val) → Prop
  | some ws => ∃ (cs' : (core3P P).Store (CanonHost (core3P P))) (ιe' ιi' : InstState)
      (G' : Garb P σ) (ST' : List Subtask),
      Calls prof (fun _ _ => false) (DI P impl) m ⟨k⟩ ⟨j⟩ args
        (readyCfgL cs' ιe' ιi' fs G' ST' s') (.resolved (some (ws.map toRefVal))) ∧
      ReadyL P l.toW Ie Ii s₀ u₀ F₀ cs' ιe' ιi' G' u₁ π₁ (k + 1)
  | none => ∃ m', Calls prof (fun _ _ => false) (DI P impl) m ⟨k⟩ ⟨j⟩ args m' .trap ∧
      LReady P l.toW Ie Ii s₀ u₀ F₀ m'.core u₁ π₁ ∧ m'.host = s'

section Call

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) σ}
  {fs : List (CFuncInst (core3P P))}

/-- **A specification round with host calls handled is a call of the reference machine**
(`FwdOutH`), for any host that handles the host callouts as `g` (`Handles`). -/
theorem linkCall_fwdG (hHd : Handles prof P impl g l) (hT : l.HostTyped g)
    (S₀ : HStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOkH l Ii s₀ fs) {cs : (core3P P).Store (CanonHost (core3P P))}
    {ιe ιi : InstState} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k : Nat} {u π : Store Nat}
    (R : ReadyL P l.toW Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k) (d : Linked2.SessRound l.toL2 Ii)
    (hok : d.Ok) {u₁ π₁ : Store Nat} (hpath : Ii.Path P (.idle u) d.instMoves (.idle u₁))
    (hexp : HLinked2.ExpRunH P l Ie π d.dss.flatten π₁) {s' : σ}
    (hhr : HostRun g h₀ (l.hostCalls d.dss.flatten) s')
    {o : Option (List Silmaril.Wasm.Component.Val)} (hans : d.ans = o.map .vals) :
    FwdOutH prof P impl l Ie Ii s₀ u₀ F₀ fs (readyCfgL cs ιe ιi fs G ST h₀) k
      (l.host.length + l.exp.exports.length + d.j) (d.vs.map toRefVal) u₁ π₁ s' o := by
  obtain ⟨xs, hck, hf₁, hf₂, hrel⟩ := hok
  have hvs : ValTy.checkList l.imp.exports[d.j].ty.params d.vs = true := by
    unfold checkLower at hck
    split_ifs at hck with h
    exact h
  have hxs : xs = lowerArgs l.imp.exports[d.j].ty.params d.vs := by
    simp only [checkLower, hvs, ↓reduceIte, Option.some.injEq] at hck
    exact hck.symm
  subst hxs
  have hx : l.imp.exports[d.j] ∈ l.imp.exports := List.getElem_mem d.j.isLt
  obtain ⟨nm, hcore⟩ := S₀.impGood.core _ hx
  have hflat : l.imp.mod.exports[l.imp.exports[d.j].core]? =
      some (nm, l.imp.exports[d.j].ty.flat) := hcore
  have hft' : Ii.exports.get d.f.1 = fnOf l.imp.exports[d.j].ty.flat := by
    have hlt : d.f.1.val < l.imp.mod.exports.length := by
      rw [hf₁]
      exact (List.getElem?_eq_some_iff.mp hflat).1
    have e₁ : Ii.exports.get d.f.1 = fnOf (l.imp.mod.exports[d.f.1.val]'hlt).2 := by
      simp only [List.get_eq_getElem, S₀.impInst.2.2, List.getElem_map]
    rw [e₁]
    have e₂ : l.imp.mod.exports[d.f.1.val]'hlt = (nm, l.imp.exports[d.j].ty.flat) := by
      have := (List.getElem?_eq_some_iff.mp hflat).2
      simp only [← hf₁] at this
      exact this
    rw [e₂]
  obtain ⟨hmax, hmaxr, hres⟩ := S₀.arity.1 _ hx
  obtain ⟨hpf, hrf⟩ := S₀.floats.1 _ hx
  have ha : Ii.addrs.getD l.imp.exports[d.j].core 0 = Ii.addr d.f.1 := by
    rw [← hf₁]
    rfl
  have hfj : fs[l.host.length + l.exp.exports.length + d.j]? =
      some (.lifted (s₀.funcs.length + Ii.addr d.f.1) (liftedFt l.imp.exports[d.j]) {} ⟨2⟩) :=
    ha ▸ hfs d.j
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atLKTS (impl := impl) prof cs ιe ιi fs G
    ST h₀ k (l.host.length + l.exp.exports.length + d.j) _ l.imp.exports[d.j] d.vs hpf hvs hmax
    hres hmaxr hrf R.thI R.leave hfj
  have S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀) := S₀.move R.inv.wfI (hat.funcs.trans hB₀.symm)
  have hF := gframe_of hat
  have hH := hHd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hat S.hostFn
  have hI₀ : LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) d.f
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr d.f.1)
        (lowerArgs l.imp.exports[d.j].ty.params d.vs)) (u, Ii.initThread d.f) π :=
    linv_ready R.inv hf₂ rfl
  have hpath' : Ii.Path P (.running d.f u (Ii.initThread d.f))
      (callMoves d.cs ++ [.inr (.ans d.f d.w)]) (.idle u₁) := by
    have h : Ii.Path P (.idle u) (.inr (.ask d.f) :: (callMoves d.cs ++ [.inr (.ans d.f d.w)]))
        (.idle u₁) := hpath
    cases h with
    | cons h₁ h₂ =>
      cases h₁
      exact h₂
  have hstart : M₀ = coreCfg (extG M₀ ιe [] [] [] [] M₀.conts h₀) th K segs rest
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr d.f.1)
        (lowerArgs l.imp.exports[d.j].ty.params d.vs)) := by
    have e := hat.start
    rw [extN_eq_extG] at e
    rw [← hat.host]
    exact e
  have hend := rounds_fwdH (prof := prof) (impl := impl) S hF hH hT R.inv d.cs d.dss _
    (u, Ii.initThread d.f) π π₁ u₁ ιe [] [] [] [] M₀.conts h₀ s' hI₀ hrel hexp hhr hpath'
    R.thE
  rw [← hstart] at hend
  have hlive₀ : Live M₀ := by
    rw [hat.start]
    exact coreCfg_extN_live _ _ _ _ _ _ _ _ _
  have hq₁ : Quiet tr₁ := Quiet.of_lrun hpre hlive₀
  -- a trapped end
  have hfr : ∀ c, TrapEndH prof P impl M₀ c s' → LReady P l.toW Ie Ii s₀ u₀ F₀ c u₁ π₁ →
      d.ans = none →
      FwdOutH prof P impl l Ie Ii s₀ u₀ F₀ fs (readyCfgL cs ιe ιi fs G ST h₀) k
        (l.host.length + l.exp.exports.length + d.j) (d.vs.map toRefVal) u₁ π₁ s' o := by
    intro c hT' hRc hn
    have ho : o = none := by
      cases o with
      | none => rfl
      | some ws =>
        rw [hn] at hans
        cases hans
    subst ho
    obtain ⟨m', hc, hcore, hhost⟩ :=
      calls_of_trapEndH R.fresh (TrapEndH.steps hpre.steps hq₁ hT')
    exact ⟨m', hc, hcore ▸ hRc, hhost⟩
  rcases hend with ⟨ιe', SL', CL', TL', HL', C', tr₂, yc, t', r, hte', hq₂, r₂, hIc, final, hw⟩ |
    ⟨c, hT', hRc, hw⟩
  · -- the importer's part finished
    obtain ⟨ρp, Op, ρc, Oc, hLc, -⟩ := hIc.rel
    cases r with
    | throw b => exact (not_result_throw hLc final).elim
    | trap =>
      exact hfr _ (TrapEndH.steps r₂ hq₂
        (coreTrap_endH (status_of_trap (gL P l.toW) hLc final)))
        (lready_after R.inv hIc) (lifted_trap (x := l.imp.exports[d.j]) (fun _ h => by cases h) hw)
    | values cvs =>
      have htyped : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal
          (Ii.exports.get d.f.1).results cvs := by
        unfold Silmaril.Wasm.Game.Answer.ofResult? at hw
        dsimp only at hw
        split_ifs at hw with ht
        exact ht
      rw [hft'] at htyped
      obtain ⟨zs, hm⟩ := Silmaril.Proofs.Wasm.Component.Core3G.toFlat?_isSome htyped
      have hst := status_of_values (gL P l.toW) hLc final hm
      have hty : zs.map (·.type) = ValTy.flatList l.imp.exports[d.j].ty.results :=
        results_typed hft' hw hm
      have hR' : d.ans = (liftArgs l.imp.exports[d.j].ty.results zs).map .vals :=
        lifted_answer hw hm
      have s₃ : Step prof (fun _ _ => false) (DI P impl)
          (coreCfg (extG M₀ ιe' SL' CL' TL' HL' C' s') th K segs rest yc) .tau
          (retCfg (extG M₀ ιe' SL' CL' TL' HL' C' s') th K segs rest yc zs) :=
        Step.coreReturned rfl hst
      cases hl : liftArgs l.imp.exports[d.j].ty.results zs with
      | none =>
        rw [hl] at hR'
        exact hfr _ (TrapEndH.steps r₂ hq₂ (TrapEndH.steps (.cons s₃ (.refl _)) Quiet.tau
          (TrapsAtSH.trapEndH (hat.trapGH ιe' SL' CL' TL' HL' C' s' yc zs hty hl))))
          (lready_after R.inv hIc) hR'
      | some ws =>
        rw [hl] at hR'
        have ho : o = some ws := by
          cases o with
          | none =>
            rw [hans] at hR'
            cases hR'
          | some ws' =>
            rw [hans] at hR'
            simp only [Option.map_some, Option.some.injEq, Payload.vals.injEq] at hR'
            rw [hR']
        subst ho
        obtain ⟨C'', tr₃, mE, hlr, rfl⟩ := hat.retG ιe' SL' CL' TL' HL' C' s' yc zs ws hty hl
        refine ⟨_, _, _, _, _, ⟨tr₁ ++ (tr₂ ++ (.tau :: tr₃)), .cons (invoke_stepL R.fresh _ _)
          (Adequacy.steps_append hpre.steps (Adequacy.steps_append r₂ (.cons s₃ hlr.steps))), ?_,
          (fun h => by cases h), ⟨rfl, rfl, result?_nextG R.fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩⟩,
          ⟨lready_after R.inv hIc, hte', threadsOk_after _ _,
            (removeThread_enter_mayLeave _ _).trans R.leave, fresh_nextG R.fresh _ _ _ _ _ _ _ _⟩⟩
        intro ev hm
        exfalso
        rcases List.mem_append.mp hm with hm | hm
        · exact hq₁.1 ev hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hq₂.1 ev hm
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm
        · exact Adequacy.LRun.no_host hlr ev hm
  · -- a trap
    exact hfr c hT' hRc (lifted_trap (x := l.imp.exports[d.j]) (fun _ h => by cases h) hw)

/-- **`linkCall_fwdG` for the answering host `answerImplS g`.** -/
theorem linkCall_fwdH (hT : l.HostTyped g) (S₀ : HStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀))
    (hB₀ : B₀.store.funcs = fs) (hfs : LiftedOkH l Ii s₀ fs)
    {cs : (core3P P).Store (CanonHost (core3P P))} {ιe ιi : InstState} {G : Garb P σ}
    {ST : List Subtask} {h₀ : σ} {k : Nat} {u π : Store Nat}
    (R : ReadyL P l.toW Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k) (d : Linked2.SessRound l.toL2 Ii)
    (hok : d.Ok) {u₁ π₁ : Store Nat} (hpath : Ii.Path P (.idle u) d.instMoves (.idle u₁))
    (hexp : HLinked2.ExpRunH P l Ie π d.dss.flatten π₁) {s' : σ}
    (hhr : HostRun g h₀ (l.hostCalls d.dss.flatten) s')
    {o : Option (List Silmaril.Wasm.Component.Val)} (hans : d.ans = o.map .vals) :
    FwdOutH prof P (answerImplS g) l Ie Ii s₀ u₀ F₀ fs (readyCfgL cs ιe ιi fs G ST h₀) k
      (l.host.length + l.exp.exports.length + d.j) (d.vs.map toRefVal) u₁ π₁ s' o :=
  linkCall_fwdG (handles_answer S₀.arity S₀.floats S₀.wireTy) hT S₀ hB₀ hfs R d hok hpath hexp
    hhr hans

end Call

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
