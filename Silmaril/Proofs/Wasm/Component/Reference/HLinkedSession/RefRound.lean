module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Sess

/-!
# Reference runs of a call of `HLinked2.toRef`, backward: rounds

The backward counterpart of `rounds_fwdH` (`Call`), at the host-first layout of `Stat` (`HStat`,
`LInv` at the renaming `gL P l.toW`), for any host whose host callouts behave as the answering
function `g` prescribes:

* `HostHandlesB`, `HandlesB`: the backward counterpart of `HostHandles`/`Handles`. At a host
  callout of the importer, in every `extG` extension of the call's frame, arguments that do not
  lift, or no answer of `g`, trap (`TrapsAtSH`: a live deterministic run to the trap, at the
  callout's core store and host state); a well-typed answer of `g` is a live deterministic run
  to the importer's activation resumed with the lowered answer, in the new host state.
  `handlesB_answer` proves it for `answerImplS g` (`hostCall_noLiftGS`, `hostCall_noAnswerS`,
  `hostCall_lrun`);
* `LInv.typedH`, `LInv.reachH`, `LInv.calloutH`, `LInv.resumeH`, `lready_expTrapH`: the backward
  lemmas of `LinkSeg` and `LinkedSessionRef.Call` (`LInv.typed`, `LInv.reach`, `LInv.callout`,
  `LInv.resume`, `lready_expTrap`) over `HStat`, same proofs. A callout of the shared thread is
  the trampoline of `l.fid k` for an import `k` of the importer (`LInv.calloutH`), a wired import
  (`k < wire.length`) or a host import;
* `trapsAtSH_out`: a run from a configuration that traps (`TrapsAtSH`) ending where a call
  outcome holds ends in the trap, at its core store and host state;
* `rounds_invH`: every machine run of the importer's core phase, in any `extG` extension of the
  call's frame, that ends where a call outcome holds is a round of the specification
  (`RoundBackH`): rounds of the importer's instance related by `ImpRel` to component import calls
  that form an `ExpRunH` segment of the exporter, whose host calls form a `HostRun g`, followed
  either by an exit of the importer's core phase (`LInv` at its end, the frame's host state that
  of the end of the `HostRun`), or by a trap of the call, answering a trap with `LReady` at the
  trapped core store and host state. **A host callout inverts** to a host call answered as `g`
  answers in the current host state (then `LInv` again by `LInv.resumeHost_fwdH`), or to a trap
  (arguments that do not lift, or no answer). The host answers are typed (`HLinked2.HostTyped g`):
  `rounds_invH` reads the lowered answer back as IR values of the import's result types.
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
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Rel4)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind}
  {g : σ → HostFuncId → List RVal → Option (List RVal × σ)}

/-! ## Traps with the host state -/

/-- **A run from a configuration that traps at `c` in host state `h`**, ending where a call
outcome holds, ends in the trap, at the core store `c` and the host state `h`. -/
theorem trapsAtSH_out {impl : HostImpl (E3 P) σ} {M m' : Machine.Config (E3 P) σ}
    {tr : List (Label (E3 P) σ)} {c : (E3 P).Store (CanonHost (E3 P))} {h : σ}
    {out : CallOutcome} {cid : CallId} (hT : TrapsAtSH prof P impl M c h)
    (r : Steps prof (fun _ _ => false) (DI P impl) M tr m')
    (ho : out.Holds (fun _ _ => false) cid m') :
    out = .trap ∧ m'.core = c ∧ m'.host = h := by
  obtain ⟨tr₁, mT, rT, -, hrun, hlive, hu, hc, hh⟩ := hT
  rcases hrun.inv r with hl' | ⟨tr'', -, r''⟩
  · exact absurd ho (hl'.not_holds _ _)
  cases r'' with
  | refl => exact absurd ho (hlive.not_holds _ _)
  | cons s' r''' =>
    obtain ⟨rfl, rfl⟩ := hu.2 _ _ s'
    have e := steps_of_locked rfl rfl r'''
    subst e
    exact ⟨holds_trapCfgD ho, hc, hh⟩

/-- The core activation in an `extG` extension is live. -/
theorem coreCfg_extG_live (M₀ : Machine.Config (E3 P) σ) (ιe : InstState) (SL : List Subtask)
    (CL : List (Caller (E3 P))) (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
    (C : List (Option (Activation (E3 P) σ))) (h : σ) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (x : CoreSt (E3 P)) :
    Live (coreCfg (extG M₀ ιe SL CL TL HL C h) th K segs rest x) :=
  ⟨List.cons_ne_nil _ _, rfl⟩

/-! ## Host runs -/

/-- `HostRun` composes. -/
theorem hostRun_append {n : Nat} {s s₁ s₂ : σ} :
    ∀ {ds₁ ds₂ : List (Σ _ : (sigN n).Op, Option Payload)},
      HostRun g s ds₁ s₁ → HostRun g s₁ ds₂ s₂ → HostRun g s (ds₁ ++ ds₂) s₂
  | [], _, h₁, h₂ => by
    obtain rfl := hostRun_nil h₁
    exact h₂
  | _ :: _, _, .cons hd h₁, h₂ => .cons hd (hostRun_append h₁ h₂)

/-- A wired component import call adds no host call. -/
theorem hostRun_wired {l : HLinked2} {s s' : σ}
    {d : Σ _ : (sigN l.imp.imports.length).Op, Option Payload}
    {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
    (h : d.1.1.val < l.wire.length) (hr : HostRun g s (l.hostCalls ds) s') :
    HostRun g s (l.hostCalls (d :: ds)) s' := by
  rw [hostCalls_cons_wired h]
  exact hr

/-- A host call of the importer answered as `g` answers, then a `HostRun`. -/
theorem hostRun_host {l : HLinked2} {s s₁ s₂ : σ}
    {d : Σ _ : (sigN l.imp.imports.length).Op, Option Payload}
    {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
    (hw : l.wire.length ≤ d.1.1.val) (hi : d.1.1.val - l.wire.length < l.host.length)
    (hd : HostAnswersS g s (⟨(⟨d.1.1.val - l.wire.length, hi⟩, d.1.2), d.2⟩ :
      Σ _ : (sigN l.host.length).Op, Option Payload) s₁)
    (hr : HostRun g s₁ (l.hostCalls ds) s₂) : HostRun g s (l.hostCalls (d :: ds)) s₂ := by
  rw [hostCalls_cons_host hw hi]
  exact .cons hd hr

/-! ## What the host does at a host callout, backward -/

/-- **The host at a host callout, backward** (`HostHandles` with live deterministic runs), in
every `extG` extension of the frame `M₀` of a call: a callout of host function `i` whose flat
arguments do not lift traps (`TrapsAtSH`, at the callout's core store and host state); one that
`g` does not answer traps likewise; a well-typed answer `us` of `g`, moving the host state to
`s'`, is a live deterministic run to the importer's activation resumed with the lowered answer,
in host state `s'` and with one more subtask and caller record. -/
def HostHandlesB (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
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
      TrapsAtSH prof P impl (coreCfg (extG M₀ ιe SL CL TL HL C h) th K segs rest y) y.1 h) ∧
    ∀ ws, liftArgs l.host[i].2.params ys = some ws →
      (g h ⟨i⟩ (ws.map toRefVal) = none →
        TrapsAtSH prof P impl (coreCfg (extG M₀ ιe SL CL TL HL C h) th K segs rest y) y.1 h) ∧
      ∀ (us : List Silmaril.Wasm.Component.Val) (s' : σ),
        g h ⟨i⟩ (ws.map toRefVal) = some (us.map toRefVal, s') →
        ValTy.checkList l.host[i].2.results us = true →
        ∃ (x : Subtask) (c : Caller (E3 P)) (tr : List (Label (E3 P) σ)),
          LRun prof (fun _ _ => false) (DI P impl)
            (coreCfg (extG M₀ ιe SL CL TL HL C h) th K segs rest y) (.tau :: tr)
            (coreCfg (extG M₀ ιe (SL ++ [x]) (CL ++ [c]) TL HL C s') th K segs rest
              (y.1, (E3 P).resume y.1 y.2 (.values (lowerArgs l.host[i].2.results us))))

/-- **The host handles the host callouts of every call, backward**: `HostHandlesB` at the frame
of every call (`CallAtLKTS`) whose component functions `0, …, k - 1` are the host functions of
`l.host`. -/
def HandlesB (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
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
    HostHandlesB prof P impl g l M₀ th K segs rest

/-- **The answering host handles the host callouts, backward** (`hostCall_noLiftGS`,
`hostCall_noAnswerS`, `hostCall_lrun`). -/
theorem handlesB_answer {l : HLinked2} (har : l.imp.Arity) (hff : l.imp.FloatFree)
    (hW : l.WireTy) : HandlesB prof P (answerImplS g) g l := by
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
  refine ⟨fun hws => hostCall_noLiftGS (fun _ => ⟨_, rfl⟩) rfl hst hentry hι₂ hleave hf hpf hys
    hmaxp hws, fun ws hws => ⟨fun hg => hostCall_noAnswerS rfl hst hentry hι₂ hleave hf hpf hys
    hmaxp hws hg, fun us s' hg hus => ?_⟩⟩
  obtain ⟨pos, tr, r⟩ := hostCall_lrun (prof := prof) (K := K) (segs := segs) (rest := rest) rfl
    hst hentry hι₂ hleave hf hpf hys hmaxp hws hg hres hrf hus hmaxr
  rw [extG_hostCall] at r
  exact ⟨_, _, tr, r⟩

/-! ## The invariant, backward, at the host-first layout -/

section Inv

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B : Machine.Config (E3 P) σ} {Op₀ Oc₀ : Own}
  {f : Ii.F.Op} {y : CoreSt (E3 P)} {x : Store Nat × STh} {π : Store Nat}

/-- The part thread is typed (`LInv.typed` over `HStat`). -/
theorem LInv.typedH (S : HStat P l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P l.toW Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π) :
    ∃ ts, Silmaril.Wasm.Execution.Core.StoreOk x.1 ∧
      Silmaril.Wasm.SingleThreaded.ThreadOk x.1 x.2 ts := by
  obtain ⟨ts, hg₀⟩ := SEnvTyping.good_invoke S.impWf f
  have hg := SEnvTyping.good_ssteps (P := P) S.impWf (valEnv_throwsBelow Ii _)
    (x := (_, ())) (y := (x.2.config x.1, ())) hg₀ hI.run
  have hs : Silmaril.Wasm.Execution.Core.StoreOk (x.2.config x.1).store :=
    Silmaril.Wasm.SingleThreaded.ConfigOk.storeOk hg.ok
  rw [Silmaril.Wasm.SingleThreaded.Thread.config_store] at hs
  exact ⟨ts, hs, hg.ok⟩

/-- **Host-free shared runs keep the invariant**, the part running host-free alongside
(`LInv.reach` over `HStat`). -/
theorem LInv.reachH (S : HStat P l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P l.toW Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π) {y' : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P)) y y') :
    ∃ x', LInv P l.toW Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y' x' π ∧ Silmaril.Wasm.Game.Reach P x x' := by
  obtain ⟨ρp, Op, ρc, Oc, hL, hR⟩ := hI.rel
  obtain ⟨ts, hs, ht⟩ := LInv.typedH S hI
  have hrun := reach_mapH (gL P l.toW) (coreSteps_internalP hy)
  obtain ⟨x', ρc', Oc', prun, hL', hgr, htc, -, -⟩ := reach_link_back hrun hL hs ht
  have hrc : PartRel ρc' Oc' (reloc s₀ x'.1) (Store.mapH (gL P l.toW) y'.1) := by
    have h := hL'.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store] at h
  have hfy : y'.1.funcs = y.1.funcs := reach_funcs' (coreSteps_internalP hy)
  refine ⟨x', ⟨⟨ρp, Op, ρc', Oc', hL', Rel4.after_c hR hrc hgr htc⟩,
    hI.fnE.congr (mapH_funcs_eq _ hfy) rfl, hI.wf, hfy.trans hI.funcs, ?_⟩, prun⟩
  exact hI.run.trans (reach_ssteps prun)

/-- **A callout of the shared thread is a trampoline call of the importer**: the trampoline of
`l.fid k` for an import `k` of type `p`, the part stopped at the redex of host code `k` on the
same arguments, a typed import question of `Ii`, whose flat arguments have the flat parameter
types (`LInv.callout` over `HStat`). -/
theorem LInv.calloutH (S : HStat P l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P l.toW Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π) {h : CanonHost (E3 P)} {ys : List Flat}
    (hst : (E3 P).status y.1 y.2 = .callout h ys) :
    ∃ (k : Nat) (nm : String) (p : FuncTy) (E : Silmaril.Wasm.SingleThreaded.Ctx) (a : Nat)
      (args : List Silmaril.Wasm.Execution.Core.Val) (e : Ii.E.Op),
      h = .lowered (l.fid k) (witFt p) {} ⟨2⟩ ∧ l.imp.imports[k]? = some (nm, p) ∧
      Silmaril.Wasm.SingleThreaded.decompose? x.1 (x.2.config x.1).code = some (E, a, k, args) ∧
      args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys ∧ Ii.importOp? k args = some e ∧
      ys.map (·.type) = ValTy.flatList p.params := by
  obtain ⟨E', A, args', hd, hm⟩ := status_callout_redex hst
  obtain ⟨fi, -, -, -, hf, hcode, -⟩ := Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  rw [hI.funcs] at hf
  obtain ⟨k, nm, p, rfl, hk⟩ := S.tramp A fi h hf hcode
  obtain ⟨hk', hpk⟩ := List.getElem?_eq_some_iff.mp hk
  have hg : gL P l.toW (.lowered (l.fid k) (witFt p) {} ⟨2⟩) = k :=
    gL_fid S.wireTy S.nodup hk' _ _ _
  have hdm : Silmaril.Wasm.SingleThreaded.decompose? (Store.mapH (gL P l.toW) y.1)
      (y.2.config (Store.mapH (gL P l.toW) y.1)).code = some (E', A, k, args') := by
    refine (decompose?_config_mapH (gL P l.toW) y.1 y.2).trans ?_
    rw [hd]
    simp only [Option.map_some, mapR, hg]
  obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hI.rel
  obtain ⟨ts, hs, ht⟩ := LInv.typedH S hI
  obtain ⟨E, a, args, hdx, -, -, hargs⟩ := callout_back P hL hs ht hdm
  have hm' : args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys := by
    have hmm : (args.map (linkMap s₀ ρc).val).mapM Silmaril.Wasm.SingleThreaded.toFlat? =
        some ys := hargs ▸ hm
    rwa [map_val_flat _ hmm] at hmm
  have hdx' : Silmaril.Wasm.SingleThreaded.decompose? (x.2.config x.1).store
      (x.2.config x.1).code = some (E, a, k, args) := by
    rw [Silmaril.Wasm.SingleThreaded.Thread.config_store]
    exact hdx
  obtain ⟨e, he⟩ := SEnvTyping.sstep_callout_typed S.impWf (valEnv_throwsBelow Ii _) hI.run hdx'
  have hek := ifaceOp?_some he
  have h2 : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (Ii.imports.get e.1).params args :=
    hek.2 ▸ e.2.2
  rw [imports_get S.impGood S.impInst e k hk' hek.1, hpk] at h2
  exact ⟨k, nm, p, E, a, args, e, rfl, hk, hdx, hm', he, flat_types_of_hasVal h2 hm'⟩

/-- **After a returned nested call the invariant holds again**, with the exporter's store after
a returned call `RetAt` (`LInv.resume` over `HStat`). -/
theorem LInv.resumeH (S : HStat P l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P l.toW Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π) {k : Nat} {nm : String} {w : Nat}
    {xe : SimpleExport} {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val} {e : Ii.E.Op}
    (hk : l.imp.imports[k]? = some (nm, xe.ty)) (hxe : l.exp.exports[w]? = some xe)
    (hdx : Silmaril.Wasm.SingleThreaded.decompose? x.1 (x.2.config x.1).code = some (E, a, k, args))
    (he : Ii.importOp? k args = some e) {ys : List Flat} {ws : List Silmaril.Wasm.Component.Val}
    (hws : liftArgs xe.ty.params ys = some ws) {ev : CoreSt (E3 P)}
    (hrun : Relation.ReflTransGen (CoreStep (E3 P))
      (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
        (lowerArgs xe.ty.params ws)) ev)
    {zs : List Flat} (hzs : (E3 P).status ev.1 ev.2 = .returned (.values zs))
    {us : List Silmaril.Wasm.Component.Val} (hus : liftArgs xe.ty.results zs = some us) :
    ∃ π', LInv P l.toW Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f
        (ev.1, (E3 P).resume ev.1 y.2 (.values (lowerArgs xe.ty.results us)))
        (x.1, Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2
          (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))) π' ∧
      RetAt P l.exp Ie xe ws π us π' := by
  obtain ⟨ρp, Op, ρc, Oc, hL, hR⟩ := hI.rel
  have hmem : xe ∈ l.exp.exports := List.mem_of_getElem? hxe
  have typed : ValTy.checkList xe.ty.params ws = true :=
    Silmaril.Wasm.Component.checkList_of_liftArgs hws
  obtain ⟨π', ρp', Op', hR', hF', -, hval, -⟩ := exp_run (vs := ws) S.expInst
    (S.expGood.core xe hmem) typed hI.wf (gL P l.toW) hR hI.fnE (S.owned xe hmem) hrun
  obtain ⟨hRet, hwf'⟩ := (hval zs hzs).2.2 us hus
  have hfe : ev.1.funcs = y.1.funcs :=
    reach_funcs' (x := (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (Ie.addrs.getD xe.core 0) (lowerArgs xe.ty.params ws))) (coreSteps_internalP hrun)
  have hfm : (Store.mapH (gL P l.toW) ev.1).funcs = (Store.mapH (gL P l.toW) y.1).funcs :=
    mapH_funcs_eq (gL P l.toW) hfe
  have hL1 : LinkSt s₀ ρc Oc x (Store.mapH (gL P l.toW) ev.1, y.2) :=
    linkSt_transport hL hfm hR'.rc
  have hL2 : LinkSt s₀ ρc Oc
      (x.1, Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2
        (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)))
      (Store.mapH (gL P l.toW) ev.1, Silmaril.Wasm.SingleThreaded.resumeResult
        (Store.mapH (gL P l.toW) ev.1) y.2
        (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))) :=
    link_resume hL1 hdx (ofFlat_scalar _)
  have hres : (E3 P).resume ev.1 y.2 (.values (lowerArgs xe.ty.results us)) =
      Silmaril.Wasm.SingleThreaded.resumeResult (Store.mapH (gL P l.toW) ev.1) y.2
        (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)) :=
    (resume_values ev.1 y.2 _).trans (resumeResult_mapH (gL P l.toW) ev.1 y.2 _).symm
  have hcheck : ValTy.checkList xe.ty.results us = true :=
    Silmaril.Wasm.Component.checkList_of_liftArgs hus
  have hek : e.1.val = k ∧ e.2.1 = args := ifaceOp?_some he
  have hdx' : Silmaril.Wasm.SingleThreaded.decompose? (x.2.config x.1).store
      (x.2.config x.1).code = some (E, a, k, args) :=
    (Silmaril.Wasm.SingleThreaded.Thread.config_store x.1 x.2).symm ▸ hdx
  have hstep : Silmaril.Wasm.Game.SStep P (valEnv Ii) (x.2.config x.1, ())
      (⟨(x.2.config x.1).store, (x.2.config x.1).frame,
        E.fill (Silmaril.Wasm.Execution.Core.Result.values
          ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)).toAdmin⟩, ()) :=
    Silmaril.Wasm.Game.SStep.answer (P := P) (L := valEnv Ii) (q := ()) (q' := ())
      (w := .values ⟨_, resAnswerH S hk hek.1 hcheck⟩) hdx' he ⟨_, rfl⟩
  have hcfg := resumeResult_config hdx'
    (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))
  refine ⟨π', ⟨⟨ρp', Op', ρc, Oc, hres ▸ hL2, hR'⟩, hF', hwf', hfe.trans hI.funcs, ?_⟩, hRet⟩
  show Silmaril.Wasm.Game.SSteps P (valEnv Ii) _ (Silmaril.Wasm.SingleThreaded.Thread.config x.1
    (Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2 _), ())
  rw [hcfg]
  exact hI.run.tail hstep

/-- **A trapping run of the exporter in a nested call** is a trapped call (`TrapAt`) of the
exporter's specification, and `LReady` holds at the core store of the trap
(`lready_expTrap` over `HStat`). -/
theorem lready_expTrapH {u : Store Nat} (S : HStat P l Ie Ii u F₀ B (ownOf s₀))
    {cs : Store (CanonHost (E3 P))} (hR : LReady P l.toW Ie Ii s₀ u₀ F₀ cs u π)
    {z : Store Nat × STh} {π' : Store Nat}
    (hI : LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y z π')
    {xe : SimpleExport} (hxe : xe ∈ l.exp.exports) {ws : List Silmaril.Wasm.Component.Val}
    (typed : ValTy.checkList xe.ty.params ws = true) {e : CoreSt (E3 P)}
    (he : Relation.ReflTransGen (CoreStep (E3 P))
      (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
        (lowerArgs xe.ty.params ws)) e)
    (hend : (E3 P).status e.1 e.2 = .returned .trap ∨
      ∃ zs, (E3 P).status e.1 e.2 = .returned (.values zs) ∧ liftArgs xe.ty.results zs = none) :
    ∃ π₂, TrapAt P l.exp Ie xe ws π' π₂ ∧ LReady P l.toW Ie Ii s₀ u₀ F₀ e.1 z.1 π₂ := by
  have hR' := lready_after hR hI
  obtain ⟨ρp, Op, ρc, Oc, -, hR4⟩ := hI.rel
  obtain ⟨nm, hcx⟩ := S.expGood.core xe hxe
  have hk : xe.core < l.exp.mod.exports.length := (List.getElem?_eq_some_iff.mp hcx).1
  have hO' : Op.fn (Ie.addrs.getD xe.core 0) := hR4.fnp ▸ S.owned xe hxe
  have hL₀ := exp_invoke hR4.rp hI.fnE hO' (lowerArgs xe.ty.params ws)
  obtain ⟨ts, htyped, -⟩ := Silmaril.Wasm.Game.ScalarInstance.invoke_typed hI.wf
    (opAt S.expInst hk (exp_hxs hcx typed hk))
  have hrun : Silmaril.Wasm.Game.Reach P (Store.mapH (gL P l.toW) y.1,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
        (lowerArgs xe.ty.params ws)) (Store.mapH (gL P l.toW) e.1, e.2) :=
    reach_mapH (gL P l.toW) (coreSteps_internalP he)
  obtain ⟨⟨π₂, t'⟩, ρp', Op', prun, hL, hgr, htc, hs', ht'⟩ :=
    reach_link_back hrun hL₀ hI.wf.storeOk htyped
  have hrel : PartRel ρp' Op' π₂ (Store.mapH (gL P l.toW) e.1) := by
    have h := hL.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store, reloc_empty] at h
  have hcode : ((e.2).config (Store.mapH (gL P l.toW) e.1)).code = ((e.2).config e.1).code :=
    config_code_mapH (gL P l.toW) e.1 e.2
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

end Inv

/-! ## Rounds, backward -/

/-- **How a run of a round ends, backward**: from the part `x` with the exporter at `π` and the
host in state `s`, the run `tr` to `m'` makes the core import calls `rs` of the importer's
instance, related by `ImpRel` to component import calls `dss` that are an `ExpRunH` segment of
the exporter from `π` to `π₁`, whose host calls are answered by `g` from `s` to `s'`
(`HostRun`); then either the importer's core phase exits (in an `extG` extension of the frame in
host state `s'`, with `LInv` at its end `z`, and the rounds a path of the importer's instance
before any continuation from `z`), or the call traps (`m'` in host state `s'`, `LReady` at its
core store, the rounds followed by the trap answer a path of the instance). -/
def RoundBackH (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (l : HLinked2)
    (Ie Ii : Silmaril.Wasm.Game.ScalarInstance) (s₀ u₀ u : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (M₀ : Machine.Config (E3 P) σ)
    (th : Option ThreadId) (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P)))
    (segs : List (Seg (E3 P) σ)) (rest : List (Activation (E3 P) σ)) (f : Ii.F.Op)
    (x : Store Nat × STh) (π : Store Nat) (s : σ) (tr : List (Label (E3 P) σ))
    (m' : Machine.Config (E3 P) σ) (out : CallOutcome) : Prop :=
  ∃ (rs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
    (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)))
    (π₁ : Store Nat) (s' : σ),
    List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) rs dss ∧
    HLinked2.ExpRunH P l Ie π dss.flatten π₁ ∧ HostRun g s (l.hostCalls dss.flatten) s' ∧
    ((∃ (ιe' : InstState) (SL' : List Subtask) (CL' : List (Caller (E3 P)))
        (TL' : List (Runtime.Task (E3 P))) (HL' : List Runtime.Thread)
        (C' : List (Option (Activation (E3 P) σ))) (pre : List (Label (E3 P) σ))
        (lb : Label (E3 P) σ) (m₁ : Machine.Config (E3 P) σ) (tr₂ : List (Label (E3 P) σ))
        (yc : CoreSt (E3 P)) (z : Store Nat × STh),
        tr = pre ++ tr₂ ∧ ThreadsOk ιe' ∧ (∀ h ys, (E3 P).status yc.1 yc.2 ≠ .callout h ys) ∧
        CoreExit (extG M₀ ιe' SL' CL' TL' HL' C' s') th K segs rest yc lb m₁ ∧
        Steps prof (fun _ _ => false) (DI P impl) m₁ tr₂ m' ∧
        LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f yc z π₁ ∧
        ∀ (rest' : List (Move Ii.E Ii.F)) (q : Ii.HState),
          (∀ s t, Silmaril.Wasm.Game.Reach P (s, t) z → Ii.Path P (.running f s t) rest' q) →
          Ii.Path P (.running f x.1 x.2) (callMoves rs ++ rest') q) ∨
      (∃ u₁ : Store Nat, out = .trap ∧ LReady P l.toW Ie Ii s₀ u₀ F₀ m'.core u₁ π₁ ∧
        m'.host = s' ∧
        Ii.Path P (.running f x.1 x.2) (callMoves rs ++ [.inr (.ans f .trap)]) (.idle u₁)))

section Rounds

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ u : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {M₀ : Machine.Config (E3 P) σ}
  {th : Option ThreadId} {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))}
  {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)} {f : Ii.F.Op}
  {impl : HostImpl (E3 P) σ}

/-- A round answered and continued: one more core import call answered `wv`, related to the
component import calls `ds`, before a `RoundBackH` from the resumed part. -/
theorem RoundBackH.cons {x x₁ : Store Nat × STh} {π π₂ : Store Nat} {s s₁ : σ}
    {tr tr₅ pre₀ : List (Label (E3 P) σ)} {m' : Machine.Config (E3 P) σ} {out : CallOutcome}
    {e : Ii.E.Op} {wv : Ii.E.Ar e} {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val}
    {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
    (htr : tr = pre₀ ++ tr₅)
    (hr₁ : Silmaril.Wasm.Game.Reach P x x₁)
    (hdx : Silmaril.Wasm.SingleThreaded.decompose? x₁.1 (x₁.2.config x₁.1).code =
      some (E, a, e.1.val, args))
    (he : Ii.importOp? e.1.val args = some e)
    (hrel : Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii ⟨e, wv⟩ ds)
    (hexp : ∀ {dss' : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)} {π' : Store Nat},
      HLinked2.ExpRunH P l Ie π₂ dss' π' → HLinked2.ExpRunH P l Ie π (ds ++ dss') π')
    (hhr : ∀ {dss' : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)} {s' : σ},
      HostRun g s₁ (l.hostCalls dss') s' → HostRun g s (l.hostCalls (ds ++ dss')) s')
    (H : RoundBackH prof P impl g l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f
      (x₁.1, Silmaril.Wasm.SingleThreaded.resumeResult x₁.1 x₁.2
        (Silmaril.Wasm.Game.Answer.toResult wv)) π₂ s₁ tr₅ m' out) :
    RoundBackH prof P impl g l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f x π s tr m' out := by
  obtain ⟨rs, dss, π₁, s', hrel', hexp', hhr', hend⟩ := H
  have hco : Silmaril.Wasm.Game.CalloutAt x₁.1 x₁.2 e.1.val args := ⟨E, a, hdx⟩
  refine ⟨⟨e, wv⟩ :: rs, ds :: dss, π₁, s', .cons hrel hrel', hexp hexp', hhr hhr', ?_⟩
  rcases hend with ⟨ιe', SL', CL', TL', HL', C', pre, lb, m₁, tr₂, yc, z, htr', hte', hnco, hx,
    r, hIz, hpath⟩ | ⟨u₁, hout, hRd, hh, hpath⟩
  · refine .inl ⟨ιe', SL', CL', TL', HL', C', pre₀ ++ pre, lb, m₁, tr₂, yc, z, ?_, hte', hnco, hx,
      r, hIz, fun rest' q hk => .cons (.ucall hr₁ hco he) (.cons (.uret wv) (hpath rest' q hk))⟩
    rw [htr, htr', List.append_assoc]
  · exact .inr ⟨u₁, hout, hRd, hh, .cons (.ucall hr₁ hco he) (.cons (.uret wv) hpath)⟩

/-- A round ending at once in a trap of the call: the core import call answered by a trap, its
component import calls `ds`. -/
theorem RoundBackH.trap1 {x x₁ : Store Nat × STh} {π π₁ : Store Nat} {s s' : σ}
    {tr : List (Label (E3 P) σ)} {m' : Machine.Config (E3 P) σ}
    {e : Ii.E.Op} {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val}
    {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
    (hr₁ : Silmaril.Wasm.Game.Reach P x x₁)
    (hdx : Silmaril.Wasm.SingleThreaded.decompose? x₁.1 (x₁.2.config x₁.1).code =
      some (E, a, e.1.val, args))
    (he : Ii.importOp? e.1.val args = some e)
    (hrel : Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii ⟨e, .trap⟩ ds)
    (hexp : HLinked2.ExpRunH P l Ie π ds π₁) (hhr : HostRun g s (l.hostCalls ds) s')
    (hRd : LReady P l.toW Ie Ii s₀ u₀ F₀ m'.core x₁.1 π₁) (hh : m'.host = s') :
    RoundBackH prof P impl g l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f x π s tr m' .trap := by
  have hP : Ii.Path P (.running f x.1 x.2)
      [.inl (.ask e), .inl (.ans e .trap), .inr (.ans f .trap)] (.idle x₁.1) :=
    path_trap_round (f := f) (zs := x₁.1) (zt := x₁.2) hdx he x.1 x.2 hr₁
  refine ⟨[⟨e, .trap⟩], [ds], π₁, s', .cons hrel .nil, ?_, ?_, .inr ⟨x₁.1, rfl, hRd, hh, hP⟩⟩
  · simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hexp
  · simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hhr

/-- **Inversion of a round of the importer with nested and host calls**: every machine run of
the importer's core phase from `LInv`, in an `extG` extension of the call's frame, that ends
where a call outcome holds is a round of the specification (`RoundBackH`). -/
theorem rounds_invH (S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀)) (hF : GFrame M₀ th)
    (hH : HostHandlesB prof P impl g l M₀ th K segs rest) (hT : l.HostTyped g) {cs₀ : Store (CanonHost (E3 P))} {π₀ : Store Nat}
    (hR : LReady P l.toW Ie Ii s₀ u₀ F₀ cs₀ u π₀) {cid : CallId} :
    ∀ (n : Nat) (ιe : InstState) (SL : List Subtask) (CL : List (Caller (E3 P)))
      (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
      (C : List (Option (Activation (E3 P) σ))) (s : σ) (y : CoreSt (E3 P)) (x : Store Nat × STh)
      (π : Store Nat) (tr : List (Label (E3 P) σ)) (m' : Machine.Config (E3 P) σ)
      (out : CallOutcome),
      tr.length ≤ n → ThreadsOk ιe →
      LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x π →
      Steps prof (fun _ _ => false) (DI P impl)
        (coreCfg (extG M₀ ιe SL CL TL HL C s) th K segs rest y) tr m' →
      out.Holds (fun _ _ => false) cid m' →
      RoundBackH prof P impl g l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f x π s tr m' out := by
  intro n
  induction n with
  | zero =>
    intro ιe SL CL TL HL C s y x π tr m' out hn _ _ hs ho
    have htr : tr = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
    subst htr
    cases hs
    exact absurd ho ((coreCfg_extG_live M₀ ιe SL CL TL HL C s th K segs rest y).not_holds _ _)
  | succ n ih =>
    intro ιe SL CL TL HL C s y x π tr m' out hn hte hI hs ho
    rcases coreCfg_steps_inv' hs with ⟨y', -, rfl⟩ | ⟨y₁, pre, lb, m₁, tr₂, hy, rfl, st, hx, r⟩
    · exact absurd ho ((coreCfg_extG_live M₀ ιe SL CL TL HL C s th K segs rest y').not_holds _ _)
    obtain ⟨⟨zs, zt⟩, hI₁, hr₁⟩ := LInv.reachH S hI hy
    by_cases hco : ∃ h ys, (E3 P).status y₁.1 y₁.2 = .callout h ys
    swap
    · exact ⟨[], [], π, s, .nil, .nil π, .nil s, .inl ⟨ιe, SL, CL, TL, HL, C, pre ++ [lb], lb, m₁,
        tr₂, y₁, (zs, zt), by simp, hte, fun h ys e => hco ⟨h, ys, e⟩, hx, r, hI₁,
        fun rest' q hk => hk x.1 x.2 hr₁⟩⟩
    obtain ⟨h, ys, hst⟩ := hco
    obtain ⟨k, nm, p, E, a', args, e, rfl, hk, hdx, hm, he', hyty⟩ := LInv.calloutH S hI₁ hst
    obtain ⟨hek, rfl⟩ := ifaceOp?_some he'
    subst hek
    have r' : Steps prof (fun _ _ => false) (DI P impl)
        (coreCfg (extG M₀ ιe SL CL TL HL C s) th K segs rest y₁) (lb :: tr₂) m' := .cons st r
    have hRdy := lready_after hR hI₁
    have hkl : e.1.val < l.imp.imports.length := (List.getElem?_eq_some_iff.mp hk).1
    have hfilt : e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys := filterMap_of_mapM hm
    -- the import's arguments do not lift: no component import call, a trap
    have hnone : liftArgs p.params ys = none →
        Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii ⟨e, .trap⟩ [] := by
      intro hws
      refine ⟨nm, p, none, hk, rfl, ?_⟩
      show match liftArgs p.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) with
        | none => _ | some ws => _
      rw [hfilt, hws]
      exact ⟨rfl, rfl⟩
    have hlen : ∀ tr₀ tr₅ : List (Label (E3 P) σ), lb :: tr₂ = tr₀ ++ tr₅ → tr₀ ≠ [] →
        tr₅.length ≤ n := by
      intro tr₀ tr₅ e₀ hne
      have h₁ : (pre ++ lb :: tr₂).length ≤ n + 1 := hn
      rw [e₀] at h₁
      have h₂ : 0 < tr₀.length := List.length_pos_iff.mpr hne
      simp only [List.length_append] at h₁
      omega
    by_cases hwk : e.1.val < l.wire.length
    · -- a wired import: a nested call of the exporter
      obtain ⟨wi, hw⟩ : ∃ wi, l.wire[e.1.val]? = some wi := ⟨_, List.getElem?_eq_getElem hwk⟩
      obtain ⟨xe, hxe, hty⟩ := S.wireTy.ty e.1.val wi hw
      have hpx : xe.ty = p := by
        rw [hk] at hty
        simp only [Option.map_some, Option.some.injEq] at hty
        exact hty.symm
      subst hpx
      have hmi : (nm, xe.ty) ∈ l.imp.imports := List.mem_of_getElem? hk
      have hres : xe.ty.results.length ≤ 1 := (S.arity.2 _ hmi).2.2
      have hfl : ArenaField.funcs.get? M₀.store (l.fid e.1.val) =
          some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) :=
        S.lifted e.1.val wi xe hw hxe
      have hsite : LinkSite M₀ y₁ (.lowered (l.fid e.1.val) (witFt xe.ty) {} ⟨2⟩) ys :=
        LInv.siteH S hI₁ hk hw hxe hyty
      obtain ⟨hpf, hys, hmaxp, hrf, hmaxr, hexpS⟩ := site_of hsite hfl hres
      have hB := hF.lframe ιe SL CL TL HL C s
      have hf' : ArenaField.funcs.get? (extG M₀ ιe SL CL TL HL C s).store (l.fid e.1.val) =
          some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) :=
        (funcs_extG _ _ _ _ _ _ _ _ _).trans hfl
      obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe [] C
      have hadd := addThread?_ok hte
        ⟨(extN (extG M₀ ιe SL CL TL HL C s) ιe [] C).store.threads.length⟩
      have hrem := removeThread?_enter ιe
        ⟨(extN (extG M₀ ιe SL CL TL HL C s) ιe [] C).store.threads.length⟩
      have r'' : Steps prof (fun _ _ => false) (DI P impl)
          (coreCfg (extN (extG M₀ ιe SL CL TL HL C s) ιe [] C) th K segs rest y₁) (lb :: tr₂)
          m' := by
        rw [extN_extG_nil]
        exact r'
      have hxm : xe ∈ l.exp.exports := List.mem_of_getElem? hxe
      have hwl : wi < l.exp.exports.length := (List.getElem?_eq_some_iff.mp hxe).1
      have hxw : l.exp.exports[(⟨wi, hwl⟩ : Fin l.exp.exports.length)] = xe :=
        (List.getElem?_eq_some_iff.mp hxe).2
      cases hws : liftArgs xe.ty.params ys with
      | none =>
        have hT' := nest_trap_argsTSH (prof := prof) (impl := impl)
          (extG M₀ ιe SL CL TL HL C s) ιe _ [] C th K segs rest y₁ (l.fid e.1.val) _ xe.ty ys ιi
          hst (hB.entry _ _ _ _ _) hi hleave hf' hB.len hadd hpf hys hmaxp hws
        obtain ⟨hout, hcore, hhost⟩ := trapsAtSH_out hT' r'' ho
        subst hout
        exact RoundBackH.trap1 hr₁ hdx he' (hnone hws) (.nil π) (.nil s) (hcore ▸ hRdy) hhost
      | some ws =>
        have hfw : liftArgs xe.ty.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) =
            some ws := by rw [hfilt, hws]
        obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr₁, hrun, hctl, hcore, hlock, hhost, hret,
          htrap⟩ := nest_atTSH (prof := prof) (impl := impl)
            (extG M₀ ιe SL CL TL HL C s) ιe _ [] C th K segs rest y₁ (l.fid e.1.val) _ xe.ty ys ιi
            ws hst (hB.entry _ _ _ _ _) hi hleave hf' hB.len hadd hrem hpf hys hmaxp hws hres hrf
            hmaxr
        rcases hrun.inv r'' with hl' | ⟨tr'', e₁, r₂⟩
        · exact absurd ho (hl'.not_holds _ _)
        have hM : M₁ = coreCfg M₁ th' K' segs' rest' (y₁.1,
            Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
              (lowerArgs xe.ty.params ws)) := by
          rw [← hcore]
          exact eq_coreCfg hctl
        rw [hM] at r₂
        have hlive : ∀ z, Live (coreCfg M₁ th' K' segs' rest' z) :=
          fun z => ⟨List.cons_ne_nil _ _, hlock⟩
        rcases coreCfg_steps_inv' r₂ with ⟨ev, -, rfl⟩ |
            ⟨ev, pre₂, l', m₂, tr₃, hev, rfl, -, hx₂, r₃⟩
        · exact absurd ho ((hlive ev).not_holds _ _)
        obtain ⟨hnco, htyz⟩ := hexpS ws hws ev hev
        have hds₁ := LinkedSessionIR.impRel_trap (I := Ii) (e := e) hk hfw
        have hw' : l.wire[(⟨e.1.val, hkl⟩ : Fin l.imp.imports.length).val]? = some wi := hw
        rcases hx₂ with ⟨zs', hzs, rfl, rfl⟩ | ⟨htr, rfl, rfl⟩ | ⟨h', ys', hc'⟩
        · cases hus : liftArgs xe.ty.results zs' with
          | none =>
            obtain ⟨hout, hcore', hhost'⟩ :=
              trapsAtSH_out (htrap ev zs' (htyz zs' hzs) hus) r₃ ho
            subst hout
            obtain ⟨π₂, hTr, hR₂⟩ := lready_expTrapH S hR hI₁ hxm
              (Silmaril.Wasm.Component.checkList_of_liftArgs hws) hev (.inr ⟨zs', hzs, hus⟩)
            exact RoundBackH.trap1 hr₁ hdx he' hds₁
              (.trap ⟨wi, hwl⟩ hw' (hxw ▸ hTr) (.nil π₂))
              (hostRun_wired (by exact hwk) (.nil s)) (hcore' ▸ hR₂) hhost'
          | some us =>
            obtain ⟨tr₄, h₄⟩ := hret ev zs' us (htyz zs' hzs) hus
            rcases h₄.inv r₃ with hl' | ⟨tr₅, e₃, r₅⟩
            · exact absurd ho (hl'.not_holds _ _)
            rw [extN_extG] at r₅
            obtain ⟨π₂, hI₂, hRet⟩ := LInv.resumeH S hI₁ hk hxe hdx he' hws hev hzs hus
            have htr : lb :: tr₂ = (tr₁ ++ (pre₂ ++ Label.tau :: tr₄)) ++ tr₅ := by
              rw [e₁, e₃]
              simp only [List.append_assoc, List.cons_append]
            have hlen₅ : tr₅.length ≤ n := hlen _ _ htr (by simp)
            have hcheck : ValTy.checkList xe.ty.results us = true :=
              Silmaril.Wasm.Component.checkList_of_liftArgs hus
            have hrel₁ := impRel_link (l := l.toL2) hk rfl rfl hm hws hcheck
              (.values ⟨_, resAnswerH S hk rfl hcheck⟩) rfl
            have hend := ih _ _ _ _ _ _ s _ _ π₂ tr₅ m' out hlen₅ (threadsOk_after _ _) hI₂ r₅ ho
            refine RoundBackH.cons (pre₀ := pre ++ (tr₁ ++ (pre₂ ++ Label.tau :: tr₄)))
              (by simp only [htr, List.append_assoc, List.cons_append]) hr₁ hdx he' hrel₁ ?_ ?_ hend
            · intro dss' π' h'
              exact .ret ⟨wi, hwl⟩ hw' (hxw ▸ hRet) h'
            · intro dss' s' h'
              exact hostRun_wired (by exact hwk) h'
        · -- the exporter traps
          have e₃ := steps_of_locked rfl rfl r₃
          subst e₃
          have hout := holds_trapCfgD ho
          subst hout
          obtain ⟨π₂, hTr, hR₂⟩ := lready_expTrapH S hR hI₁ hxm
            (Silmaril.Wasm.Component.checkList_of_liftArgs hws) hev (.inl htr)
          exact RoundBackH.trap1 hr₁ hdx he' hds₁ (.trap ⟨wi, hwl⟩ hw' (hxw ▸ hTr) (.nil π₂))
            (hostRun_wired (by exact hwk) (.nil s)) hR₂ hhost
        · exact absurd hc' (hnco h' ys')
    · -- a host import: a host callout
      obtain ⟨hi, hhost⟩ := host_get_of S.wireTy hk hwk
      have hp2 : l.host[e.1.val - l.wire.length].2 = p := by rw [hhost]
      have hfid : l.fid e.1.val = ⟨e.1.val - l.wire.length⟩ := by
        simp only [HLinked2.fid, hwk, ↓reduceIte]
      have hst' : (E3 P).status y₁.1 y₁.2 =
          .callout (.lowered ⟨e.1.val - l.wire.length⟩ (witFt p) {} ⟨2⟩) ys := by
        rw [← hfid]
        exact hst
      have hge : l.wire.length ≤ (⟨e.1.val, hkl⟩ : Fin l.imp.imports.length).val :=
        Nat.le_of_not_lt hwk
      have hn : (⟨e.1.val, hkl⟩ : Fin l.imp.imports.length).val =
          l.wire.length + (⟨e.1.val - l.wire.length, hi⟩ : Fin l.host.length).val := by
        show e.1.val = l.wire.length + (e.1.val - l.wire.length)
        omega
      have hst'' : (E3 P).status y₁.1 y₁.2 = .callout (.lowered ⟨e.1.val - l.wire.length⟩
          (witFt l.host[e.1.val - l.wire.length].2) {} ⟨2⟩) ys := by
        rw [hp2]
        exact hst'
      have hys'' : ys.map (·.type) = ValTy.flatList l.host[e.1.val - l.wire.length].2.params := by
        rw [hp2]
        exact hyty
      have hHk := hH ιe SL CL TL HL C s y₁ _ hi ys hst'' hys''
      cases hws : liftArgs p.params ys with
      | none =>
        obtain ⟨hout, hcore, hhost'⟩ := trapsAtSH_out (hHk.1 (by rw [hp2]; exact hws)) r' ho
        subst hout
        exact RoundBackH.trap1 hr₁ hdx he' (hnone hws) (.nil π) (.nil s) (hcore ▸ hRdy) hhost'
      | some ws =>
        have hfw : liftArgs p.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) =
            some ws := by rw [hfilt, hws]
        have hHw := hHk.2 ws (by rw [hp2]; exact hws)
        cases hg : g s ⟨e.1.val - l.wire.length⟩ (ws.map toRefVal) with
        | none =>
          obtain ⟨hout, hcore, hhost'⟩ := trapsAtSH_out (hHw.1 hg) r' ho
          subst hout
          exact RoundBackH.trap1 hr₁ hdx he' (LinkedSessionIR.impRel_trap (I := Ii) hk hfw)
            (.host ⟨e.1.val - l.wire.length, hi⟩ hn (.nil π))
            (hostRun_host hge hi ⟨⟨e.1.val - l.wire.length, hi⟩, ws, rfl, hg, rfl⟩ (.nil s))
            (hcore ▸ hRdy) hhost'
        | some rs₁ =>
          obtain ⟨rs₁, s₁⟩ := rs₁
          obtain ⟨us, rfl, hck⟩ := hT s _ hi ws rs₁ s₁ hg
          obtain ⟨xS, cS, trH, hL⟩ := hHw.2 us s₁ hg hck
          rw [hp2] at hck hL
          rcases hL.inv r' with hl' | ⟨tr₅, e₃, r₅⟩
          · exact absurd ho (hl'.not_holds _ _)
          have hI₂ := LInv.resumeHost_fwdH S hI₁ hk hdx he' hck
          have hlen₅ : tr₅.length ≤ n := hlen _ _ e₃ (by simp)
          have hrel₁ := impRel_link (l := l.toL2) hk rfl rfl hm hws hck
            (.values ⟨_, resAnswerH S hk rfl hck⟩) rfl
          have hend := ih _ _ _ _ _ _ s₁ _ _ π tr₅ m' out hlen₅ hte hI₂ r₅ ho
          refine RoundBackH.cons (pre₀ := pre ++ (Label.tau :: trH))
            (by rw [e₃, List.append_assoc]) hr₁ hdx he' hrel₁ ?_ ?_ hend
          · intro dss' π' h'
            exact .host ⟨e.1.val - l.wire.length, hi⟩ hn h'
          · intro dss' s' h'
            exact hostRun_host hge hi ⟨⟨e.1.val - l.wire.length, hi⟩, ws, rfl, hg⟩ h'

end Rounds

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
