module

public import Silmaril.Wasm.Component.Reference.SessionDiv.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.RefSess
public import Silmaril.Proofs.Wasm.Component.Reference.CallRun

/-!
# Diverging session calls: the specification and the reference machine

For a call between calls (`ReadyAt`) of a `Simple` component in the adequate fragment:

* `callDiverges_of_divAt` (the converse of `CallRun.diverges_spec`, at every call of a
  session): a host-free infinite Core run of the lowered call (`DivAt`) is an infinite run of the
  machine's core activation, one machine step (label `core`, `Step.coreInternal`) per Core step,
  so no stuttering arises. The deterministic prefix of the call (`CallRun`: the host's
  invocation, the lowering) is a finite live run, prepended. The Core store of the
  specification is the machine's store renamed (`store_eq`); host-free steps carry over
  (`internalP_mapH'`) and start at a running status (`statusP_running_of`);
* `divAt_of_callDiverges`: the other direction at a call between calls (`CallRun.diverges_spec`
  is the case of the first call): machine divergence is divergence of the core activation, the
  run after it leaves the core phase never diverging (a resolution returns control to the host,
  a lift trap and a Core trap lock down, and the activation never calls out);
* `sessDiv_forward`, `sessDiv_inv`: through returned and trapped calls (#676's
  `sessCalls_forward`, `sess_inv`, with `resumeCfg` after a trap);
* `sessDivs_eq_refDivs`: the diverging session calls of the specification (`sessDivs`) are those
  of the reference machine (`refDivs`), at every profile and component choice profile.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.SessionDiv

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Game (InternalP statusP)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

/-! ## Generic facts -/

section Generic

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

/-- A live run followed by divergence diverges. -/
theorem lrun_diverges {m m' : Machine.Config E σ} {tr : List (Label E σ)}
    (h : LRun prof hr dispatch m tr m') (d : Diverges prof hr dispatch m') :
    Diverges prof hr dispatch m := by
  induction h with
  | refl => exact d
  | cons hl s _ ih =>
    refine Silmaril.InfiniteTrace.fold ⟨_, fun ev he => ?_, s.1⟩ (ih d)
    subst he
    exact hl.1 (Step.host_ready s.1).1

/-- **A divergent core activation is a divergent machine configuration**: one machine step
per core step. -/
theorem coreCfg_diverges_of {B : Machine.Config E σ} {th : Option ThreadId}
    {K : List FlatValue → Canon.P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {x : CoreSt E} (h : Silmaril.InfiniteTrace (CoreStep E) x) :
    Diverges prof hr dispatch (coreCfg B th K segs rest x) :=
  Silmaril.InfiniteTrace.map (coreCfg B th K segs rest) (fun a b hab => by
    obtain ⟨hst, hi⟩ := hab
    have s : Step prof hr dispatch (coreCfg B th K segs rest a) .core
        (coreCfg B th K segs rest b) := Step.coreInternal rfl hst hi
    exact ⟨.core, (fun _ he => by cases he), s⟩) h

end Generic

/-! ## Core divergence -/

variable {P : Profile} {prof : ProfileKind} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
  {cs : (core3P P).Store (CanonHost (core3P P))} {x : SimpleExport}
  {vs : List IVal} {ι : InstState} {fs : List (CFuncInst (core3P P))}
  {G : Garb P} {k j : Nat}

/-- **Specification divergence is divergence of the machine's core activation.** -/
theorem coreTrace_of_divAt (C : CallCtxAt P c I cs x vs)
    (h : DivAt P I x vs (Store.mapH (fun _ => 0) cs)) :
    Silmaril.InfiniteTrace (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) := by
  obtain ⟨g, hg0, hg⟩ := h.run
  refine ⟨fun n => (Store.mapH (someHost P) (g n).1, (g n).2), ?_, fun n => ?_⟩
  · exact (congrArg (fun y : Store Nat × STh => (Store.mapH (someHost P) y.1, y.2)) hg0).trans
      (Prod.ext (store_eq C) rfl)
  · have hs' : InternalP P (Store.mapH (someHost P) (g n).1, (g n).2)
        (Store.mapH (someHost P) (g (n + 1)).1, (g (n + 1)).2) :=
      internalP_mapH' (someHost P) (hg n)
    refine ⟨.inl ?_, hs'⟩
    show flatStatus (statusP P (Store.mapH (someHost P) (g n).1) (g n).2) = .running
    rw [statusP_running_of hs']
    rfl

/-- **Divergence of the machine's core activation is specification divergence.** -/
theorem divAt_of_coreTrace (C : CallCtxAt P c I cs x vs)
    (h : Silmaril.InfiniteTrace (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs))) :
    DivAt P I x vs (Store.mapH (fun _ => 0) cs) := by
  obtain ⟨g, hg0, hg⟩ := h
  refine ⟨C.typed, fun n => (Store.mapH (fun _ => 0) (g n).1, (g n).2),
    congrArg (fun y : CoreSt (E3 P) => (Store.mapH (fun _ => (0 : Nat)) y.1, y.2)) hg0,
    fun n => ?_⟩
  exact internalP_mapH' (fun _ => (0 : Nat))
    (show InternalP P (g n) (g (n + 1)) from (hg n).2)

/-! ## One call between calls -/

/-- **Specification divergence gives reference divergence** for a call between calls. -/
theorem callDiverges_of_divAt (C : CallCtxAt P c I cs x vs) (R : ReadyAt I cs ι G k)
    (CR : CallRun prof P cs ι fs G k j x vs I) (h : DivAt P I x vs (Store.mapH (fun _ => 0) cs)) :
    CallDiverges prof (refHost P).hr (D P) (readyCfg cs ι fs G) ⟨k⟩ ⟨j⟩ (vs.map toRefVal) := by
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := CR.run
  refine ⟨_, invoke_step R _, lrun_diverges hpre ?_⟩
  rw [eq_core_k hat.toCallAtK.ctl hat.toCallAtK.core]
  exact coreCfg_diverges_of (coreTrace_of_divAt C h)

/-- **Reference divergence gives specification divergence** for a call between calls. -/
theorem divAt_of_callDiverges (C : CallCtxAt P c I cs x vs)
    (CR : CallRun prof P cs ι fs G k j x vs I)
    (hd : CallDiverges prof (refHost P).hr (D P) (readyCfg cs ι fs G) ⟨k⟩ ⟨j⟩ (vs.map toRefVal)) :
    DivAt P I x vs (Store.mapH (fun _ => 0) cs) := by
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := CR.run
  obtain ⟨m₂, s, hd⟩ := hd
  rw [invoke_inv_k s] at hd
  have hd₀ := hpre.diverges hd
  rw [eq_core_k hat.toCallAtK.ctl hat.toCallAtK.core] at hd₀
  rcases coreCfg_diverges_inv hd₀ with hi | ⟨y, l, m₁, hy, hx, hd'⟩
  · exact divAt_of_coreTrace C hi
  exfalso
  rcases hx with ⟨ys, hst, -, rfl⟩ | ⟨hst, -, rfl⟩ | ⟨h, args, hst⟩
  · obtain ⟨-, hty, -⟩ := C.values hy hst
    cases hl : liftArgs x.ty.results ys with
    | some ws =>
      obtain ⟨tr₃, mE, hlr, rfl⟩ := hat.toCallAtK.ret y ys ws hty hl
      exact not_diverges_of_ctl_nil rfl (hlr.diverges hd')
    | none =>
      obtain ⟨mT, r, -, hlr, -, hu⟩ := hat.trapS y ys hty hl
      obtain ⟨m', ⟨l', -, s'⟩, hd''⟩ := (hlr.diverges hd').unfold
      obtain ⟨-, rfl⟩ := hu.2 _ _ s'
      exact not_diverges_trapCfg _ hd''
  · exact not_diverges_trapCfg _ hd'
  · exact C.no_callout hy hst

/-! ## Sessions -/

/-- **Specification sessions ending in a divergent call are reference ones**, between
calls. -/
theorem sessDiv_forward (hc : c.Good) (hf : c.FloatFree) (ha : c.Arity) (hI : c.mod.IsInst I)
    (j : Fin c.exports.length) (vs : List IVal)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    ∀ (calls : List (Fin c.exports.length × List IVal)) (outs : List (Option (List IVal)))
      (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState) (G : Garb P) (k : Nat)
      (s : Store Nat), ReadyAt I cs ι G k → TypedCalls c calls →
      SessSpec P c I (Store.mapH (fun _ => 0) cs) (specCalls c calls) outs s →
      DivAt P I c.exports[j] vs s →
      SessDiv prof (refHost P)
        (readyCfg cs ι (liftedFuncs P (fun k => I.addrs.getD k 0) c) G) k (callArgs c calls)
        (refOuts outs) ⟨j⟩ (vs.map toRefVal)
  | [], outs, cs, ι, G, k, s, R, _, h, hd => by
    cases h
    have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
    have C : CallCtxAt P c I cs c.exports[j] vs := ⟨hI, R.wf, hc.core _ hx, hvs⟩
    obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
    obtain ⟨hff, hffr⟩ := hf _ hx
    have CR := callRun (prof := prof) C R hff hmax hres hmaxr hffr
      (liftedFuncs_get? (P := P) c (fun k => I.addrs.getD k 0) j.isLt)
    exact .div (callDiverges_of_divAt C R CR hd)
  | (j', vs') :: calls, outs, cs, ι, G, k, s, R, ht, h, hd => by
    have h' : SessSpec P c I (Store.mapH (fun _ => 0) cs)
        ((c.exports[j'], vs') :: specCalls c calls) outs s := h
    have hvs' : ValTy.checkList c.exports[j'].ty.params vs' = true := ht _ List.mem_cons_self
    have hx : c.exports[j'] ∈ c.exports := List.getElem_mem j'.isLt
    have C : CallCtxAt P c I cs c.exports[j'] vs' := ⟨hI, R.wf, hc.core _ hx, hvs'⟩
    obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
    obtain ⟨hff, hffr⟩ := hf _ hx
    have hget := liftedFuncs_get? (P := P) c (fun k => I.addrs.getD k 0) j'.isLt
    have ht' : TypedCalls c calls := fun q hq => ht q (List.mem_cons_of_mem _ hq)
    cases h' with
    | @ret _ s₁ _ _ _ ws _ outs' hret hseq =>
      have CR := callRun (prof := prof) C R hff hmax hres hmaxr hffr hget
      obtain ⟨cs₁, hcs₁, hcall⟩ := call_forward_ret C R CR hret
      have R₁ : ReadyAt I cs₁ (InstState.removeThread 1 (enterInst ι ⟨G.threads.length⟩))
          (nextGarb G c.exports[j'] k j' (I.addrs.getD c.exports[j'].core 0) (vs'.map toRefVal)
            (ws.map toRefVal)) (k + 1) :=
        ⟨hcs₁ ▸ hret.wellFormed hI (hc.core _ hx) R.wf, threadsOk_after _ _,
          fresh_next R.fresh _ _ _ _ _⟩
      exact .ret hcall (sessDiv_forward hc hf ha hI j vs hvs calls outs' cs₁ _ _ (k + 1) s R₁ ht'
        (hcs₁ ▸ hseq) hd)
    | @trap _ s₁ _ _ _ _ outs' htrap hseq =>
      have CR := callRunT (prof := prof) C R hff hmax hres hmaxr hffr hget
      obtain ⟨m', hcall, hcore'⟩ := call_forward_trap C R CR htrap
      have hwf : I.WellFormed s₁ := htrap.wellFormed hI (hc.core _ hx) R.wf
      have hs₁ : Store.mapH (fun _ => (0 : Nat)) m'.core = s₁ := by
        rw [hcore']
        exact mapH_mapH_of_noHostFns _ _ (noHostFns_of_wf hI.2.1 hwf)
      have R₁ : ReadyAt I m'.core ι G (k + 1) :=
        resume_ready C R (hs₁ ▸ htrap)
      refine .trap hcall ?_
      rw [resumeCfg_ready]
      exact sessDiv_forward hc hf ha hI j vs hvs calls outs' m'.core ι G (k + 1) s R₁ ht'
        (hs₁ ▸ hseq) hd

/-- **Reference sessions ending in a divergent call are specification ones**, between
calls. -/
theorem sessDiv_inv (hc : c.Good) (hf : c.FloatFree) (ha : c.Arity) (hI : c.mod.IsInst I)
    (j : Fin c.exports.length) (vs : List IVal)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    ∀ (calls : List (Fin c.exports.length × List IVal))
      (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState) (G : Garb P) (k : Nat)
      (outs : List (Option (List RVal))), ReadyAt I cs ι G k → TypedCalls c calls →
      SessDiv prof (refHost P)
        (readyCfg cs ι (liftedFuncs P (fun k => I.addrs.getD k 0) c) G) k (callArgs c calls)
        outs ⟨j⟩ (vs.map toRefVal) →
      ∃ outs' s', SessSpec P c I (Store.mapH (fun _ => 0) cs) (specCalls c calls) outs' s' ∧
        outs = refOuts outs' ∧ DivAt P I c.exports[j] vs s'
  | [], cs, ι, G, k, outs, R, _, hS => by
    cases hS with
    | div hd =>
      have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
      have C : CallCtxAt P c I cs c.exports[j] vs := ⟨hI, R.wf, hc.core _ hx, hvs⟩
      obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
      obtain ⟨hff, hffr⟩ := hf _ hx
      have CR := callRun (prof := prof) C R hff hmax hres hmaxr hffr
        (liftedFuncs_get? (P := P) c (fun k => I.addrs.getD k 0) j.isLt)
      exact ⟨[], _, .nil _, rfl, divAt_of_callDiverges C CR hd⟩
  | (j', vs') :: calls, cs, ι, G, k, outs, R, ht, hS => by
    have hvs' : ValTy.checkList c.exports[j'].ty.params vs' = true := ht _ List.mem_cons_self
    have ht' : TypedCalls c calls := fun q hq => ht q (List.mem_cons_of_mem _ hq)
    cases hS with
    | ret hcall hS' =>
      obtain ⟨cs₁, ι₁, G₁, ws, rfl, hret, rfl, R₁⟩ := seq_step hc hf ha hI R j' hvs' hcall
      obtain ⟨outs', s', hseq, rfl, hd⟩ :=
        sessDiv_inv hc hf ha hI j vs hvs calls cs₁ ι₁ G₁ (k + 1) _ R₁ ht' hS'
      exact ⟨some ws :: outs', s', .ret hret hseq, rfl, hd⟩
    | @trap _ m₁ _ _ _ _ _ _ _ hcall hS' =>
      have hx : c.exports[j'] ∈ c.exports := List.getElem_mem j'.isLt
      have C : CallCtxAt P c I cs c.exports[j'] vs' := ⟨hI, R.wf, hc.core _ hx, hvs'⟩
      obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
      obtain ⟨hff, hffr⟩ := hf _ hx
      have htrap := call_trap_inv C R hff hmax hres hmaxr hffr
        (liftedFuncs_get? (P := P) c (fun k => I.addrs.getD k 0) j'.isLt) hcall
      rw [resumeCfg_ready] at hS'
      obtain ⟨outs', s', hseq, rfl, hd⟩ := sessDiv_inv hc hf ha hI j vs hvs calls m₁.core
        ι G (k + 1) _ (resume_ready C R htrap) ht' hS'
      exact ⟨none :: outs', s', .trap htrap hseq, rfl, hd⟩

/-! ## From the empty store -/

/-- **Diverging specification sessions are diverging reference sessions.** -/
theorem refDivs_of_sessDivs (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    (calls : List (Fin c.exports.length × List IVal)) (j : Fin c.exports.length)
    (vs : List IVal) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {outs : List (Option (List IVal))} (h : outs ∈ sessDivs P c calls j vs) :
    outs ∈ refDivs P prof c calls j vs := by
  obtain ⟨I, s, hI, hseq, hd⟩ := h
  obtain ⟨I', cs, hI', hcs, hinst⟩ := inst_forward P prof hc.good hc.inst
  obtain rfl := NumModule.IsInst.unique hI' hI
  have hS := sessDiv_forward (prof := prof) hc.good hc.floatFree hc.arity hI' j vs hvs calls
    outs cs {} ⟨[], [], [], [], [], [], []⟩ 0 s (ready_afterInst hI' hcs) ht (hcs ▸ hseq) hd
  refine ⟨afterInst P cs (liftedFuncs P (fun k => I'.addrs.getD k 0) c), ⟨0⟩, exportMap c,
    calls.map fun q => (⟨q.1⟩ : FuncId), ⟨j⟩, hinst, mapM_lookup hc.good calls,
    exportMap_lookup hc.good j j.isLt, ?_⟩
  rw [zip_callArgs]
  exact hS

/-- **Diverging reference sessions are diverging specification sessions.** -/
theorem sessDivs_of_refDivs (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    (calls : List (Fin c.exports.length × List IVal)) (j : Fin c.exports.length)
    (vs : List IVal) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {outs : List (Option (List IVal))} (h : outs ∈ refDivs P prof c calls j vs) :
    outs ∈ sessDivs P c calls j vs := by
  obtain ⟨I, cs, hI, hcs, hinst⟩ := instPhase P prof c hc.good hc.inst
  obtain ⟨m₀, inst, es, fs, f, hr, hfs, hf, hS⟩ := h
  have he : m₀ = afterInst P cs (liftedFuncs P (fun k => I.addrs.getD k 0) c) ∧
      inst = ⟨0⟩ ∧ es = exportMap c := by
    simpa only [InstResult.instance.injEq] using hinst _ hr
  have hfs' : fs = calls.map fun q => (⟨q.1⟩ : FuncId) :=
    Option.some.inj (hfs.symm.trans (he.2.2 ▸ mapM_lookup hc.good calls))
  have hf' : f = ⟨j⟩ :=
    Option.some.inj (hf.symm.trans (he.2.2 ▸ exportMap_lookup hc.good j j.isLt))
  have hS₁ : SessDiv prof (refHost P) (readyCfg cs {}
      (liftedFuncs P (fun k => I.addrs.getD k 0) c) ⟨[], [], [], [], [], [], []⟩) 0
      (callArgs c calls) (refOuts outs) ⟨j⟩ (vs.map toRefVal) := by
    have hS₀ : SessDiv prof (refHost P) (afterInst P cs (liftedFuncs P
        (fun k => I.addrs.getD k 0) c)) 0 (fs.zip ((calls.map fun q =>
          (c.exports[q.1].name, q.2.map toRefVal)).map Prod.snd)) (refOuts outs) f
          (vs.map toRefVal) := he.1 ▸ hS
    rw [← zip_callArgs, ← hfs', ← hf']
    exact hS₀
  obtain ⟨outs', s, hseq, he', hd⟩ := sessDiv_inv hc.good hc.floatFree hc.arity hI j vs hvs
    calls cs {} _ 0 _ (ready_afterInst hI hcs) ht hS₁
  obtain rfl := refOuts_inj he'
  exact ⟨I, s, hI, hcs ▸ hseq, hd⟩

/-- **The diverging session calls of the specification are those of the reference
machine.** -/
theorem sessDivs_eq_refDivs (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    (calls : List (Fin c.exports.length × List IVal)) (j : Fin c.exports.length)
    (vs : List IVal) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    sessDivs P c calls j vs = refDivs P prof c calls j vs :=
  Set.ext fun _ => ⟨refDivs_of_sessDivs P prof c hc calls j vs ht hvs,
    sessDivs_of_refDivs P prof c hc calls j vs ht hvs⟩

/-- **A single call from the instance's store**: specification divergence is reference
divergence of the first call after instantiation. -/
theorem divAt_iff_refDiv (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I) (j : Fin c.exports.length)
    (vs : List IVal) (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    DivAt P I c.exports[j] vs I.store ↔ [] ∈ refDivs P prof c [] j vs := by
  rw [← sessDivs_eq_refDivs P prof c hc [] j vs (fun _ h => nomatch h) hvs]
  constructor
  · exact fun hd => ⟨I, I.store, hI, .nil _, hd⟩
  · rintro ⟨I', s, hI', hs, hd⟩
    obtain rfl := NumModule.IsInst.unique hI' hI
    cases hs
    exact hd

/-- **`RefSessEquivD` with the divergence clause on reference-machine runs.** -/
theorem refSessEquivD_iff {P : Profile} {prof : ProfileKind} {c c' : Simple}
    (hc : c.Adequate) (hc' : c'.Adequate) :
    RefSessEquivD P prof c c' ↔ ∃ h : RefSessEquiv P prof c c',
      ∀ (calls : List (Fin c.exports.length × List IVal)) (j : Fin c.exports.length)
        (vs : List IVal), TypedCalls c calls → ValTy.checkList c.exports[j].ty.params vs = true →
        refDivs P prof c calls j vs =
          refDivs P prof c' (castCalls h.len calls) (Fin.cast h.len j) vs := by
  have key : ∀ (h : RefSessEquiv P prof c c') (calls : List (Fin c.exports.length × List IVal))
      (j : Fin c.exports.length) (vs : List IVal), TypedCalls c calls →
      ValTy.checkList c.exports[j].ty.params vs = true →
      (sessDivs P c calls j vs = sessDivs P c' (castCalls h.len calls) (Fin.cast h.len j) vs ↔
        refDivs P prof c calls j vs =
          refDivs P prof c' (castCalls h.len calls) (Fin.cast h.len j) vs) := by
    intro h calls j vs ht hvs
    have ht' : TypedCalls c' (castCalls h.len calls) := typedCalls_cast h.ty ht
    have hvs' : ValTy.checkList c'.exports[Fin.cast h.len j].ty.params vs = true := by
      rw [h.ty j]
      exact hvs
    rw [sessDivs_eq_refDivs P prof c hc calls j vs ht hvs,
      sessDivs_eq_refDivs P prof c' hc' _ _ vs ht' hvs']
  constructor
  · intro h
    exact ⟨h.toRefSessEquiv, fun calls j vs ht hvs =>
      (key h.toRefSessEquiv calls j vs ht hvs).mp (h.div calls j vs ht hvs)⟩
  · rintro ⟨h, hd⟩
    exact ⟨h, fun calls j vs ht hvs => (key h calls j vs ht hvs).mpr (hd calls j vs ht hvs)⟩

end Silmaril.Proofs.Wasm.Component.Reference.SessionDiv
