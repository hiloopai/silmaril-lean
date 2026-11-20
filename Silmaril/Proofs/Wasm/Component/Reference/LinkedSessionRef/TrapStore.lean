module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkCallPhaseK

/-!
# Linked calls: the core store of a trap

`Linked2.sound` reads a trapped linked call only through its outcome (`TrapsFrom`,
`TrapsNextD`): a live run reaches a configuration whose only step is a trap. A resumable
session (`resumeCfg`, `SessionAdequacy.Defs`) resumes from the **core store** of the trapped
configuration, so the trapping runs are restated here with that store (`TrapsAt M c`: the
trapped configuration holds the core store `c`):

* `lrun_lift_trapAt`: a failing lift of flat results traps after one step that keeps the store;
* `lift_body_atT`, `nest_atT`: `lift_body_at`, `nest_at` (same proofs), the trap of a failing
  lift of the exporter's results at the core store the exporter returned with;
* `traps_startLT`, `lift_body_trapT`, `nest_trap_argsT`: a callout of the importer whose
  arguments do not lift traps at the core store of the callout;
* `call_atLKT`: `call_atLK` (same proof), the trap of a failing lift of the importer's results at
  the core store the importer returned with.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## Traps at a core store -/

/-- From `M`, a live run reaches a configuration whose only step is a trap, holding the core
store `c`. -/
def TrapsAt (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (M : Machine.Config (E3 P) σ) (c : (E3 P).Store (CanonHost (E3 P))) : Prop :=
  ∃ tr mT r, LRun prof (fun _ _ => false) (DI P impl) M tr mT ∧ Live mT ∧
    UniqueStep prof (fun _ _ => false) (DI P impl) mT (.trap r) (trapCfg mT) ∧
    mT.core = c

theorem TrapsAt.lrun {M M' : Machine.Config (E3 P) σ} {tr : List (Label (E3 P) σ)}
    {c : (E3 P).Store (CanonHost (E3 P))}
    (h : LRun prof (fun _ _ => false) (DI P impl) M tr M') (h' : TrapsAt prof P impl M' c) :
    TrapsAt prof P impl M c := by
  obtain ⟨tr', mT, r, h₁, hl, hu, hc⟩ := h'
  exact ⟨_, mT, r, h.trans h₁, hl, hu, hc⟩

/-- **A run from a configuration that traps at `c`**, ending where a call outcome holds, ends
in the trap, at the core store `c`. -/
theorem TrapsAt.out {M m' : Machine.Config (E3 P) σ} {tr : List (Label (E3 P) σ)}
    {c : (E3 P).Store (CanonHost (E3 P))} {out : CallOutcome} {cid : CallId}
    (hT : TrapsAt prof P impl M c) (r : Steps prof (fun _ _ => false) (DI P impl) M tr m')
    (ho : out.Holds (fun _ _ => false) cid m') : out = .trap ∧ m'.core = c := by
  obtain ⟨tr₁, mT, rT, hrun, hlive, hu, hc⟩ := hT
  rcases hrun.inv r with hl' | ⟨tr'', -, r''⟩
  · exact absurd ho (hl'.not_holds _ _)
  cases r'' with
  | refl => exact absurd ho (hlive.not_holds _ _)
  | cons s' r''' =>
    obtain ⟨rfl, rfl⟩ := hu.2 _ _ s'
    have e := steps_of_locked rfl rfl r'''
    subst e
    exact ⟨holds_trapCfgD ho, hc⟩

/-- `lrun_lift_trapP`, keeping the store. -/
theorem lrun_lift_trapAt {α : Type} {th : Option ThreadId} (p : Silmaril.Wasm.Component.FuncTy)
    (hres : p.results.length ≤ 1) (hmaxr : (ValTy.flatList p.results).length ≤ 1)
    (hff : floatFreeList p.results = true) {ys : List Flat}
    (hys : ys.map (·.type) = ValTy.flatList p.results) (hnone : liftArgs p.results ys = none)
    {cx : LiftLowerContext (E3 P)}
    {f : List Silmaril.Wasm.Component.Reference.Val × FlatCursor → Canon.P (E3 P) σ α}
    {g : α → Canon.P (E3 P) σ (Ret (E3 P))} {M : Machine.Config (E3 P) σ}
    {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)}
    (hc : M.ctl = ⟨th, .prog ((liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList ys) (resultTypes (witFt p)) >>= f) >>= g), segs⟩ :: rest)
    (hl : M.store.lockdown = false) : TrapsAt prof P impl M M.core := by
  have e : liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList ys)
      (resultTypes (witFt p)) =
        (ptrType cx >>= fun q => liftFlatTypes Limits.spec Quirks.none cx q
        (toClosedList p.results) ⟨ys, 0⟩ : Canon.P (E3 P) σ _) := by
    rw [resultTypes_witFt p hres, show FlatCursor.ofList ys = ⟨ys, 0⟩ from rfl,
      liftFlatValues_toClosed (max := ABI.maxFlatResults) Limits.spec Quirks.none cx hmaxr]
  have hT := liftFlatTypes_liftArgs (σ := σ) (E := E3 P) Limits.spec Quirks.none cx
    (ptrTypeIn (CoreEngine.view _ M.core) cx) hff hys
  rw [hnone] at hT
  obtain ⟨r, k₀, hk⟩ := hT
  have hc' : M.ctl = ⟨th, .prog (.op (S := Eff (E3 P) σ) .readCore fun s =>
      (liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn s cx) (toClosedList p.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest := by
    rw [hc, e]
    rfl
  have s₁ : Step prof (fun _ _ => false) (DI P impl) M .tau { M with ctl := ⟨th, .prog
      ((liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn (CoreEngine.view _ M.core) cx) (toClosedList p.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest } := Step.readCore hc'
  rw [hk] at s₁
  exact ⟨_, _, r, .cons ⟨by rw [hc]; exact List.cons_ne_nil _ _, hl⟩
    (.of_prog hc (fun _ _ e => by cases e) s₁) (.refl _), ⟨List.cons_ne_nil _ _, hl⟩,
    .of_prog rfl (fun _ _ e => by cases e) (.trap rfl), rfl⟩

/-! ## A nested call whose results do not lift -/

theorem lift_body_atT (M₀ : Machine.Config (E3 P) σ) (S : CStore (E3 P)) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) (ws : List Silmaril.Wasm.Component.Val) {ιe ιe' : InstState}
    (a : (E3 P).FuncAddr) (R : List (Activation (E3 P) σ))
    (hie : S.insts[1]? = some ιe) (hadd : ιe.addThread? ⟨S.threads.length⟩ = some (1, ιe'))
    (hrem : ιe'.removeThread? 1 = some (⟨S.threads.length⟩, InstState.removeThread 1 ιe'))
    (hl : S.lockdown = false)
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws)
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hmaxr : (ValTy.flatList p.results).length ≤ 1) :
    ∃ pos K' segs' tr, LRun prof (fun _ _ => false) (DI P impl)
      { M₀ with
        store := nstore S { inst := ⟨2⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p 0) (ntask₀ S p)
          (thread₁ S.tasks) S.insts
        ctl := ⟨some ⟨S.threads.length⟩,
          .prog (DI P impl (.threadBody (.liftImplicit ⟨S.tasks.length⟩ a))), []⟩ :: R } tr
      { M₀ with
        store := nstoreCore S ys p ιe' pos
        ctl := ⟨some ⟨S.threads.length⟩,
          .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) K',
          segs'⟩ :: R } ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat) (us : List Silmaril.Wasm.Component.Val),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = some us →
        ∃ tr', LRun prof (fun _ _ => false) (DI P impl)
          (retCfg { M₀ with store := nstoreCore S ys p ιe' pos } (some ⟨S.threads.length⟩) K'
            segs' R y zs) tr'
          { M₀ with store := nstoreRet S y.1 ys p ιe' pos us, core := y.1, ctl := R }) ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = none →
        TrapsAt prof P impl
          (retCfg { M₀ with store := nstoreCore S ys p ιe' pos } (some ⟨S.threads.length⟩) K'
            segs' R y zs) y.1) := by
  obtain ⟨pos, trS, hst⟩ := runs_startL (impl := impl) (th := some ⟨S.threads.length⟩)
    (m := { M₀ with
      store := nstore S { inst := ⟨2⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p 0) (ntask₁ S p)
        ((thread₁ S.tasks).withIndex 1) (S.insts.set 1 ιe') })
    (Gt := S.tasks) rfl rfl (callers_get_last rfl) (subtasks_get_last rfl) rfl hpf hys hmaxp hws
  have hlen : 1 < S.insts.length := (List.getElem?_eq_some_iff.mp hie).1
  have hie' : (S.insts.set 1 ιe')[1]? = some ιe' := List.getElem?_set_self hlen
  refine ⟨pos, ?_⟩
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨?_, ?_, ?_⟩
  · apply RunsQ.chunk rfl (runs_enterG (impl := impl) (Gt := S.tasks) rfl rfl (by exact hie) hadd)
      (by exact hl)
    apply LRun.store_congr (nstore_enter S _ _ p hie hadd)
    apply RunsQ.chunk rfl (runs_getObj ArenaField.tasks _ _ (tasks_get_last rfl)) (by exact hl)
    apply RunsQ.chunk rfl (hst.withCtl _) (by exact hl)
    apply RunsQ.chunk rfl (runs_lowerP p ws _ hpf (Silmaril.Wasm.Component.checkList_of_liftArgs hws)
      hmaxp _) (by exact hl)
    lstep hl
    exact .refl _
  · intro y zs us hzs hus
    apply Exists.intro
    unfold retCfg
    apply LRun.store_congr (S' := nstore S { inst := ⟨2⟩, state := .started }
      (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p pos) ((ntask₁ S p).withState .started)
      ((thread₁ S.tasks).withIndex 1) (S.insts.set 1 ιe')) (by rw [nstoreCore_eq])
    apply RunsQ.chunk2 rfl (runs_lift_someP (impl := impl) p hres hmaxr hrf hzs hus _ _).choose_spec
      (by exact hl)
    apply RunsQ.chunk2 rfl (by exact (runs_returnL (impl := impl) (Gt := S.tasks) rfl rfl rfl rfl
        (callers_get_last rfl) (subtasks_get_last rfl) rfl hres hrf
        (Silmaril.Wasm.Component.checkList_of_liftArgs hus) hmaxr).choose_spec) (by exact hl)
    apply LRun.store_congr (nstore_return S y.1 ys p ιe' pos _)
    apply RunsQ.chunk rfl (runs_exitG (impl := impl) (Gt := S.tasks) (Gth := S.threads) rfl rfl rfl
      rfl rfl rfl (by exact hie') hrem) (by exact hl)
    lstep ((CStore.unregisterThreadSt_frame (E := E3 P) _ _ _ _).2.2.2.2.2.2.1.trans hl)
    exact lrun_refl_store (nstore_exit S y.1 _ _ p ιe')
  · intro y zs hzs hn
    exact lrun_lift_trapAt p hres hmaxr hrf hzs hn rfl (by exact hl)

theorem nest_atT (B : Machine.Config (E3 P) σ) (ιe ιe' : InstState) (N : List (NRec P))
    (C : List (Option (Activation (E3 P) σ))) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (x : CoreSt (E3 P)) (f : FuncId) (a : (E3 P).FuncAddr)
    (p : Silmaril.Wasm.Component.FuncTy) (ys : List Flat) (ιi : InstState)
    (ws : List Silmaril.Wasm.Component.Val)
    (hs : (E3 P).status x.1 x.2 = .callout (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hentry : calloutEntry (extN B ιe N C).store th (.lowered f (witFt p) {} ⟨2⟩) = none)
    (hi : ArenaField.insts.get? (extN B ιe N C).store ⟨2⟩ = some ιi) (hleave : ιi.mayLeave = true)
    (hf : ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩))
    (hlen : 1 < B.store.insts.length)
    (hadd : ιe.addThread? ⟨(extN B ιe N C).store.threads.length⟩ = some (1, ιe'))
    (hrem : ιe'.removeThread? 1 =
      some (⟨(extN B ιe N C).store.threads.length⟩, InstState.removeThread 1 ιe'))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws)
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hmaxr : (ValTy.flatList p.results).length ≤ 1) :
    ∃ (pos : Nat) (C₁ : List (Option (Activation (E3 P) σ))) (M₁ : Machine.Config (E3 P) σ)
      (th' : Option ThreadId) (K' : List Flat → Canon.P (E3 P) σ (Ret (E3 P)))
      (segs' : List (Seg (E3 P) σ)) (rest' : List (Activation (E3 P) σ)) (tr : List (Label (E3 P) σ)),
      LRun prof (fun _ _ => false) (DI P impl) (coreCfg (extN B ιe N C) th K segs rest x) tr M₁ ∧
      M₁.ctl = ⟨th', .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws))
        K', segs'⟩ :: rest' ∧
      M₁.core = x.1 ∧ M₁.store.lockdown = false ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat) (us : List Silmaril.Wasm.Component.Val),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = some us →
        ∃ tr', LRun prof (fun _ _ => false) (DI P impl) (retCfg M₁ th' K' segs' rest' y zs) tr'
          (coreCfg (extN B (InstState.removeThread 1 ιe')
            (N ++ [nrec (extN B ιe N C).store ys p pos (lowerArgs p.results us)])
            C₁) th K segs rest (y.1, (E3 P).resume y.1 x.2 (.values (lowerArgs p.results us))))) ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = none →
        TrapsAt prof P impl (retCfg M₁ th' K' segs' rest' y zs) y.1) := by
  obtain ⟨C₁, R, tr₁, h₁, hback⟩ := nest_pre (prof := prof) (impl := impl) B ιe ιe' N C th K segs
    rest x f a p ys ιi hs hentry hi hleave hf
  have hie : ((extN B ιe N C).store : CStore (E3 P)).insts[1]? = some ιe :=
    List.getElem?_set_self hlen
  obtain ⟨pos, K', segs', tr₂, h₂, hret, htrap⟩ := lift_body_atT (prof := prof) (impl := impl)
    { coreCfg (extN B ιe N C) th K segs rest x with conts := C₁ }
    (extN B ιe N C).store ys p ws a R hie hadd hrem rfl hpf hys hmaxp hws
    hres hrf hmaxr
  refine ⟨pos, C₁, _, _, K', segs', _, _, h₁.trans h₂, rfl, rfl, rfl, ?_, htrap⟩
  intro y zs us hzs hus
  obtain ⟨tr₃, h₃⟩ := hret y zs us hzs hus
  obtain ⟨tr₄, h₄⟩ := hback y.1 pos us
  exact ⟨_, h₃.trans h₄⟩

/-! ## A callout whose arguments do not lift -/

/-- A big-step run to a trap in focus, at the store it reaches. -/
theorem TrapsQ.trapsAt {α : Type} {th : Option ThreadId} {p : Canon.P (E3 P) σ α}
    {f : α → Canon.P (E3 P) σ (Ret (E3 P))} {M mT : Machine.Config (E3 P) σ}
    {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)} {tr : List (Label (E3 P) σ)}
    (hc : M.ctl = ⟨th, .prog (p >>= f), segs⟩ :: rest) (h : TrapsQ (DI P impl) th p M tr mT)
    (hl : M.store.lockdown = false) {c : (E3 P).Store (CanonHost (E3 P))}
    (hcore : mT.core = c) : TrapsAt prof P impl M c := by
  have e : M = { M with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } := by
    cases M
    cases hc
    rfl
  obtain ⟨q, segs', r, hrun, hlive, hu⟩ := h.lrun (prof := prof) (hr := fun _ _ => false) hl f
    segs rest
  rw [← e] at hrun
  exact ⟨_, _, r, hrun, hlive, hu, hcore⟩

/-- `traps_startL`, at the store it reaches: the core store is unchanged. -/
theorem traps_startLT {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {c : CallerId} {S : SubtaskId}
    {cx : LiftLowerContext (E3 P)} {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy}
    {xS : Subtask}
    (ht : m.store.tasks = Gt ++ [y]) (hy : y.caller = c)
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys 0 (witFt p) 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (hff : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmax : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    ∃ tr mT, TrapsQ (DI P impl) th (Task.start ⟨Gt.length⟩) m tr mT ∧
      mT.core = m.core := by
  obtain ⟨tr, h⟩ := traps_lowerOnStart (impl := impl) (th := th)
    (m := { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store }) (by exact hc)
    (by exact hS) hidx hff hys hmax hws
  have hon : TrapsQ (DI P impl) th (DI P impl (.onStart c))
      { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store } (.tau :: tr)
      { m with store := LowerSt.startSt S (CStore.setTaskState ⟨Gt.length⟩ .started m.store) } :=
    TrapsQ.bind (RunsQ.getObj _ _ (by exact hc)) (TrapsQ.left h)
  have hs : TrapsQ (DI P impl) th (callVals (.onStart y.caller) :
      Canon.P (E3 P) σ (List Silmaril.Wasm.Component.Reference.Val))
      { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store } (.tau :: .tau :: tr)
      { m with store := LowerSt.startSt S (CStore.setTaskState ⟨Gt.length⟩ .started m.store) } := by
    rw [hy]
    exact TrapsQ.callIn hon
  unfold Task.start
  exact ⟨_, _, TrapsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
    (TrapsQ.bind (runs_modifyStore _ _ rfl) hs), rfl⟩

/-- `lift_body_trap`, at the core store of `S`. -/
theorem lift_body_trapT (M₀ : Machine.Config (E3 P) σ) (S : CStore (E3 P)) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) {ιe ιe' : InstState}
    (a : (E3 P).FuncAddr) (R : List (Activation (E3 P) σ))
    (hie : S.insts[1]? = some ιe) (hadd : ιe.addThread? ⟨S.threads.length⟩ = some (1, ιe'))
    (hl : S.lockdown = false)
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    TrapsAt prof P impl
      { M₀ with
        store := nstore S { inst := ⟨2⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p 0) (ntask₀ S p)
          (thread₁ S.tasks) S.insts
        ctl := ⟨some ⟨S.threads.length⟩,
          .prog (DI P impl (.threadBody (.liftImplicit ⟨S.tasks.length⟩ a))), []⟩ :: R }
      M₀.core := by
  obtain ⟨trS, mT, hst, hcore⟩ := traps_startLT (impl := impl) (th := some ⟨S.threads.length⟩)
    (m := { M₀ with
      store := nstore S { inst := ⟨2⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p 0) (ntask₁ S p)
        ((thread₁ S.tasks).withIndex 1) (S.insts.set 1 ιe') })
    (Gt := S.tasks) rfl rfl (callers_get_last rfl) (subtasks_get_last rfl) rfl hpf hys hmaxp hws
  have h₁ := RunsQ.lrun_at (prof := prof) (hr := fun _ _ => false)
    (runs_enterG (impl := impl) (Gt := S.tasks) (t := ⟨S.threads.length⟩)
      (m := { M₀ with
        store := nstore S { inst := ⟨2⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p 0) (ntask₀ S p)
          (thread₁ S.tasks) S.insts
        ctl := ⟨some ⟨S.threads.length⟩,
          .prog (DI P impl (.threadBody (.liftImplicit ⟨S.tasks.length⟩ a))), []⟩ :: R })
      rfl rfl (by exact hie) hadd) (by exact hl) _ rfl
  refine TrapsAt.lrun h₁ ?_
  rw [nstore_enter S _ _ p hie hadd]
  refine TrapsAt.lrun (RunsQ.lrun_at (runs_getObj ArenaField.tasks _ _ (tasks_get_last rfl))
    (by exact hl) _ rfl) ?_
  exact TrapsQ.trapsAt rfl (hst.withCtl _) (by exact hl) hcore

/-- **A callout of the importer whose arguments do not lift traps at the core store of the
callout.** -/
theorem nest_trap_argsT (B : Machine.Config (E3 P) σ) (ιe ιe' : InstState) (N : List (NRec P))
    (C : List (Option (Activation (E3 P) σ))) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (x : CoreSt (E3 P)) (f : FuncId) (a : (E3 P).FuncAddr)
    (p : Silmaril.Wasm.Component.FuncTy) (ys : List Flat) (ιi : InstState)
    (hs : (E3 P).status x.1 x.2 = .callout (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hentry : calloutEntry (extN B ιe N C).store th (.lowered f (witFt p) {} ⟨2⟩) = none)
    (hi : ArenaField.insts.get? (extN B ιe N C).store ⟨2⟩ = some ιi) (hleave : ιi.mayLeave = true)
    (hf : ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩))
    (hlen : 1 < B.store.insts.length)
    (hadd : ιe.addThread? ⟨(extN B ιe N C).store.threads.length⟩ = some (1, ιe'))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    TrapsAt prof P impl (coreCfg (extN B ιe N C) th K segs rest x) x.1 := by
  obtain ⟨C₁, R, tr₁, h₁, -⟩ := nest_pre (prof := prof) (impl := impl) B ιe ιe' N C th K segs
    rest x f a p ys ιi hs hentry hi hleave hf
  have hie : ((extN B ιe N C).store : CStore (E3 P)).insts[1]? = some ιe :=
    List.getElem?_set_self hlen
  exact TrapsAt.lrun h₁ (lift_body_trapT (prof := prof) (impl := impl)
    { coreCfg (extN B ιe N C) th K segs rest x with conts := C₁ }
    (extN B ιe N C).store ys p a R hie hadd rfl hpf hys hmaxp hws)

/-! ## The importer's call -/

/-- `CallAtLK`, with the trap of a failing lift of the importer's results at the core store the
importer returned with. -/
structure CallAtLKT (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi' : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) (h₀ : σ) (k j : Nat)
    (x : SimpleExport) (a : Nat) (vs : List Silmaril.Wasm.Component.Val)
    (M₀ : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) : Prop where
  start : M₀ = coreCfg (extN M₀ ιe [] M₀.conts) th K segs rest
    (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs x.ty.params vs))
  funcs : M₀.store.funcs = fs
  frame : LFrame M₀ th
  ret : ∀ (ιe' : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
    (y : CoreSt (E3 P)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    ∃ C', ResolvesAtL prof P impl (retCfg (extN M₀ ιe' N C) th K segs rest y ys)
      (readyCfgL y.1 ιe' (InstState.removeThread 1 ιi') fs
        (nextGarbL G x k j (vs.map toRefVal) (ws.map toRefVal) N C') (ST ++ N.map (·.sub)) h₀)
  trap : ∀ (ιe' : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
    (y : CoreSt (E3 P)) (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsAt prof P impl (retCfg (extN M₀ ιe' N C) th K segs rest y ys) y.1

/-- `call_atLK` (same proof), with `CallAtLKT`. -/
theorem call_atLKT (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (ιe ιi : InstState) (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask)
    (h₀ : σ) (k j a : Nat) (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val)
    (hff : floatFreeList x.ty.params = true)
    (hck : ValTy.checkList x.ty.params vs = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true) (hth : ThreadsOk ιi) (hleave : ιi.mayLeave = true)
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨2⟩)) :
    ∃ M₀ th K segs rest tr₁, LRun prof (fun _ _ => false) (DI P impl)
      (invokedAtL cs ιe ιi fs G ST h₀ k j (vs.map toRefVal)) tr₁ M₀ ∧
      CallAtLKT prof P impl cs ιe (enterInst ιi ⟨G.threads.length⟩) fs G ST h₀ k j x a vs M₀ th
        K segs rest := by
  have hadd : ιi.addThread? ⟨G.threads.length⟩ = some (1, enterInst ιi ⟨G.threads.length⟩) :=
    addThread?_ok hth _
  have hrem : (enterInst ιi ⟨G.threads.length⟩).removeThread? 1 = some (⟨G.threads.length⟩,
      InstState.removeThread 1 (enterInst ιi ⟨G.threads.length⟩)) :=
    removeThread?_enter ιi _
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  · show LRun prof (fun _ _ => false) (DI P impl)
      (invokedAtL cs ιe ιi fs G ST h₀ k j (vs.map toRefVal)) _ _
    unfold invokedAtL
    apply RunsQ.chunk rfl
      (runs_allocObj ArenaField.callers (.host ⟨k⟩ (vs.map toRefVal) 0) _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.modify (f := enterHostSt) rfl (.pure _ _)) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl (.call rfl)
    have hget : ∀ s : CStore (E3 P), s.funcs = fs →
        ArenaField.funcs.get? s (⟨j⟩ : FuncId) = some (.lifted a (liftedFt x) {} ⟨2⟩) := by
      intro s e
      simp only [ArenaField.get?, ArenaField.funcs, e, Arena.get?_eq_getElem?]
      exact hf
    apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (hget _ rfl)) rfl
    apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) rfl
    show LRun prof (fun _ _ => false) (DI P impl) _ _ _
    apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
    apply RunsQ.chunk2 rfl (RunsQ.get (.pure _ _)) rfl
    apply RunsQ.chunk2 rfl (runs_ite_false (by exact threadIs_last rfl) _ _) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl
      (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
    have e₁ : ∀ S : CStore (E3 P), S.threads = G.threads ++ [{ task := ⟨G.tasks.length⟩ }] →
        threadStatusSt ⟨G.threads.length⟩ .running S =
          { S with threads := G.threads ++ [thread₁ G.tasks] } :=
      fun S h => threadStatus_last h _
    apply LRun.store_congr (S' := storeK₁ cs ιe ιi fs G ST x k (vs.map toRefVal))
      ((e₁ _ rfl).trans rfl)
    have hS₁ : (storeK₁ cs ιe ιi fs G ST x k (vs.map toRefVal)).insts = [{}, ιe, ιi] := rfl
    apply RunsQ.chunk (th := some ⟨G.threads.length⟩)
      (p := Task.enterImplicitThread Quirks.none ⟨G.tasks.length⟩) (a := true) rfl
      (runs_enter3 (Gt := G.tasks) (y := taskK₀ x G.callers) rfl rfl rfl hS₁ hadd) rfl
    have e₂ : CStore.registerThreadSt ⟨G.tasks.length⟩ ⟨G.threads.length⟩
        (CStore.setImplicitThread ⟨G.tasks.length⟩ ⟨G.threads.length⟩
          (storeK₁ cs ιe ιi fs G ST x k (vs.map toRefVal))) =
        storeK₂ cs ιe ιi (enterInst ιi ⟨G.threads.length⟩) fs G ST x k (vs.map toRefVal) :=
      enter_eq3 rfl rfl rfl hadd rfl
    apply LRun.store_congr (by exact e₂)
    have hS₂ : (storeK₂ cs ιe ιi (enterInst ιi ⟨G.threads.length⟩) fs G ST x k
        (vs.map toRefVal)).tasks = G.tasks ++ [taskK₁ x G.callers ⟨G.threads.length⟩] := rfl
    apply RunsQ.chunk rfl (runs_getObj ArenaField.tasks _ _ (tasks_get_last hS₂)) rfl
    apply RunsQ.chunk rfl (runs_start (Gt := G.tasks) (Gc := G.callers) hS₂ rfl rfl) rfl
    have hlow : ∀ (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) σ),
        RunsQ (DI P impl) (some ⟨G.threads.length⟩) (lowerFlatValues Limits.spec Quirks.none cx
          ABI.maxFlatParams (vs.map toRefVal) (paramTypes (liftedFt x)) none) m [.tau]
          (lowerArgs x.ty.params vs) m :=
      fun cx m => runs_lowerP x.ty vs cx hff hck hmax m
    apply RunsQ.chunk rfl (hlow _ _) rfl
    apply LRun.store_congr
      (S' := storeK₃ cs ιe ιi (enterInst ιi ⟨G.threads.length⟩) fs G ST x k (vs.map toRefVal))
      (setTaskState_last (Gt := G.tasks) rfl _)
    mstep
    exact .refl _
  apply CallAtLKT.mk
  · exact start_of rfl rfl rfl rfl
  · rfl
  · refine ⟨fun f ft ιe' N C => ?_, ⟨_, rfl, hleave⟩⟩
    exact calloutEntry_mid (Gt := G.tasks) (Gth := G.threads) rfl rfl rfl rfl f ft {}
  · show ∀ (ιe' : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
      (y : CoreSt (E3 P)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val), _ → _ →
      ∃ C', ResolvesAtL prof P impl (retCfg (extN _ ιe' N C) _ _ _ _ y ys) _
    intro ιe' N C y ys ws hys hws
    have hlift : ∀ (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) σ), ∃ c,
        RunsQ (DI P impl) (some ⟨G.threads.length⟩) (liftFlatValues Limits.spec Quirks.none cx
          ABI.maxFlatResults (.ofList ys) (resultTypes (witFt x.ty))) m [.tau]
          (ws.map toRefVal, c) m :=
      runs_lift_someP x.ty hres hmaxr hffr hys hws
    apply Exists.intro; apply Exists.intro; apply Exists.intro
    apply And.intro
    · show LRun prof (fun _ _ => false) (DI P impl) (retCfg _ _ _ _ _ y ys) _ _
      unfold retCfg
      apply RunsQ.chunk2 rfl (hlift _ _).choose_spec rfl
      apply RunsQ.chunk2 rfl (runs_returnM (Gt := G.tasks) (R := N.map (·.task))
        (Gc := G.callers) (CL := N.map (·.caller)) _ rfl rfl rfl rfl rfl) rfl
      apply LRun.store_congr (setTaskState_mid (Gt := G.tasks) rfl _)
      apply RunsQ.chunk rfl (runs_exitM (Gt := G.tasks) (R := N.map (·.task))
        (Gth := G.threads) (R' := N.map (·.thread)) rfl rfl rfl rfl rfl rfl rfl hrem) rfl
      apply LRun.store_congr (unregisterThreadSt_mid _ _ rfl rfl rfl)
      show LRun prof (fun _ _ => false) (DI P impl) _ _ _
      mstep
      apply LRun.store_congr (threadStatus_mid (Gth := G.threads) rfl _)
      apply RunsQ.chunk rfl (runs_callUnit_loopM (Gt := G.tasks) (R := N.map (·.task)) rfl rfl)
        rfl
      mstep
      mstep
      mstep
      exact .refl _
    · rw [hostFinish_cancel _ G.pending ⟨k⟩ ⟨j⟩ (vs.map toRefVal) _ rfl]
      rfl
  · intro ιe' N C y ys hys hn
    exact lrun_lift_trapAt x.ty hres hmaxr hffr hys hn rfl rfl

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
