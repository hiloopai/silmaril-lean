module

public import Silmaril.Proofs.Wasm.Component.Reference.CallPhaseKI
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# A `canon lower` callout answered by another component's `canon lift`

In the reference machine of `Linked2.toRef`, a callout of the importer's core activation to the
trampoline `.lowered f (witFt p) {} ⟨2⟩` of import `k` runs `canonLower`, whose
`callCancel (.funcInst f c)` dispatches `funcInstProg`: `f` is the exporter's lifted function
`.lifted a (witFt p) {} ⟨1⟩`, so `canonLift` runs the exporter's core function `a` in a fresh
task and thread of instance `1` (`Thread.resume`), nested above the importer's parked callout.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## Records of nested calls -/

/-- The records one nested call leaves: the subtask and the `canon_lower` caller record of the
importer's callout, the task and the thread of the exporter's `canon lift`. -/
structure NRec (P : Profile) where
  /-- The subtask. -/
  sub : Subtask
  /-- The caller record. -/
  caller : Caller (E3 P)
  /-- The task. -/
  task : Runtime.Task (E3 P)
  /-- The thread. -/
  thread : Runtime.Thread

/-- The frame `B` with the exporter's instance state `ιe` (instance `1`), the records `N` of
nested calls appended, the saved-continuation slots `C`, and the store not locked down. -/
def extN (B : Machine.Config (E3 P) σ) (ιe : InstState) (N : List (NRec P))
    (C : List (Option (Activation (E3 P) σ))) : Machine.Config (E3 P) σ :=
  { B with
    conts := C
    store := { B.store with
      insts := B.store.insts.set 1 ιe
      subtasks := B.store.subtasks ++ N.map (·.sub)
      callers := B.store.callers ++ N.map (·.caller)
      tasks := B.store.tasks ++ N.map (·.task)
      threads := B.store.threads ++ N.map (·.thread)
      lockdown := false } }


/-! ## The callout step and the entry check -/

/-- The callout step of the machine, under `DI P impl`. -/
theorem callout_stepD {M : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {ct : (E3 P).Thread (CanonHost (E3 P))} {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))}
    {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)}
    {h : CanonHost (E3 P)} {ys : List Flat}
    (hc : M.ctl = ⟨th, .core ct K, segs⟩ :: rest) (hs : (E3 P).status M.store.core ct = .callout h ys) :
    UniqueStep prof (fun _ _ => false) (DI P impl) M .tau
      { M with ctl := ⟨th, .prog (DI P impl (.hostCallout h ys)), .core ct K :: segs⟩ :: rest } :=
  .of_core hc (callout_status_ne hs) (.coreCallout hc hs)

/-- The prefix of the callout program of a `canon lower` trampoline: the entry check passes. -/
theorem lrun_hostCallout {m M : Machine.Config (E3 P) σ} {th : Option ThreadId} {f : FuncId}
    {ft : WIT.FuncType Empty RtId} {inst : InstId} {ys : List Flat}
    {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)} {tr : List (Label (E3 P) σ)}
    (hl : m.store.lockdown = false)
    (hentry : calloutEntry m.store th (.lowered f ft {} inst) = none)
    (r : LRun prof (fun _ _ => false) (DI P impl)
      { m with ctl := ⟨th, .prog (canonLower Limits.spec Quirks.none f ft {} inst ys >>=
        fun fl => pure (Ret.flat fl)), segs⟩ :: rest } tr M) :
    LRun prof (fun _ _ => false) (DI P impl)
      { m with ctl := ⟨th, .prog (DI P impl (.hostCallout (.lowered f ft {} inst) ys)), segs⟩ ::
        rest } (.tau :: .tau :: tr) M := by
  refine LRun.prog rfl (fun _ _ e => by cases e) hl (Step.currentThread rfl) ?_
  refine LRun.prog rfl (fun _ _ e => by cases e) hl (Step.get rfl) ?_
  show LRun _ _ _ { m with ctl := ⟨th, .prog (match calloutEntry m.store th (.lowered f ft {} inst)
    with | some r => trap r | none => _), segs⟩ :: rest } _ _
  rw [hentry]
  exact r


/-- Big-step runs do not read or write the control chain. -/
theorem RunsQ.withCtl {d : Call (E3 P) → Canon.P (E3 P) σ (Ret (E3 P))} {α : Type}
    {th : Option ThreadId} {p : Canon.P (E3 P) σ α} {m m' : Machine.Config (E3 P) σ}
    {tr : List (Label (E3 P) σ)} {a : α} (h : RunsQ d th p m tr a m')
    (c : List (Activation (E3 P) σ)) :
    RunsQ d th p { m with ctl := c } tr a { m' with ctl := c } := by
  induction h with
  | pure => exact .pure _ _
  | get _ ih => exact .get ih
  | modify hf _ ih => exact .modify hf ih
  | hostGet _ ih => exact .hostGet ih
  | hostSet _ ih => exact .hostSet ih
  | currentThread _ ih => exact .currentThread ih
  | emit _ ih =>
    refine .emit ?_
    rename_i o _ _ _ _ _ _
    cases o <;> exact ih
  | newThread ha hs _ ih => exact .newThread ha hs ih
  | call _ _ ih₁ ih₂ => exact .call ih₁ ih₂

/-- The program in focus is a choice. -/
def isChoose {α : Type} : Canon.P (E3 P) σ α → Bool
  | .op (.choose _) _ => true
  | _ => false

theorem notChoose_of {α : Type} {p : Canon.P (E3 P) σ α} (h : isChoose p = false) :
    NotChoose p := by
  intro ck k e
  subst e
  cases h

/-- One step of a non-choice program in focus whose store is not locked down by `h`. -/
macro "lstep " h:term : tactic => `(tactic| apply LRun.prog rfl (notChoose_of rfl)
  (by exact $h)
  (by first
    | exact Step.get rfl | exact Step.modify rfl | exact Step.call rfl | exact Step.popProg rfl
    | exact Step.currentThread rfl | exact Step.hostGet rfl | exact Step.hostSet rfl
    | exact Step.emit rfl | exact Step.popCore rfl
    | exact Step.resumeThread rfl rfl | exact Step.newThread rfl rfl | exact Step.threadExit rfl
    | exact Step.hostDone rfl | exact Step.callCore rfl))

/-! ## The stores of a nested call -/

/-- The store `S` with one more subtask, caller record, task and thread, and the instance states
`is`. -/
def nstore (S : CStore (E3 P)) (sub : Subtask) (cl : Caller (E3 P)) (tk : Runtime.Task (E3 P))
    (thr : Runtime.Thread) (is : List InstState) : CStore (E3 P) :=
  { S with
    subtasks := S.subtasks ++ [sub]
    callers := S.callers ++ [cl]
    tasks := S.tasks ++ [tk]
    threads := S.threads ++ [thr]
    insts := is }

/-- The exporter's task of a nested call from store `S` at type `p`, as allocated. -/
def ntask₀ (S : CStore (E3 P)) (p : Silmaril.Wasm.Component.FuncTy) : Runtime.Task (E3 P) :=
  { ft := witFt p, opts := {}, inst := ⟨1⟩, caller := ⟨S.callers.length⟩ }

/-- The exporter's task once its implicit thread is registered. -/
def ntask₁ (S : CStore (E3 P)) (p : Silmaril.Wasm.Component.FuncTy) : Runtime.Task (E3 P) :=
  ({ ntask₀ S p with implicitThread := some ⟨S.threads.length⟩ } : Runtime.Task (E3 P)).addThread
    ⟨S.threads.length⟩

theorem nstore_resume (S : CStore (E3 P)) (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy) :
    threadStatusSt ⟨S.threads.length⟩ .running
        (ArenaField.threads.alloc (ArenaOps.allocSt ArenaField.tasks (ntask₀ S p)
          (allocSC S ⟨2⟩ ys p)) { task := ⟨S.tasks.length⟩ }).1 =
      nstore S { inst := ⟨2⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p 0) (ntask₀ S p)
        (thread₁ S.tasks) S.insts := by
  simp [threadStatusSt, allocSC, ArenaOps.allocSt, ArenaField.alloc, Arena.alloc,
    ArenaField.modify, Arena.modify, ArenaField.threads, ArenaField.tasks, ArenaField.callers,
    ArenaField.subtasks, modify_concat_length, thread₁, nstore]

/-- `enter_implicit_thread` of a synchronous task (last in the task arena) of an instance
`ι` found at any index. -/
theorem runs_enterG {m : Machine.Config (E3 P) σ} {Gt : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} {t : ThreadId} {ι ι' : InstState}
    (htasks : m.store.tasks = Gt ++ [y]) (hasync : y.ft.async_ = false)
    (hi : ArenaField.insts.get? m.store y.inst = some ι) (hadd : ι.addThread? t = some (1, ι')) :
    RunsQ (DI P impl) (some t) (Task.enterImplicitThread Quirks.none ⟨Gt.length⟩) m
      [.tau, .tau, .tau, .tau, .tau, .tau] true
      { m with store := (CStore.registerThreadSt ⟨Gt.length⟩ t
        (CStore.setImplicitThread ⟨Gt.length⟩ t m.store)) } := by
  have h₁ : (CStore.setImplicitThread ⟨Gt.length⟩ t m.store).tasks =
      Gt ++ [{ y with implicitThread := some t }] := tasks_modify_last htasks _
  have hi' : ArenaField.insts.get? (CStore.setImplicitThread ⟨Gt.length⟩ t m.store) y.inst =
      some ι := hi
  unfold Task.enterImplicitThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_currentThreadId m)
  apply RunsQ.bind (runs_modifyStore _ m rfl)
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last h₁))
  apply RunsQ.bind (runs_ite_pure hasync _ true _)
  show RunsQ _ _ (Task.registerThread ⟨Gt.length⟩ t >>= fun _ => pure true) _ _ _ _
  apply RunsQ.bind (f := fun _ => pure true) (a := 1) ?_ (.pure _ _)
  rotate_left
  unfold Task.registerThread
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last h₁))
  apply RunsQ.bind (runs_getObj ArenaField.insts _ _ (by exact hi'))
  rw [hadd]
  exact RunsQ.bind (runs_modifyStore _ _
    (CStore.registerThreadSt_frame (E := E3 P) _ _ _).2.2.2.2.2.2.1) (.pure _ _)
  rfl

theorem nstore_enter (S : CStore (E3 P)) (sub : Subtask) (cl : Caller (E3 P))
    (p : Silmaril.Wasm.Component.FuncTy) {ιe ιe' : InstState} (hi : S.insts[1]? = some ιe)
    (hadd : ιe.addThread? ⟨S.threads.length⟩ = some (1, ιe')) :
    CStore.registerThreadSt ⟨S.tasks.length⟩ ⟨S.threads.length⟩
        (CStore.setImplicitThread ⟨S.tasks.length⟩ ⟨S.threads.length⟩
          (nstore S sub cl (ntask₀ S p) (thread₁ S.tasks) S.insts)) =
      nstore S sub cl (ntask₁ S p) ((thread₁ S.tasks).withIndex 1) (S.insts.set 1 ιe') := by
  have h₁ : (CStore.setImplicitThread ⟨S.tasks.length⟩ ⟨S.threads.length⟩
      (nstore S sub cl (ntask₀ S p) (thread₁ S.tasks) S.insts)).task? ⟨S.tasks.length⟩ =
      some { ntask₀ S p with implicitThread := some ⟨S.threads.length⟩ } :=
    tasks_get_last (tasks_modify_last rfl _)
  have h₂ : (CStore.setImplicitThread ⟨S.tasks.length⟩ ⟨S.threads.length⟩
      (nstore S sub cl (ntask₀ S p) (thread₁ S.tasks) S.insts)).inst? ⟨1⟩ = some ιe := hi
  unfold CStore.registerThreadSt
  rw [h₁]
  dsimp only
  rw [show ({ ntask₀ S p with implicitThread := some ⟨S.threads.length⟩ } : Runtime.Task (E3 P)).inst =
    ⟨1⟩ from rfl, h₂, Option.bind_some, hadd]
  dsimp only
  simp [nstore, CStore.setImplicitThread, ArenaField.modify, ArenaField.set, ArenaField.tasks,
    ArenaField.insts, ArenaField.threads, Arena.modify, Arena.set, modify_concat_length, ntask₁,
    ntask₀, Runtime.Task.addThread, Runtime.Thread.withIndex]

/-- `on_start` dispatched to a `canon_lower` caller record, under `DI P impl`. -/
theorem runs_onStartLowerD {th : Option ThreadId} {m m' : Machine.Config (E3 P) σ} {c : CallerId}
    {x : Caller (E3 P)} {tr : List (Label (E3 P) σ)} {vs : List Val}
    (hc : ArenaField.callers.get? m.store c = some x)
    (hx : ∀ S cx ys pos ft mp mr, x = .lower S cx ys pos ft mp mr →
      RunsQ (DI P impl) th (lowerOnStart Limits.spec Quirks.none c) m tr vs m')
    (hl : ∃ S cx ys pos ft mp mr, x = .lower S cx ys pos ft mp mr) :
    RunsQ (DI P impl) th (DI P impl (.onStart c)) m (.tau :: (tr ++ [])) (.vals vs) m' := by
  obtain ⟨S, cx, ys, pos, ft, mp, mr, rfl⟩ := hl
  exact RunsQ.getObj_bind _ _ hc (RunsQ.bind (hx _ _ _ _ _ _ _ rfl) (RunsQ.pure _ _))

/-- `Task.start` of a task whose caller record is a `canon_lower` record: the flat arguments of
the callout are lifted. -/
theorem runs_startL {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {c : CallerId} {S : SubtaskId}
    {cx : LiftLowerContext (E3 P)} {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy}
    {xS : Subtask} {ws : List Silmaril.Wasm.Component.Val}
    (ht : m.store.tasks = Gt ++ [y]) (hy : y.caller = c)
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys 0 (witFt p) 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (hff : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmax : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws) :
    ∃ pos tr, RunsQ (DI P impl) th (Task.start ⟨Gt.length⟩) m tr (ws.map toRefVal)
      { m with
        store := LowerSt.setCallerPosSt c pos
          (LowerSt.startSt S (CStore.setTaskState ⟨Gt.length⟩ .started m.store)) } := by
  obtain ⟨pos, tr, h⟩ := runs_lowerOnStart (d := DI P impl) (th := th)
    (m := { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store }) (by exact hc)
    (by exact hS) hidx hff hys hmax hws
  refine ⟨pos, ?_⟩
  apply Exists.intro
  unfold Task.start
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  apply RunsQ.bind (runs_modifyStore _ _ rfl)
  rw [hy]
  unfold callVals callRet perform Prog.lift
  exact RunsQ.call (runs_onStartLowerD (by exact hc) (fun _ _ _ _ _ _ _ _ => h)
    ⟨_, _, _, _, _, _, _, rfl⟩) (.pure _ _)

theorem runs_lowerP {th : Option ThreadId} (p : Silmaril.Wasm.Component.FuncTy)
    (vs : List Silmaril.Wasm.Component.Val) (cx : LiftLowerContext (E3 P))
    (hf : floatFreeList p.params = true) (hck : ValTy.checkList p.params vs = true)
    (hmax : (ValTy.flatList p.params).length ≤ 16) (m : Machine.Config (E3 P) σ) :
    RunsQ (DI P impl) th (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
      (vs.map toRefVal) (paramTypes (witFt p)) none) m [.tau] (lowerArgs p.params vs) m := by
  rw [show paramTypes (witFt p) = toClosedList p.params from labels_map_snd _ _,
    lowerFlatValues_toClosed (max := ABI.maxFlatParams) _ _ _ hf hck hmax]
  exact .get (.pure _ _)

theorem subtasks_get_last {s : CStore (E3 P)} {G : List Subtask} {y : Subtask}
    (h : s.subtasks = G ++ [y]) : ArenaField.subtasks.get? s (⟨G.length⟩ : SubtaskId) = some y := by
  show (s.subtasks)[G.length]? = some y
  rw [h, List.getElem?_concat_length]

/-- A trap after one live step, under `DI P impl`. -/
def TrapsNextD (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (mS : Machine.Config (E3 P) σ) : Prop :=
  ∃ mT r, LRun prof (fun _ _ => false) (DI P impl) mS [.tau] mT ∧ Live mT ∧
    UniqueStep prof (fun _ _ => false) (DI P impl) mT (.trap r) (trapCfg mT)

theorem resultTypes_witFt (p : Silmaril.Wasm.Component.FuncTy) (h : p.results.length ≤ 1) :
    resultTypes (witFt p) = toClosedList p.results := result_witFt p h

theorem lrun_lift_trapP {α : Type} {th : Option ThreadId} (p : Silmaril.Wasm.Component.FuncTy)
    (hres : p.results.length ≤ 1) (hmaxr : (ValTy.flatList p.results).length ≤ 1)
    (hff : floatFreeList p.results = true) {ys : List Flat}
    (hys : ys.map (·.type) = ValTy.flatList p.results) (hnone : liftArgs p.results ys = none)
    {cx : LiftLowerContext (E3 P)} {f : List Val × FlatCursor → Canon.P (E3 P) σ α}
    {g : α → Canon.P (E3 P) σ (Ret (E3 P))} {M : Machine.Config (E3 P) σ}
    {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)}
    (hc : M.ctl = ⟨th, .prog ((liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList ys) (resultTypes (witFt p)) >>= f) >>= g), segs⟩ :: rest)
    (hl : M.store.lockdown = false) : TrapsNextD prof P impl M := by
  have e : liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList ys)
      (resultTypes (witFt p)) =
        (ptrType cx >>= fun q => liftFlatTypes Limits.spec Quirks.none cx q
        (toClosedList p.results) ⟨ys, 0⟩ : Canon.P (E3 P) σ _) := by
    rw [resultTypes_witFt p hres, show FlatCursor.ofList ys = ⟨ys, 0⟩ from rfl,
      liftFlatValues_toClosed (max := ABI.maxFlatResults) Limits.spec Quirks.none cx hmaxr]
  have hT := liftFlatTypes_liftArgs (σ := σ) (E := E3 P) Limits.spec Quirks.none cx
    (ptrTypeIn M.store cx) hff hys
  rw [hnone] at hT
  obtain ⟨r, k₀, hk⟩ := hT
  have hc' : M.ctl = ⟨th, .prog (.op (S := Eff (E3 P) σ) .get fun s =>
      (liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn s cx) (toClosedList p.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest := by
    rw [hc, e]
    rfl
  have s₁ : Step prof (fun _ _ => false) (DI P impl) M .tau { M with ctl := ⟨th, .prog
      ((liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn M.store cx) (toClosedList p.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest } := Step.get hc'
  rw [hk] at s₁
  exact ⟨_, r, .cons ⟨by rw [hc]; exact List.cons_ne_nil _ _, hl⟩
    (.of_prog hc (fun _ _ e => by cases e) s₁) (.refl _), ⟨List.cons_ne_nil _ _, hl⟩,
    .of_prog rfl (fun _ _ e => by cases e) (.trap rfl)⟩

theorem runs_lift_someP {th : Option ThreadId} (p : Silmaril.Wasm.Component.FuncTy)
    (hres : p.results.length ≤ 1) (hmaxr : (ValTy.flatList p.results).length ≤ 1)
    (hff : floatFreeList p.results = true) {ys : List Flat}
    (hys : ys.map (·.type) = ValTy.flatList p.results)
    {ws : List Silmaril.Wasm.Component.Val} (hws : liftArgs p.results ys = some ws)
    (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) σ) :
    ∃ c, RunsQ (DI P impl) th (liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList ys) (resultTypes (witFt p))) m [.tau] (ws.map toRefVal, c) m := by
  have h := liftFlatTypes_liftArgs (σ := σ) (E := E3 P) Limits.spec Quirks.none cx
    (ptrTypeIn m.store cx) hff hys
  rw [hws] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rw [resultTypes_witFt p hres, show FlatCursor.ofList ys = ⟨ys, 0⟩ from rfl,
    liftFlatValues_toClosed (max := ABI.maxFlatResults) Limits.spec Quirks.none cx hmaxr]
  refine .get ?_
  show RunsQ _ _ (liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn m.store cx)
    (toClosedList p.results) ⟨ys, 0⟩) _ _ _ _
  rw [hc]
  exact .pure _ _

/-- `Task.return_` of a task whose caller record is a `canon_lower` record: the results are
lowered into the callout's subtask. -/
theorem runs_returnL {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {c : CallerId} {S : SubtaskId}
    {cx : LiftLowerContext (E3 P)} {ys : List Flat} {pos : Nat} {p : Silmaril.Wasm.Component.FuncTy}
    {xS : Subtask} {us : List Silmaril.Wasm.Component.Val}
    (ht : m.store.tasks = Gt ++ [y]) (hy : y.caller = c) (hst : y.state = .started)
    (hb : y.numBorrows = 0)
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys pos (witFt p) 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (hres : p.results.length ≤ 1) (hff : floatFreeList p.results = true)
    (hus : ValTy.checkList p.results us = true) (hmax : (ValTy.flatList p.results).length ≤ 1) :
    ∃ tr, RunsQ (DI P impl) th (Task.return_ ⟨Gt.length⟩ (us.map toRefVal)) m tr ()
      { m with
        store := CStore.setTaskState ⟨Gt.length⟩ .resolved
          (CStore.subtaskResolveSt S .returned (lowerArgs p.results us) m.store) } := by
  obtain ⟨tr, h⟩ := runs_lowerOnResolve (d := DI P impl) (th := th) (m := m) hc hS hidx hres hff
    hus hmax
  apply Exists.intro
  unfold Task.return_
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  apply RunsQ.bind (runs_trapIf (by rw [hst]; rfl) _ _)
  apply RunsQ.bind (runs_trapIf (by rw [hb]; rfl) _ _)
  rw [hy]
  unfold callUnit callRet perform Prog.lift
  apply RunsQ.bind (RunsQ.call (RunsQ.getObj_bind _ _ hc
    (RunsQ.bind (f := fun _ => pure Ret.unit) h (RunsQ.pure _ _)))
    (.pure _ _))
  exact runs_modifyStore _ _ rfl

theorem runs_unregisterG {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gth : List Runtime.Thread}
    {z : Runtime.Thread} {ι ι' : InstState} {i : Nat} {t' : ThreadId}
    (ht : m.store.tasks = Gt ++ [y]) (hst : y.state = .resolved)
    (hthr : m.store.threads = Gth ++ [z]) (hidx : z.index = some i)
    (hi : ArenaField.insts.get? m.store y.inst = some ι) (hrem : ι.removeThread? i = some (t', ι')) :
    RunsQ (DI P impl) th (Task.unregisterThread ⟨Gt.length⟩ ⟨Gth.length⟩) m [.tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ i m.store } := by
  unfold Task.unregisterThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  apply RunsQ.bind (runs_trapIf (by rw [hst]; simp) _ _)
  apply RunsQ.bind (runs_getObj ArenaField.threads _ _ (threads_get_last hthr))
  rw [hidx]
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind (runs_getObj ArenaField.insts _ _ hi)
  rw [hrem]
  exact runs_modifyStore _ _ (CStore.unregisterThreadSt_frame (E := E3 P) _ _ _ _).2.2.2.2.2.2.2.1
  rfl

theorem runs_exitG {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gth : List Runtime.Thread}
    {z : Runtime.Thread} {ι ι' : InstState} {i : Nat} {t' : ThreadId}
    (ht : m.store.tasks = Gt ++ [y]) (himp : y.implicitThread = some ⟨Gth.length⟩)
    (hst : y.state = .resolved) (hasync : y.ft.async_ = false)
    (hthr : m.store.threads = Gth ++ [z]) (hidx : z.index = some i)
    (hi : ArenaField.insts.get? m.store y.inst = some ι) (hrem : ι.removeThread? i = some (t', ι')) :
    RunsQ (DI P impl) th (Task.exitImplicitThread ⟨Gt.length⟩) m [.tau, .tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ i m.store } := by
  have hu := runs_unregisterG (impl := impl) (th := th) ht hst hthr hidx hi hrem
  unfold Task.exitImplicitThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  rw [himp]
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind hu
  exact runs_ite_false (by rw [hasync]; rfl) _ _
  rfl

/-- The store of the exporter's thread once its core activation starts. -/
def nstoreCore (S : CStore (E3 P)) (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy)
    (ιe' : InstState) (pos : Nat) : CStore (E3 P) :=
  LowerSt.setCallerPosSt ⟨S.callers.length⟩ pos (LowerSt.startSt ⟨S.subtasks.length⟩
    (CStore.setTaskState ⟨S.tasks.length⟩ .started
      (nstore S { inst := ⟨2⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p 0) (ntask₁ S p)
        ((thread₁ S.tasks).withIndex 1) (S.insts.set 1 ιe'))))

theorem nstoreCore_eq (S : CStore (E3 P)) (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy)
    (ιe' : InstState) (pos : Nat) :
    nstoreCore S ys p ιe' pos =
      nstore S { inst := ⟨2⟩, state := .started } (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p pos)
        ((ntask₁ S p).withState .started) ((thread₁ S.tasks).withIndex 1) (S.insts.set 1 ιe') := by
  simp [nstoreCore, nstore, LowerSt.setCallerPosSt, LowerSt.startSt, CStore.setTaskState,
    ArenaField.modify, Arena.modify, ArenaField.tasks, ArenaField.callers, ArenaField.subtasks,
    modify_concat_length, lowerRec, LowerSt.Caller.withPos]

/-- The subtask of a nested call resolved with `flat`. -/
def nsubRet (flat : List Flat) : Subtask :=
  { inst := ⟨2⟩, state := .returned, flatResults := flat }

/-- The exporter's task of a nested call once it exited. -/
def ntaskRet (S : CStore (E3 P)) (p : Silmaril.Wasm.Component.FuncTy) : Runtime.Task (E3 P) :=
  { (((ntask₁ S p).withState .started).withState .resolved) with
    threads := (((ntask₁ S p).withState .started).withState .resolved).threads.erase
      ⟨S.threads.length⟩ }

/-- The exporter's thread of a nested call once it exited. -/
def nthreadRet (S : CStore (E3 P)) : Runtime.Thread :=
  { (thread₁ S.tasks).withIndex 1 with status := .exited }

theorem nstore_return (S : CStore (E3 P)) (cs : (E3 P).Store (CanonHost (E3 P))) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) (ιe' : InstState) (pos : Nat) (flat : List Flat) :
    CStore.setTaskState ⟨S.tasks.length⟩ .resolved (CStore.subtaskResolveSt ⟨S.subtasks.length⟩
        .returned flat
        (nstore { S with core := cs } { inst := ⟨2⟩, state := .started }
          (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p pos) ((ntask₁ S p).withState .started)
          ((thread₁ S.tasks).withIndex 1) (S.insts.set 1 ιe'))) =
      nstore { S with core := cs } (nsubRet flat) (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p pos)
        (((ntask₁ S p).withState .started).withState .resolved) ((thread₁ S.tasks).withIndex 1)
        (S.insts.set 1 ιe') := by
  simp [nstore, CStore.subtaskResolveSt, CStore.setTaskState, ArenaField.modify, Arena.modify,
    ArenaField.tasks, ArenaField.subtasks, modify_concat_length, nsubRet]

theorem modify_set_self {α : Type} : ∀ (l : List α) (i : Nat) (a : α) (f : α → α),
    (l.set i a).modify i f = l.set i (f a)
  | [], _, _, _ => by simp
  | _ :: _, 0, _, _ => rfl
  | b :: l, i + 1, a, f => by
    show b :: (l.set i a).modify i f = b :: l.set i (f a)
    rw [modify_set_self l i a f]

theorem nstore_exit (S : CStore (E3 P)) (cs : (E3 P).Store (CanonHost (E3 P))) (sub : Subtask)
    (cl : Caller (E3 P)) (p : Silmaril.Wasm.Component.FuncTy) (ιe' : InstState) :
    threadStatusSt ⟨S.threads.length⟩ .exited
      (CStore.unregisterThreadSt ⟨S.tasks.length⟩ ⟨S.threads.length⟩ 1
        (nstore { S with core := cs } sub cl
          (((ntask₁ S p).withState .started).withState .resolved) ((thread₁ S.tasks).withIndex 1)
          (S.insts.set 1 ιe'))) =
      nstore { S with core := cs } sub cl (ntaskRet S p) (nthreadRet S)
        (S.insts.set 1 (InstState.removeThread 1 ιe')) := by
  have h₁ : (nstore { S with core := cs } sub cl
      (((ntask₁ S p).withState .started).withState .resolved) ((thread₁ S.tasks).withIndex 1)
      (S.insts.set 1 ιe')).task? ⟨S.tasks.length⟩ =
      some (((ntask₁ S p).withState .started).withState .resolved) := tasks_get_last rfl
  unfold CStore.unregisterThreadSt
  rw [h₁]
  simp [nstore, threadStatusSt, ArenaField.modify, Arena.modify, ArenaField.tasks,
    ArenaField.threads, ArenaField.insts, modify_concat_length, ntaskRet, nthreadRet]
  exact modify_set_self _ _ _ _

/-- The store after a nested call returned `us` at core store `cs`, before the importer's
callout program resumes. -/
def nstoreRet (S : CStore (E3 P)) (cs : (E3 P).Store (CanonHost (E3 P))) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) (ιe' : InstState) (pos : Nat)
    (us : List Silmaril.Wasm.Component.Val) : CStore (E3 P) :=
  nstore { S with core := cs } (nsubRet (lowerArgs p.results us))
    (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p pos) (ntaskRet S p) (nthreadRet S)
    (S.insts.set 1 (InstState.removeThread 1 ιe'))

theorem lrun_refl_store {prof : ProfileKind} {hr : HostReady σ}
    {d : Call (E3 P) → Canon.P (E3 P) σ (Ret (E3 P))} {m : Machine.Config (E3 P) σ}
    {S' : CStore (E3 P)} (h : m.store = S') : LRun prof hr d m [] { m with store := S' } := by
  obtain ⟨⟩ := m
  dsimp only at h
  subst h
  exact .refl _

/-- **The exporter's thread of a nested call**: from its first activation, a live run to its
core activation on the lowered arguments; when the core activation returns flat values of the
result types, the thread lowers the lifted results into the callout's subtask and exits, or traps
where the lift fails. -/
theorem lift_body_at (M₀ : Machine.Config (E3 P) σ) (S : CStore (E3 P)) (ys : List Flat)
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
          { M₀ with store := nstoreRet S y.1 ys p ιe' pos us, ctl := R }) ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = none →
        TrapsNextD prof P impl
          (retCfg { M₀ with store := nstoreCore S ys p ιe' pos } (some ⟨S.threads.length⟩) K'
            segs' R y zs)) := by
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
    apply LRun.store_congr (S' := nstore { S with core := y.1 } { inst := ⟨2⟩, state := .started }
      (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p pos) ((ntask₁ S p).withState .started)
      ((thread₁ S.tasks).withIndex 1) (S.insts.set 1 ιe')) (by rw [nstoreCore_eq]; rfl)
    apply RunsQ.chunk2 rfl (runs_lift_someP (impl := impl) p hres hmaxr hrf hzs hus _ _).choose_spec
      (by exact hl)
    apply RunsQ.chunk2 rfl (by exact (runs_returnL (impl := impl) (Gt := S.tasks) rfl rfl rfl rfl
        (callers_get_last rfl) (subtasks_get_last rfl) rfl hres hrf
        (Silmaril.Wasm.Component.checkList_of_liftArgs hus) hmaxr).choose_spec) (by exact hl)
    apply LRun.store_congr (nstore_return S y.1 ys p ιe' pos _)
    apply RunsQ.chunk rfl (runs_exitG (impl := impl) (Gt := S.tasks) (Gth := S.threads) rfl rfl rfl
      rfl rfl rfl (by exact hie') hrem) (by exact hl)
    lstep ((CStore.unregisterThreadSt_frame (E := E3 P) _ _ _ _).2.2.2.2.2.2.2.1.trans hl)
    exact lrun_refl_store (nstore_exit S y.1 _ _ p ιe')
  · intro y zs hzs hn
    exact lrun_lift_trapP p hres hmaxr hrf hzs hn rfl (by exact hl)

/-! ## The importer's side of a nested call -/

/-- The records of a nested call that returned the flat results `flat`. -/
def nrec (S : CStore (E3 P)) (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy) (pos : Nat)
    (flat : List Flat) : NRec P :=
  ⟨{ nsubRet flat with onCancel := .task ⟨S.tasks.length⟩, lenders := none },
    lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p pos, ntaskRet S p, nthreadRet S⟩

theorem nstore_deliver (S : CStore (E3 P)) (sub : Subtask) (cl : Caller (E3 P))
    (tk : Runtime.Task (E3 P)) (thr : Runtime.Thread) (is : List InstState) (r : CancelRef)
    (hl : sub.lenders = some []) :
    CStore.deliverResolveSt ⟨S.subtasks.length⟩
        (LowerSt.setOnCancelSt ⟨S.subtasks.length⟩ r (nstore S sub cl tk thr is)) =
      nstore S { sub with onCancel := r, lenders := none } cl tk thr is := by
  have h₁ : (LowerSt.setOnCancelSt ⟨S.subtasks.length⟩ r (nstore S sub cl tk thr is)).subtask?
      ⟨S.subtasks.length⟩ = some { sub with onCancel := r } :=
    subtasks_get_last (by simp [LowerSt.setOnCancelSt, nstore, ArenaField.modify, Arena.modify,
      ArenaField.subtasks, modify_concat_length])
  unfold CStore.deliverResolveSt
  rw [h₁]
  simp only [hl, Option.getD_some, List.foldl_nil]
  simp [LowerSt.setOnCancelSt, nstore, ArenaField.modify, Arena.modify, ArenaField.subtasks,
    modify_concat_length]

theorem nstore_extN (B : Machine.Config (E3 P) σ) (ιe ι : InstState) (N : List (NRec P))
    (C C₁ : List (Option (Activation (E3 P) σ))) (c₀ cs : (E3 P).Store (CanonHost (E3 P)))
    (r : NRec P) :
    nstore { ({ (extN B ιe N C).store with core := c₀ } : CStore (E3 P)) with core := cs } r.sub
        r.caller r.task r.thread ((extN B ιe N C).store.insts.set 1 ι) =
      { (extN B ι (N ++ [r]) C₁).store with core := cs } := by
  simp only [nstore, extN, List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  congr 1
  exact List.set_set _

/-- **The importer's side of a nested call**: from the callout of the importer's core activation
to the exporter's lifted function `f`, a live run to the first activation of the exporter's
thread above the parked callout (`R`); from the end of that thread, with the subtask resolved,
the callout program delivers the results and the importer's core activation resumes. -/
theorem nest_pre (B : Machine.Config (E3 P) σ) (ιe ιe' : InstState) (N : List (NRec P))
    (C : List (Option (Activation (E3 P) σ))) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (x : CoreSt (E3 P)) (f : FuncId) (a : (E3 P).FuncAddr)
    (p : Silmaril.Wasm.Component.FuncTy) (ys : List Flat) (ιi : InstState)
    (hs : (E3 P).status x.1 x.2 = .callout (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hentry : calloutEntry (extN B ιe N C).store th (.lowered f (witFt p) {} ⟨2⟩) = none)
    (hi : ArenaField.insts.get? (extN B ιe N C).store ⟨2⟩ = some ιi) (hleave : ιi.mayLeave = true)
    (hf : ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩)) :
    ∃ C₁ R tr, LRun prof (fun _ _ => false) (DI P impl) (coreCfg (extN B ιe N C) th K segs rest x)
      tr { coreCfg (extN B ιe N C) th K segs rest x with
        store := nstore { (extN B ιe N C).store with core := x.1 } { inst := ⟨2⟩ }
          (lowerRec ⟨(extN B ιe N C).store.subtasks.length⟩ ⟨2⟩ ys p 0)
          (ntask₀ { (extN B ιe N C).store with core := x.1 } p)
          (thread₁ (extN B ιe N C).store.tasks) (extN B ιe N C).store.insts
        conts := C₁
        ctl := ⟨some ⟨(extN B ιe N C).store.threads.length⟩,
          .prog (DI P impl (.threadBody (.liftImplicit ⟨(extN B ιe N C).store.tasks.length⟩ a))),
          []⟩ :: R } ∧
      ∀ (cs : (E3 P).Store (CanonHost (E3 P))) (pos : Nat) (us : List Silmaril.Wasm.Component.Val),
        ∃ tr', LRun prof (fun _ _ => false) (DI P impl)
          { coreCfg (extN B ιe N C) th K segs rest x with
            store := nstoreRet { (extN B ιe N C).store with core := x.1 } cs ys p ιe' pos us
            conts := C₁
            ctl := R } tr'
          (coreCfg (extN B (InstState.removeThread 1 ιe')
            (N ++ [nrec { (extN B ιe N C).store with core := x.1 } ys p pos (lowerArgs p.results us)])
            C₁) th K segs rest (cs, (E3 P).resume cs x.2 (.values (lowerArgs p.results us)))) := by
  let S : CStore (E3 P) := { (extN B ιe N C).store with core := x.1 }
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨?_, ?_⟩
  apply LRun.cons (m := coreCfg (extN B ιe N C) th K segs rest x) ⟨List.cons_ne_nil _ _, rfl⟩
    (callout_stepD rfl hs)
  apply lrun_hostCallout (m := coreCfg (extN B ιe N C) th K segs rest x) rfl hentry
  apply RunsQ.chunk2 rfl (runs_getObj ArenaField.insts _ _ (by exact hi)) rfl
  apply RunsQ.chunk2 rfl (runs_trapIf (by rw [hleave]; rfl) _ _) rfl
  apply RunsQ.chunk2 rfl (runs_allocObj ArenaField.subtasks _ _ rfl) rfl
  apply RunsQ.chunk2 rfl (runs_allocObj ArenaField.callers _ _ rfl) rfl
  mstep
  apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (by exact hf)) rfl
  apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) rfl
  apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
  apply RunsQ.chunk2 rfl (RunsQ.get (.pure _ _)) rfl
  apply RunsQ.chunk2 rfl (runs_ite_false (impl := impl) (by exact threadIs_last rfl) _ _) rfl
  apply LRun.prog rfl (fun _ _ e => by cases e) rfl
    (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
  apply LRun.store_congr (nstore_resume S ys p)
  exact .refl _
  intro cs pos us
  apply Exists.intro
  apply RunsQ.chunk rfl (runs_callUnit_loop (impl := impl) (Gt := S.tasks) rfl rfl) rfl
  lstep (rfl : (extN B ιe N C).store.lockdown = false)
  lstep (rfl : (extN B ιe N C).store.lockdown = false)
  apply RunsQ.chunk rfl (runs_lowerTail (d := DI P impl)
    (X := { nsubRet (lowerArgs p.results us) with onCancel := .task ⟨S.tasks.length⟩ })
    (subtasks_get_last (G := S.subtasks) (by
      simp only [LowerSt.setOnCancelSt, nstoreRet, nstore, ArenaField.modify, Arena.modify,
        ArenaField.subtasks, ArenaField.size, coreCfg, modify_concat_length]
      rfl))
    rfl rfl) rfl
  apply LRun.store_congr (nstore_deliver _ _ _ _ _ _ _ rfl)
  repeat lstep (rfl : (extN B ιe N C).store.lockdown = false)
  have he := nstore_extN B ιe (InstState.removeThread 1 ιe') N C C x.1 cs
    (nrec { (extN B ιe N C).store with core := x.1 } ys p pos (lowerArgs p.results us))
  exact lrun_refl_store (by exact he)

/-- **A callout of the importer answered by the exporter's `canon lift`**: from the importer's
core activation stopped at a callout to the trampoline of the exporter's lifted function `f`
(core address `a`, type `p`), a live deterministic run to the exporter's core activation on the
lowered arguments, nested above the parked callout; when it returns flat values of the result
types, the lifted results are lowered back and the importer's activation resumes with them, the
records of the nested call appended (`nrec`) and the exporter's thread table reset; where the
lift of the results fails, the machine traps. -/
theorem nest_at (B : Machine.Config (E3 P) σ) (ιe ιe' : InstState) (N : List (NRec P))
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
      M₁.store.core = x.1 ∧ M₁.store.lockdown = false ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat) (us : List Silmaril.Wasm.Component.Val),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = some us →
        ∃ tr', LRun prof (fun _ _ => false) (DI P impl) (retCfg M₁ th' K' segs' rest' y zs) tr'
          (coreCfg (extN B (InstState.removeThread 1 ιe')
            (N ++ [nrec { (extN B ιe N C).store with core := x.1 } ys p pos (lowerArgs p.results us)])
            C₁) th K segs rest (y.1, (E3 P).resume y.1 x.2 (.values (lowerArgs p.results us))))) ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = none →
        TrapsNextD prof P impl (retCfg M₁ th' K' segs' rest' y zs)) := by
  obtain ⟨C₁, R, tr₁, h₁, hback⟩ := nest_pre (prof := prof) (impl := impl) B ιe ιe' N C th K segs
    rest x f a p ys ιi hs hentry hi hleave hf
  have hie : ({ (extN B ιe N C).store with core := x.1 } : CStore (E3 P)).insts[1]? = some ιe :=
    List.getElem?_set_self hlen
  obtain ⟨pos, K', segs', tr₂, h₂, hret, htrap⟩ := lift_body_at (prof := prof) (impl := impl)
    { coreCfg (extN B ιe N C) th K segs rest x with conts := C₁ }
    { (extN B ιe N C).store with core := x.1 } ys p ws a R hie hadd hrem rfl hpf hys hmaxp hws
    hres hrf hmaxr
  refine ⟨pos, C₁, _, _, K', segs', _, _, h₁.trans h₂, rfl, rfl, rfl, ?_, htrap⟩
  intro y zs us hzs hus
  obtain ⟨tr₃, h₃⟩ := hret y zs us hzs hus
  obtain ⟨tr₄, h₄⟩ := hback y.1 pos us
  exact ⟨_, h₃.trans h₄⟩

/-! ## A callout whose arguments do not lift -/

/-- From `M`, a live run reaches a configuration whose only step is a trap. -/
def TrapsFrom (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (M : Machine.Config (E3 P) σ) : Prop :=
  ∃ tr mT r, LRun prof (fun _ _ => false) (DI P impl) M tr mT ∧ Live mT ∧
    UniqueStep prof (fun _ _ => false) (DI P impl) mT (.trap r) (trapCfg mT)

theorem TrapsFrom.lrun {M M' : Machine.Config (E3 P) σ} {tr : List (Label (E3 P) σ)}
    (h : LRun prof (fun _ _ => false) (DI P impl) M tr M') (h' : TrapsFrom prof P impl M') :
    TrapsFrom prof P impl M := by
  obtain ⟨tr', mT, r, h₁, hl, hu⟩ := h'
  exact ⟨_, mT, r, h.trans h₁, hl, hu⟩

/-- A big-step run to a trap in focus. -/
theorem TrapsQ.trapsFrom {α : Type} {th : Option ThreadId} {p : Canon.P (E3 P) σ α}
    {f : α → Canon.P (E3 P) σ (Ret (E3 P))} {M mT : Machine.Config (E3 P) σ}
    {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)} {tr : List (Label (E3 P) σ)}
    (hc : M.ctl = ⟨th, .prog (p >>= f), segs⟩ :: rest) (h : TrapsQ (DI P impl) th p M tr mT)
    (hl : M.store.lockdown = false) : TrapsFrom prof P impl M := by
  have e : M = { M with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } := by
    cases M
    cases hc
    rfl
  obtain ⟨q, segs', r, hrun, hlive, hu⟩ := h.lrun (prof := prof) (hr := fun _ _ => false) hl f
    segs rest
  rw [← e] at hrun
  exact ⟨_, _, r, hrun, hlive, hu⟩

/-- Big-step runs to a trap do not read or write the control chain. -/
theorem TrapsQ.withCtl {d : Call (E3 P) → Canon.P (E3 P) σ (Ret (E3 P))} {α : Type}
    {th : Option ThreadId} {p : Canon.P (E3 P) σ α} {m mT : Machine.Config (E3 P) σ}
    {tr : List (Label (E3 P) σ)} (h : TrapsQ d th p m tr mT) (c : List (Activation (E3 P) σ)) :
    TrapsQ d th p { m with ctl := c } tr { mT with ctl := c } := by
  induction h with
  | trap _ hp => exact .trap _ hp
  | bind h₁ _ ih => exact .bind (h₁.withCtl c) ih
  | left _ ih => exact .left ih
  | callIn _ ih => exact .callIn ih

/-- `on_start` of a `canon_lower` caller record whose arguments do not lift traps. -/
theorem traps_lowerOnStart {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {c : CallerId}
    {S : SubtaskId} {cx : LiftLowerContext (E3 P)} {ys : List Flat}
    {p : Silmaril.Wasm.Component.FuncTy} {xS : Subtask}
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys 0 (witFt p) 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (hff : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmax : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    ∃ tr, TrapsQ (DI P impl) th (lowerOnStart Limits.spec Quirks.none c) m tr
      { m with store := LowerSt.startSt S m.store } := by
  have hT : IsTrap (liftFlatTypes (σ := σ) Limits.spec Quirks.none cx
      (ptrTypeIn (LowerSt.startSt S m.store) cx) (toClosedList p.params) ⟨ys, 0⟩) := by
    have h := liftFlatTypes_liftArgs (σ := σ) (E := E3 P) Limits.spec Quirks.none cx
      (ptrTypeIn (LowerSt.startSt S m.store) cx) hff hys
    rwa [hws] at h
  have hmp : RunsQ (DI P impl) th (maybeOnProgress S) m [.tau] () m :=
    RunsQ.getObj_bind _ _ hS (by rw [hidx]; exact RunsQ.pure _ _)
  have hlift : TrapsQ (DI P impl) th (liftFlatValues Limits.spec Quirks.none cx 16 ⟨ys, 0⟩
      ((witFt p).params.map (·.2))) { m with store := LowerSt.startSt S m.store } [.tau]
      { m with store := LowerSt.startSt S m.store } := by
    rw [liftFlatValues_witFt hmax]
    exact TrapsQ.bind (RunsQ.get (RunsQ.pure _ _)) (TrapsQ.trap _ hT)
  exact ⟨_, TrapsQ.bind (RunsQ.getObj _ _ hc) (TrapsQ.bind hmp
    (TrapsQ.bind (RunsQ.modify rfl (RunsQ.pure _ _)) (TrapsQ.left hlift)))⟩

/-- `Task.start` of a task whose `canon_lower` caller record's arguments do not lift traps. -/
theorem traps_startL {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {c : CallerId} {S : SubtaskId}
    {cx : LiftLowerContext (E3 P)} {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy}
    {xS : Subtask}
    (ht : m.store.tasks = Gt ++ [y]) (hy : y.caller = c)
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys 0 (witFt p) 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (hff : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmax : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    ∃ tr mT, TrapsQ (DI P impl) th (Task.start ⟨Gt.length⟩) m tr mT := by
  obtain ⟨tr, h⟩ := traps_lowerOnStart (impl := impl) (th := th)
    (m := { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store }) (by exact hc)
    (by exact hS) hidx hff hys hmax hws
  have hon : TrapsQ (DI P impl) th (DI P impl (.onStart c))
      { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store } (.tau :: tr)
      { m with store := LowerSt.startSt S (CStore.setTaskState ⟨Gt.length⟩ .started m.store) } :=
    TrapsQ.bind (RunsQ.getObj _ _ (by exact hc)) (TrapsQ.left h)
  have hs : TrapsQ (DI P impl) th (callVals (.onStart y.caller) : Canon.P (E3 P) σ (List Val))
      { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store } (.tau :: .tau :: tr)
      { m with store := LowerSt.startSt S (CStore.setTaskState ⟨Gt.length⟩ .started m.store) } := by
    rw [hy]
    exact TrapsQ.callIn hon
  unfold Task.start
  exact ⟨_, _, TrapsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
    (TrapsQ.bind (runs_modifyStore _ _ rfl) hs)⟩

/-- **The exporter's thread traps when the callout's arguments do not lift.** -/
theorem lift_body_trap (M₀ : Machine.Config (E3 P) σ) (S : CStore (E3 P)) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) {ιe ιe' : InstState}
    (a : (E3 P).FuncAddr) (R : List (Activation (E3 P) σ))
    (hie : S.insts[1]? = some ιe) (hadd : ιe.addThread? ⟨S.threads.length⟩ = some (1, ιe'))
    (hl : S.lockdown = false)
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    TrapsFrom prof P impl
      { M₀ with
        store := nstore S { inst := ⟨2⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p 0) (ntask₀ S p)
          (thread₁ S.tasks) S.insts
        ctl := ⟨some ⟨S.threads.length⟩,
          .prog (DI P impl (.threadBody (.liftImplicit ⟨S.tasks.length⟩ a))), []⟩ :: R } := by
  obtain ⟨trS, mT, hst⟩ := traps_startL (impl := impl) (th := some ⟨S.threads.length⟩)
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
  refine TrapsFrom.lrun h₁ ?_
  rw [nstore_enter S _ _ p hie hadd]
  refine TrapsFrom.lrun (RunsQ.lrun_at (runs_getObj ArenaField.tasks _ _ (tasks_get_last rfl))
    (by exact hl) _ rfl) ?_
  exact TrapsQ.trapsFrom rfl (hst.withCtl _) (by exact hl)

/-- **A callout of the importer whose arguments do not lift traps** (in the exporter's
`on_start`). -/
theorem nest_trap_args (B : Machine.Config (E3 P) σ) (ιe ιe' : InstState) (N : List (NRec P))
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
    TrapsFrom prof P impl (coreCfg (extN B ιe N C) th K segs rest x) := by
  obtain ⟨C₁, R, tr₁, h₁, -⟩ := nest_pre (prof := prof) (impl := impl) B ιe ιe' N C th K segs
    rest x f a p ys ιi hs hentry hi hleave hf
  have hie : ({ (extN B ιe N C).store with core := x.1 } : CStore (E3 P)).insts[1]? = some ιe :=
    List.getElem?_set_self hlen
  exact TrapsFrom.lrun h₁ (lift_body_trap (prof := prof) (impl := impl)
    { coreCfg (extN B ιe N C) th K segs rest x with conts := C₁ }
    { (extN B ιe N C).store with core := x.1 } ys p a R hie hadd rfl hpf hys hmaxp hws)

end Silmaril.Proofs.Wasm.Component.Reference
