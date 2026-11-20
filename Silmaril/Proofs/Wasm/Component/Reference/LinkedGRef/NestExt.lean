module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef.Nest
public import Silmaril.Wasm.Component.Reference.LinkedGRef.Defs

/-!
# The return half of a nested call from an extended store

`nest_atG` (`Nest`) returns from the callee's core activation in the callee's frame `M₁` with
only the core store replaced (`retCfg M₁ … y zs`), and its proofs read the callee's records as
the *last* entry of each arena (`tasks_get_last`, `subtasks_get_last`, …). A nested linked
exporter appends records of its own nested calls, changes its own instances and the saved
continuation slots before it returns. Here the return half starts from **any** store `S'` that
keeps the callee's records at their indices (`CalleeAt`: the arenas of `M₁.store` are prefixes
of those of `S'`, the callee's instance state is unchanged, the store is not locked down) and
**any** continuation slots `C'`; the records are looked up by index.

* `runs_loopI`, `runs_callUnit_loopI`, `runs_returnI`, `runs_unregisterI`, `runs_exitI`: the
  big-step runs of `MultiProgs`/`LinkCallout` with the task and thread looked up by index;
* `retStG`, `retStoreG`: the stores after the callee's thread exited, and after the caller's
  callout program delivered the results: `S'` with the callee's records replaced at their
  indices (the records of `nrecG`) and the callee's thread table reset;
* `lift_body_atX`, `nest_preX`, `nest_atX`: `lift_body_atG`, `nest_preG`, `nest_atG` with the
  return half (and the trap of the result lift) from `CalleeAt` stores; `nest_atX` also exposes
  the callee's store (`nstoreCoreG`), its thread (`⟨M.store.threads.length⟩`) and its instance
  (`instOfThread?`);
* the read-back of these runs is `LRun.inv` of the runs of `nest_atX`, and `trapsAtSH_back` of
  its trap, as for `nest_backG`;
* `nest_atG_of_X`: the return half of `nest_atG` is the instance `S' = ⟨M₁.store, y.1⟩` (the
  component store and the core store `y.1`), `C' = M₁.conts`.

No continuation slot is read on these paths: the machine reads `conts` only in `resumeThread`
and `block`, and the nested call's `resumeThread` reads the slot its own `newThread` has just
written. So `C'` is arbitrary and is carried to the caller's resumed frame.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## Lists -/

theorem modify_eq_set_of {α : Type} : ∀ {l : List α} {i : Nat} {a : α}, l[i]? = some a →
    ∀ f : α → α, l.modify i f = l.set i (f a)
  | [], _, _, h, _ => by simp at h
  | b :: l, 0, a, h, f => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp
  | b :: l, i + 1, a, h, f => by
    simp only [List.getElem?_cons_succ] at h
    rw [List.modify_succ_cons, modify_eq_set_of h f]
    rfl

theorem prefix_getElem? {α : Type} {l l' : List α} (h : l <+: l') {i : Nat} {a : α}
    (hi : l[i]? = some a) : l'[i]? = some a := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1]
  exact hi

theorem set_concat_length {α : Type} : ∀ (l : List α) (a b : α),
    (l ++ [a]).set l.length b = l ++ [b]
  | [], _, _ => rfl
  | c :: l, a, b => congrArg (c :: ·) (set_concat_length l a b)

theorem lt_of_getElem? {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    i < l.length := (List.getElem?_eq_some_iff.mp h).1

/-! ## Big-step runs with records looked up by index -/

theorem runs_loopI {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {T : TaskId}
    {y : Runtime.Task (E3 P)} (ht : ArenaField.tasks.get? m.store T = some y)
    (hst : y.state = .resolved) :
    RunsQ (DI P impl) th (DI P impl (.loop (.syncLiftLoop T))) m [.tau] .unit m := by
  show RunsQ _ _ (syncLiftLoopBody (fun _ _ => false) T) _ _ _ _
  unfold syncLiftLoopBody
  apply RunsQ.bind (tr₂ := []) (runs_getObj ArenaField.tasks _ _ ht)
  rw [hst]
  exact .pure _ _

theorem runs_callUnit_loopI {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {T : TaskId}
    {y : Runtime.Task (E3 P)} (ht : ArenaField.tasks.get? m.store T = some y)
    (hst : y.state = .resolved) :
    RunsQ (DI P impl) th (callUnit (.loop (.syncLiftLoop T))) m [.tau, .tau, .tau] () m := by
  unfold callUnit callRet perform Prog.lift
  exact RunsQ.call (runs_loopI ht hst) (.pure _ _)

/-- `runs_returnL` with the task looked up by index. -/
theorem runs_returnI {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {T : TaskId}
    {y : Runtime.Task (E3 P)} {c : CallerId} {S : SubtaskId}
    {cx : LiftLowerContext (E3 P)} {ys : List Flat} {pos : Nat} {p : Silmaril.Wasm.Component.FuncTy}
    {xS : Subtask} {us : List Silmaril.Wasm.Component.Val}
    (ht : ArenaField.tasks.get? m.store T = some y) (hy : y.caller = c) (hst : y.state = .started)
    (hb : y.numBorrows = 0)
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys pos (witFt p) 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (hres : p.results.length ≤ 1) (hff : floatFreeList p.results = true)
    (hus : ValTy.checkList p.results us = true) (hmax : (ValTy.flatList p.results).length ≤ 1) :
    ∃ tr, RunsQ (DI P impl) th (Task.return_ T (us.map toRefVal)) m tr ()
      { m with
        store := CStore.setTaskState T .resolved
          (CStore.subtaskResolveSt S .returned (lowerArgs p.results us) m.store) } := by
  obtain ⟨tr, h⟩ := runs_lowerOnResolve (d := DI P impl) (th := th) (m := m) hc hS hidx hres hff
    hus hmax
  apply Exists.intro
  unfold Task.return_
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ ht)
  apply RunsQ.bind (runs_trapIf (by rw [hst]; rfl) _ _)
  apply RunsQ.bind (runs_trapIf (by rw [hb]; rfl) _ _)
  rw [hy]
  unfold callUnit callRet perform Prog.lift
  apply RunsQ.bind (RunsQ.call (RunsQ.getObj_bind _ _ hc
    (RunsQ.bind (f := fun _ => pure Ret.unit) h (RunsQ.pure _ _)))
    (.pure _ _))
  exact runs_modifyStore _ _ rfl

theorem runs_unregisterI {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {T : TaskId}
    {y : Runtime.Task (E3 P)} {H : ThreadId} {z : Runtime.Thread} {ι ι' : InstState} {i : Nat}
    {t' : ThreadId}
    (ht : ArenaField.tasks.get? m.store T = some y) (hst : y.state = .resolved)
    (hthr : ArenaField.threads.get? m.store H = some z) (hidx : z.index = some i)
    (hi : ArenaField.insts.get? m.store y.inst = some ι) (hrem : ι.removeThread? i = some (t', ι')) :
    RunsQ (DI P impl) th (Task.unregisterThread T H) m [.tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt T H i m.store } := by
  unfold Task.unregisterThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ ht)
  apply RunsQ.bind (runs_trapIf (by rw [hst]; simp) _ _)
  apply RunsQ.bind (runs_getObj ArenaField.threads _ _ hthr)
  rw [hidx]
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind (runs_getObj ArenaField.insts _ _ hi)
  rw [hrem]
  exact runs_modifyStore _ _ (CStore.unregisterThreadSt_frame (E := E3 P) _ _ _ _).2.2.2.2.2.2.1
  rfl

theorem runs_exitI {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {T : TaskId}
    {y : Runtime.Task (E3 P)} {H : ThreadId} {z : Runtime.Thread} {ι ι' : InstState} {i : Nat}
    {t' : ThreadId}
    (ht : ArenaField.tasks.get? m.store T = some y) (himp : y.implicitThread = some H)
    (hst : y.state = .resolved) (hasync : y.ft.async_ = false)
    (hthr : ArenaField.threads.get? m.store H = some z) (hidx : z.index = some i)
    (hi : ArenaField.insts.get? m.store y.inst = some ι) (hrem : ι.removeThread? i = some (t', ι')) :
    RunsQ (DI P impl) th (Task.exitImplicitThread T) m [.tau, .tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt T H i m.store } := by
  have hu := runs_unregisterI (impl := impl) (th := th) ht hst hthr hidx hi hrem
  unfold Task.exitImplicitThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ ht)
  rw [himp]
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind hu
  exact runs_ite_false (by rw [hasync]; rfl) _ _
  rfl

/-! ## The callee's records in a later store -/

/-- **The callee's records of a nested call are kept in `S'`**: the arenas of the store at the
start of the callee's core activation (`nstoreCoreG ie ii S ys p ιe' pos`) are prefixes of those
of `S'`, the callee's instance state at `ie` is unchanged, and `S'` is not locked down. -/
structure CalleeAt (ie ii : Nat) (S : CStore (E3 P)) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) (ιe' : InstState) (pos : Nat) (S' : CStore (E3 P)) :
    Prop where
  subtasks : (nstoreCoreG ie ii S ys p ιe' pos).subtasks <+: S'.subtasks
  callers : (nstoreCoreG ie ii S ys p ιe' pos).callers <+: S'.callers
  tasks : (nstoreCoreG ie ii S ys p ιe' pos).tasks <+: S'.tasks
  threads : (nstoreCoreG ie ii S ys p ιe' pos).threads <+: S'.threads
  inst : S'.insts[ie]? = some ιe'
  lockdown : S'.lockdown = false

namespace CalleeAt

variable {ie ii : Nat} {S : CStore (E3 P)} {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy}
  {ιe' : InstState} {pos : Nat} {S' : CStore (E3 P)}

theorem subtask (h : CalleeAt ie ii S ys p ιe' pos S') :
    S'.subtasks[S.subtasks.length]? = some ({ inst := ⟨ii⟩, state := .started } : Subtask) := by
  refine prefix_getElem? h.subtasks ?_
  rw [nstoreCore_eqG]
  exact List.getElem?_concat_length

theorem caller (h : CalleeAt ie ii S ys p ιe' pos S') :
    S'.callers[S.callers.length]? = some (lowerRec ⟨S.subtasks.length⟩ ⟨ii⟩ ys p pos) := by
  refine prefix_getElem? h.callers ?_
  rw [nstoreCore_eqG]
  exact List.getElem?_concat_length

theorem task (h : CalleeAt ie ii S ys p ιe' pos S') :
    S'.tasks[S.tasks.length]? = some ((ntask₁G ie S p).withState .started) := by
  refine prefix_getElem? h.tasks ?_
  rw [nstoreCore_eqG]
  exact List.getElem?_concat_length

theorem thread (h : CalleeAt ie ii S ys p ιe' pos S') :
    S'.threads[S.threads.length]? = some ((thread₁ S.tasks).withIndex 1) := by
  refine prefix_getElem? h.threads ?_
  rw [nstoreCore_eqG]
  exact List.getElem?_concat_length

end CalleeAt

/-- `M₁.store` itself, with any core store, keeps the callee's records. -/
theorem calleeAt_self (ie ii : Nat) (S : CStore (E3 P)) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) {ιe' : InstState} (pos : Nat)
    (hlen : ie < S.insts.length) (hl : S.lockdown = false) :
    CalleeAt ie ii S ys p ιe' pos (nstoreCoreG ie ii S ys p ιe' pos) where
  subtasks := List.prefix_refl _
  callers := List.prefix_refl _
  tasks := List.prefix_refl _
  threads := List.prefix_refl _
  inst := by
    show (nstoreCoreG ie ii S ys p ιe' pos).insts[ie]? = _
    rw [nstoreCore_eqG]
    exact List.getElem?_set_self hlen
  lockdown := by
    show (nstoreCoreG ie ii S ys p ιe' pos).lockdown = _
    rw [nstoreCore_eqG]
    exact hl

/-- **An exporter's store extension of a frame `M₁` extends its arenas**: the subtask, caller,
task and thread arenas of `M₁.store` are prefixes of those of `S'`. -/
theorem storeExt_prefixes {e : ExpSpec} {d : e.RefData P} {pl : d.Pl}
    {M₁ : Machine.Config (E3 P) σ} {S : CStore (E3 P)} {S' : RefStore (E3 P)}
    (hst : M₁.store = S) (hext : d.StoreExt pl M₁.ref S') :
    S.subtasks <+: S'.subtasks ∧ S.callers <+: S'.callers ∧ S.tasks <+: S'.tasks ∧
      S.threads <+: S'.threads := by
  subst hst
  exact ⟨hext.subtasks, hext.callers, hext.tasks, hext.threads⟩

/-- **An exporter's store extension keeps the callee's records**: from the callee's frame `M₁`
at the start of its core activation, a store `S'` extending `M₁`'s by the exporter's changes
(`StoreExt`), with the callee's instance state at `ie` and not locked down, keeps them. -/
theorem calleeAt_ext {ie ii : Nat} {S : CStore (E3 P)} {ys : List Flat}
    {p : Silmaril.Wasm.Component.FuncTy} {ιe' : InstState} {pos : Nat} {e : ExpSpec}
    {d : e.RefData P} {pl : d.Pl} {M₁ : Machine.Config (E3 P) σ} {S' : RefStore (E3 P)}
    (hst : M₁.store = nstoreCoreG ie ii S ys p ιe' pos) (hext : d.StoreExt pl M₁.ref S')
    (hinst : S'.insts[ie]? = some ιe') (hl : S'.lockdown = false) :
    CalleeAt ie ii S ys p ιe' pos S'.toCStore where
  subtasks := (storeExt_prefixes hst hext).1
  callers := (storeExt_prefixes hst hext).2.1
  tasks := (storeExt_prefixes hst hext).2.2.1
  threads := (storeExt_prefixes hst hext).2.2.2
  inst := hinst
  lockdown := hl

/-! ## The stores of the return -/

/-- The store after the callee's thread of a nested call exited, from the store `S'` at its
return: the subtask resolved with `flat`, the task resolved without the thread, the thread
exited, the callee's thread table reset. -/
def retStG (ie ii : Nat) (S : CStore (E3 P)) (p : Silmaril.Wasm.Component.FuncTy)
    (ιe' : InstState) (flat : List Flat) (S' : CStore (E3 P)) : CStore (E3 P) :=
  { S' with
    subtasks := List.set S'.subtasks S.subtasks.length (nsubRetG ii flat)
    tasks := List.set S'.tasks S.tasks.length (ntaskRetG ie S p)
    threads := List.set S'.threads S.threads.length (nthreadRet S)
    insts := List.set S'.insts ie (InstState.removeThread 1 ιe') }

/-- **The caller's store after a nested call** returned to it, from the store `S'` at the
callee's return: the records `r` written at the callee's indices (those of `S`), the callee's
instance state `ι` at `ie`. -/
def retStoreG (S' S : CStore (E3 P)) (ie : Nat) (ι : InstState) (r : NRec P) : CStore (E3 P) :=
  { S' with
    subtasks := List.set S'.subtasks S.subtasks.length r.sub
    tasks := List.set S'.tasks S.tasks.length r.task
    threads := List.set S'.threads S.threads.length r.thread
    insts := List.set S'.insts ie ι }

section Stores

variable {ie ii : Nat} {S : CStore (E3 P)} {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy}
  {ιe' : InstState} {pos : Nat} {S' : CStore (E3 P)}

theorem retSt_resolve (h : CalleeAt ie ii S ys p ιe' pos S') (flat : List Flat) :
    CStore.setTaskState ⟨S.tasks.length⟩ .resolved
        (CStore.subtaskResolveSt ⟨S.subtasks.length⟩ .returned flat S') =
      { S' with
        subtasks := List.set S'.subtasks S.subtasks.length (nsubRetG ii flat)
        tasks := List.set S'.tasks S.tasks.length
          (((ntask₁G ie S p).withState .started).withState .resolved) } := by
  simp only [CStore.setTaskState, CStore.subtaskResolveSt, ArenaField.modify, ArenaField.tasks,
    ArenaField.subtasks, Arena.modify]
  erw [modify_eq_set_of h.subtask, modify_eq_set_of h.task]
  rfl

theorem retSt_exit (h : CalleeAt ie ii S ys p ιe' pos S') (flat : List Flat) :
    threadStatusSt ⟨S.threads.length⟩ .exited
      (CStore.unregisterThreadSt ⟨S.tasks.length⟩ ⟨S.threads.length⟩ 1
        { S' with
          subtasks := List.set S'.subtasks S.subtasks.length (nsubRetG ii flat)
          tasks := List.set S'.tasks S.tasks.length
            (((ntask₁G ie S p).withState .started).withState .resolved) }) =
      retStG ie ii S p ιe' flat S' := by
  have h₁ : ({ S' with
      subtasks := List.set S'.subtasks S.subtasks.length (nsubRetG ii flat)
      tasks := List.set S'.tasks S.tasks.length
        (((ntask₁G ie S p).withState .started).withState .resolved) } : CStore (E3 P)).task?
      ⟨S.tasks.length⟩ = some (((ntask₁G ie S p).withState .started).withState .resolved) :=
    List.getElem?_set_self (lt_of_getElem? h.task)
  unfold CStore.unregisterThreadSt
  rw [h₁]
  simp only [threadStatusSt, ArenaField.modify, ArenaField.tasks, ArenaField.threads,
    ArenaField.insts, Arena.modify]
  erw [modify_set_self, modify_eq_set_of h.inst, modify_eq_set_of h.thread]
  rfl

theorem retStoreG_deliver (h : CalleeAt ie ii S ys p ιe' pos S') (flat : List Flat) :
    CStore.deliverResolveSt ⟨S.subtasks.length⟩
        (LowerSt.setOnCancelSt ⟨S.subtasks.length⟩ (.task ⟨S.tasks.length⟩)
          (retStG ie ii S p ιe' flat S')) =
      retStoreG S' S ie (InstState.removeThread 1 ιe') (nrecG ie ii S ys p pos flat) := by
  have hlen := lt_of_getElem? h.subtask
  have h₁ : (LowerSt.setOnCancelSt ⟨S.subtasks.length⟩ (.task ⟨S.tasks.length⟩)
      (retStG ie ii S p ιe' flat S')).subtask? ⟨S.subtasks.length⟩ =
      some { nsubRetG ii flat with onCancel := .task ⟨S.tasks.length⟩ } := by
    show ((List.set S'.subtasks S.subtasks.length (nsubRetG ii flat)).modify S.subtasks.length
      _)[S.subtasks.length]? = _
    rw [modify_set_self]
    exact List.getElem?_set_self hlen
  unfold CStore.deliverResolveSt
  rw [h₁]
  simp only [LowerSt.setOnCancelSt, retStG, ArenaField.modify,
    ArenaField.subtasks, Arena.modify]
  erw [modify_set_self, modify_set_self]
  rfl

/-- At `M₁.store` with its core store replaced, `retStoreG` is `nstore` of the records. -/
theorem retStoreG_self (ie ii : Nat) (S : CStore (E3 P)) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) (ιe' ι : InstState) (pos : Nat)
    (flat : List Flat) :
    retStoreG (nstoreCoreG ie ii S ys p ιe' pos) S ie ι (nrecG ie ii S ys p pos flat) =
      nstore S (nrecG ie ii S ys p pos flat).sub (nrecG ie ii S ys p pos flat).caller
        (nrecG ie ii S ys p pos flat).task (nrecG ie ii S ys p pos flat).thread
        (S.insts.set ie ι) := by
  rw [nstoreCore_eqG]
  simp only [retStoreG, nstore, Arena.set, set_concat_length, List.set_set]
  rfl

end Stores

/-! ## The callee's thread -/

/-- **The callee's thread of a nested call, returning from an extended store**
(`lift_body_atG` with the return half from any `CalleeAt` store `S'` and continuation slots
`C'`): the first half as in `lift_body_atG`; from a return of flat values of the result types
at `S'`, the thread lowers the lifted results and exits, at `retStG`; where the lift fails, a
trap one step away, and a specification trap at the core store of `S'` and the host state of
`M₀`. -/
theorem lift_body_atX (ie ii : Nat) (M₀ : Machine.Config (E3 P) σ) (S : CStore (E3 P))
    (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy) (ws : List Silmaril.Wasm.Component.Val)
    {ιe ιe' : InstState} (a : (E3 P).FuncAddr) (R : List (Activation (E3 P) σ))
    (hie : S.insts[ie]? = some ιe) (hadd : ιe.addThread? ⟨S.threads.length⟩ = some (1, ιe'))
    (hrem : ιe'.removeThread? 1 = some (⟨S.threads.length⟩, InstState.removeThread 1 ιe'))
    (hl : S.lockdown = false)
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws)
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hmaxr : (ValTy.flatList p.results).length ≤ 1) :
    ∃ pos K' segs' tr, LRun prof (fun _ _ => false) (DI P impl)
      { M₀ with
        store := nstore S { inst := ⟨ii⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨ii⟩ ys p 0)
          (ntask₀G ie S p) (thread₁ S.tasks) S.insts
        ctl := ⟨some ⟨S.threads.length⟩,
          .prog (DI P impl (.threadBody (.liftImplicit ⟨S.tasks.length⟩ a))), []⟩ :: R } tr
      { M₀ with
        store := nstoreCoreG ie ii S ys p ιe' pos
        ctl := ⟨some ⟨S.threads.length⟩,
          .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) K',
          segs'⟩ :: R } ∧
      (∀ (S' : RefStore (E3 P)) (C' : List (Option (Activation (E3 P) σ))) (zs : List Flat)
        (us : List Silmaril.Wasm.Component.Val), CalleeAt ie ii S ys p ιe' pos S'.toCStore →
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = some us →
        ∃ tr', LRun prof (fun _ _ => false) (DI P impl)
          { M₀ with
            store := S'.toCStore
            core := S'.core
            conts := C'
            ctl := ⟨some ⟨S.threads.length⟩, .prog (K' zs), segs'⟩ :: R } tr'
          { M₀ with
            store := retStG ie ii S p ιe' (lowerArgs p.results us) S'.toCStore
            core := S'.core
            conts := C'
            ctl := R }) ∧
      (∀ (S' : RefStore (E3 P)) (C' : List (Option (Activation (E3 P) σ))) (zs : List Flat),
        CalleeAt ie ii S ys p ιe' pos S'.toCStore →
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = none →
        TrapsNextD prof P impl
          { M₀ with
            store := S'.toCStore
            core := S'.core
            conts := C'
            ctl := ⟨some ⟨S.threads.length⟩, .prog (K' zs), segs'⟩ :: R } ∧
        TrapsAtSH prof P impl
          { M₀ with
            store := S'.toCStore
            core := S'.core
            conts := C'
            ctl := ⟨some ⟨S.threads.length⟩, .prog (K' zs), segs'⟩ :: R } S'.core M₀.host) := by
  obtain ⟨pos, trS, hst⟩ := runs_startL (impl := impl) (th := some ⟨S.threads.length⟩)
    (m := { M₀ with
      store := nstore S { inst := ⟨ii⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨ii⟩ ys p 0) (ntask₁G ie S p)
        ((thread₁ S.tasks).withIndex 1) (S.insts.set ie ιe') })
    (Gt := S.tasks) rfl rfl (callers_get_last rfl) (subtasks_get_last rfl) rfl hpf hys hmaxp hws
  refine ⟨pos, ?_⟩
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨?_, ?_, ?_⟩
  · apply RunsQ.chunk rfl (runs_enterG (impl := impl) (Gt := S.tasks) rfl rfl (by exact hie) hadd)
      (by exact hl)
    apply LRun.store_congr (nstore_enterG ie S _ _ p hie hadd)
    apply RunsQ.chunk rfl (runs_getObj ArenaField.tasks _ _ (tasks_get_last rfl)) (by exact hl)
    apply RunsQ.chunk rfl (hst.withCtl _) (by exact hl)
    apply RunsQ.chunk rfl (runs_lowerP p ws _ hpf (Silmaril.Wasm.Component.checkList_of_liftArgs hws)
      hmaxp _) (by exact hl)
    lstep hl
    exact .refl _
  · intro S' C' zs us hS hzs hus
    have hl' := hS.lockdown
    apply Exists.intro
    apply RunsQ.chunk2 rfl (runs_lift_someP (impl := impl) p hres hmaxr hrf hzs hus _ _).choose_spec
      (by exact hl')
    apply RunsQ.chunk2 rfl (by exact (runs_returnI (impl := impl) (T := ⟨S.tasks.length⟩)
        (by exact hS.task) rfl rfl rfl (by exact hS.caller) (by exact hS.subtask) rfl hres hrf
        (Silmaril.Wasm.Component.checkList_of_liftArgs hus) hmaxr).choose_spec) (by exact hl')
    apply LRun.store_congr (retSt_resolve hS _)
    apply RunsQ.chunk rfl (runs_exitI (impl := impl) (T := ⟨S.tasks.length⟩)
      (H := ⟨S.threads.length⟩) (by exact List.getElem?_set_self (lt_of_getElem? hS.task)) rfl rfl rfl
      (by exact hS.thread) rfl (by exact hS.inst) hrem) (by exact hl')
    lstep ((CStore.unregisterThreadSt_frame (E := E3 P) _ _ _ _).2.2.2.2.2.2.1.trans hl')
    exact lrun_refl_store (retSt_exit hS _)
  · intro S' C' zs hS hzs hn
    exact ⟨lrun_lift_trapP p hres hmaxr hrf hzs hn rfl (by exact hS.lockdown),
      lrun_lift_trapAtSH p hres hmaxr hrf hzs hn rfl (by exact hS.lockdown)⟩

/-! ## The caller's side -/

/-- **The caller's side of a nested call, resumed from an extended store** (`nest_preG` with the
return half from the store `retStG … S'` of a `CalleeAt` store `S'` and any continuation slots
`C'`): the callout program delivers the results and the caller's core activation resumes at
`retStoreG S' …`, with the slots `C'`. -/
theorem nest_preX (ie ii : Nat) (M : Machine.Config (E3 P) σ) (hl : M.store.lockdown = false)
    (ιe' : InstState) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (x : CoreSt (E3 P)) (f : FuncId) (a : (E3 P).FuncAddr)
    (p : Silmaril.Wasm.Component.FuncTy) (ys : List Flat) (ιi : InstState)
    (hs : (E3 P).status x.1 x.2 = .callout (.lowered f (witFt p) {} ⟨ii⟩) ys)
    (hentry : calloutEntry M.store th (.lowered f (witFt p) {} ⟨ii⟩) = none)
    (hi : ArenaField.insts.get? M.store ⟨ii⟩ = some ιi) (hleave : ιi.mayLeave = true)
    (hf : ArenaField.funcs.get? M.store f = some (.lifted a (witFt p) {} ⟨ie⟩)) :
    ∃ C₁ R tr, LRun prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest x)
      tr { coreCfg M th K segs rest x with
        store := nstore M.store { inst := ⟨ii⟩ }
          (lowerRec ⟨M.store.subtasks.length⟩ ⟨ii⟩ ys p 0)
          (ntask₀G ie M.store p) (thread₁ M.store.tasks) M.store.insts
        conts := C₁
        ctl := ⟨some ⟨M.store.threads.length⟩,
          .prog (DI P impl (.threadBody (.liftImplicit ⟨M.store.tasks.length⟩ a))), []⟩ :: R } ∧
      ∀ (S' : RefStore (E3 P)) (C' : List (Option (Activation (E3 P) σ))) (pos : Nat)
        (us : List Silmaril.Wasm.Component.Val),
        CalleeAt ie ii M.store ys p ιe' pos S'.toCStore →
        ∃ tr', LRun prof (fun _ _ => false) (DI P impl)
          { coreCfg M th K segs rest x with
            store := retStG ie ii M.store p ιe' (lowerArgs p.results us) S'.toCStore
            core := S'.core
            conts := C'
            ctl := R } tr'
          (coreCfg
            { M with
              conts := C'
              store := retStoreG S'.toCStore M.store ie
                (InstState.removeThread 1 ιe')
                (nrecG ie ii M.store ys p pos (lowerArgs p.results us)) }
            th K segs rest (S'.core, (E3 P).resume S'.core x.2 (.values (lowerArgs p.results us)))) := by
  let S : CStore (E3 P) := M.store
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨?_, ?_⟩
  apply LRun.cons (m := coreCfg M th K segs rest x) ⟨List.cons_ne_nil _ _, hl⟩
    (callout_stepD rfl hs)
  apply lrun_hostCallout (m := coreCfg M th K segs rest x) hl hentry
  apply RunsQ.chunk2 rfl (runs_getObj ArenaField.insts _ _ (by exact hi)) (by exact hl)
  apply RunsQ.chunk2 rfl (runs_trapIf (by rw [hleave]; rfl) _ _) (by exact hl)
  apply RunsQ.chunk2 rfl (runs_allocObj ArenaField.subtasks _ _ rfl) (by exact hl)
  apply RunsQ.chunk2 rfl (runs_allocObj ArenaField.callers _ _ rfl) (by exact hl)
  lstep hl
  apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (by exact hf)) (by exact hl)
  apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) (by exact hl)
  apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) (by exact hl)
  apply RunsQ.chunk2 rfl (RunsQ.get (.pure _ _)) (by exact hl)
  apply RunsQ.chunk2 rfl (runs_ite_false (impl := impl) (by exact threadIs_last rfl) _ _)
    (by exact hl)
  apply LRun.prog rfl (fun _ _ e => by cases e) (by exact hl)
    (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
  apply LRun.store_congr (nstore_resumeG ie ii S ys p)
  exact .refl _
  intro S' C' pos us hS
  have hl' := hS.lockdown
  apply Exists.intro
  apply RunsQ.chunk rfl (runs_callUnit_loopI (impl := impl) (T := ⟨S.tasks.length⟩)
    (by exact List.getElem?_set_self (lt_of_getElem? hS.task)) rfl) (by exact hl')
  lstep hl'
  lstep hl'
  apply RunsQ.chunk rfl (runs_lowerTail (d := DI P impl)
    (X := { nsubRetG ii (lowerArgs p.results us) with onCancel := .task ⟨S.tasks.length⟩ })
    (by
      show ((List.set S'.subtasks S.subtasks.length (nsubRetG ii (lowerArgs p.results us))).modify
        S.subtasks.length _)[S.subtasks.length]? = _
      rw [modify_set_self]
      exact List.getElem?_set_self (lt_of_getElem? hS.subtask))
    rfl rfl) (by exact hl')
  apply LRun.store_congr (retStoreG_deliver hS _)
  repeat lstep hl'
  exact .refl _

/-! ## The whole call -/

/-- **A callout of the caller answered by the callee's `canon lift`, returning from an extended
store** (`nest_atG` with the return half from any `CalleeAt` store and continuation slots): from
the caller's core activation stopped at a callout to the trampoline (of instance `ii`) of the
callee's lifted function `f` (of instance `ie`, core address `a`, type `p`), a live
deterministic run to the callee's core activation `M₁` on the lowered arguments, at the store
`nstoreCoreG ie ii M.store ys p ιe' pos`, on the thread
`⟨M.store.threads.length⟩` of instance `ie`, nested above the parked callout, at the frame's
host state. When it returns flat values of the result types at a store `S'` keeping the
callee's records (`CalleeAt`) with continuation slots `C'`, the lifted results are lowered back
and the caller's activation resumes at `retStoreG S' …` with the slots `C'`; where the lift
fails, the machine traps one step later, with a specification trap at the core store of `S'` and
the frame's host state. -/
theorem nest_atX (ie ii : Nat) (M : Machine.Config (E3 P) σ) (hl : M.store.lockdown = false)
    (ιe ιe' : InstState) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (x : CoreSt (E3 P)) (f : FuncId) (a : (E3 P).FuncAddr)
    (p : Silmaril.Wasm.Component.FuncTy) (ys : List Flat) (ιi : InstState)
    (ws : List Silmaril.Wasm.Component.Val)
    (hs : (E3 P).status x.1 x.2 = .callout (.lowered f (witFt p) {} ⟨ii⟩) ys)
    (hentry : calloutEntry M.store th (.lowered f (witFt p) {} ⟨ii⟩) = none)
    (hi : ArenaField.insts.get? M.store ⟨ii⟩ = some ιi) (hleave : ιi.mayLeave = true)
    (hf : ArenaField.funcs.get? M.store f = some (.lifted a (witFt p) {} ⟨ie⟩))
    (hie : M.store.insts[ie]? = some ιe)
    (hadd : ιe.addThread? ⟨M.store.threads.length⟩ = some (1, ιe'))
    (hrem : ιe'.removeThread? 1 =
      some (⟨M.store.threads.length⟩, InstState.removeThread 1 ιe'))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws)
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hmaxr : (ValTy.flatList p.results).length ≤ 1) :
    ∃ (pos : Nat) (M₁ : Machine.Config (E3 P) σ)
      (K' : List Flat → Canon.P (E3 P) σ (Ret (E3 P)))
      (segs' : List (Seg (E3 P) σ)) (rest' : List (Activation (E3 P) σ)) (tr : List (Label (E3 P) σ)),
      LRun prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest x) tr M₁ ∧
      M₁.ctl = ⟨some ⟨M.store.threads.length⟩,
        .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) K',
        segs'⟩ :: rest' ∧
      M₁.store = nstoreCoreG ie ii M.store ys p ιe' pos ∧ M₁.core = x.1 ∧
      M₁.host = M.host ∧ M₁.pending = M.pending ∧ M₁.results = M.results ∧
      M₁.cancels = M.cancels ∧
      instOfThread? M₁.store (some ⟨M.store.threads.length⟩) = some ⟨ie⟩ ∧
      (∀ (S' : RefStore (E3 P)) (C' : List (Option (Activation (E3 P) σ))) (zs : List Flat)
        (us : List Silmaril.Wasm.Component.Val),
        CalleeAt ie ii M.store ys p ιe' pos S'.toCStore →
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = some us →
        ∃ tr', LRun prof (fun _ _ => false) (DI P impl)
          { M₁ with
            store := S'.toCStore
            core := S'.core
            conts := C'
            ctl := ⟨some ⟨M.store.threads.length⟩, .prog (K' zs), segs'⟩ :: rest' } tr'
          (coreCfg
            { M with
              conts := C'
              store := retStoreG S'.toCStore M.store ie
                (InstState.removeThread 1 ιe')
                (nrecG ie ii M.store ys p pos (lowerArgs p.results us)) }
            th K segs rest (S'.core, (E3 P).resume S'.core x.2 (.values (lowerArgs p.results us))))) ∧
      (∀ (S' : RefStore (E3 P)) (C' : List (Option (Activation (E3 P) σ))) (zs : List Flat),
        CalleeAt ie ii M.store ys p ιe' pos S'.toCStore →
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = none →
        TrapsNextD prof P impl
          { M₁ with
            store := S'.toCStore
            core := S'.core
            conts := C'
            ctl := ⟨some ⟨M.store.threads.length⟩, .prog (K' zs), segs'⟩ :: rest' } ∧
        TrapsAtSH prof P impl
          { M₁ with
            store := S'.toCStore
            core := S'.core
            conts := C'
            ctl := ⟨some ⟨M.store.threads.length⟩, .prog (K' zs), segs'⟩ :: rest' }
          S'.core M.host) := by
  obtain ⟨C₁, R, tr₁, h₁, hback⟩ := nest_preX (prof := prof) (impl := impl) ie ii M hl ιe' th K
    segs rest x f a p ys ιi hs hentry hi hleave hf
  obtain ⟨pos, K', segs', tr₂, h₂, hret, htrap⟩ := lift_body_atX (prof := prof) (impl := impl)
    ie ii { coreCfg M th K segs rest x with conts := C₁ } M.store ys p ws a R
    hie hadd hrem hl hpf hys hmaxp hws hres hrf hmaxr
  have hinst : instOfThread? (nstoreCoreG ie ii M.store ys p ιe' pos)
      (some ⟨M.store.threads.length⟩) = some ⟨ie⟩ := by
    rw [nstoreCore_eqG]
    have h₁ : ArenaField.threads.get? (nstore M.store
        { inst := ⟨ii⟩, state := .started }
        (lowerRec ⟨M.store.subtasks.length⟩ ⟨ii⟩ ys p pos)
        ((ntask₁G ie M.store p).withState .started)
        ((thread₁ M.store.tasks).withIndex 1) (M.store.insts.set ie ιe'))
        ⟨M.store.threads.length⟩ = some ((thread₁ M.store.tasks).withIndex 1) :=
      threads_get_last rfl
    have h₂ : ArenaField.tasks.get? (nstore M.store
        { inst := ⟨ii⟩, state := .started }
        (lowerRec ⟨M.store.subtasks.length⟩ ⟨ii⟩ ys p pos)
        ((ntask₁G ie M.store p).withState .started)
        ((thread₁ M.store.tasks).withIndex 1) (M.store.insts.set ie ιe'))
        ⟨M.store.tasks.length⟩ = some ((ntask₁G ie M.store p).withState
          .started) :=
      tasks_get_last rfl
    simp only [instOfThread?, h₁, Option.bind_eq_bind, Option.bind_some]
    erw [h₂]
    rfl
  refine ⟨pos, _, K', segs', _, _, h₁.trans h₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hinst, ?_,
    htrap⟩
  intro S' C' zs us hS hzs hus
  obtain ⟨tr₃, h₃⟩ := hret S' C' zs us hS hzs hus
  obtain ⟨tr₄, h₄⟩ := hback S' C' pos us hS
  exact ⟨_, h₃.trans h₄⟩

/-! ## The fixed-frame return is an instance -/

/-- **`nest_atG` is an instance of `nest_atX`**: its return half is the return half of
`nest_atX` at `S' = ⟨M₁.store, y.1⟩` and `C' = M₁.conts`. -/
theorem nest_atG_of_X (ie ii : Nat) (M : Machine.Config (E3 P) σ) (hl : M.store.lockdown = false)
    (ιe ιe' : InstState) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (x : CoreSt (E3 P)) (f : FuncId) (a : (E3 P).FuncAddr)
    (p : Silmaril.Wasm.Component.FuncTy) (ys : List Flat) (ιi : InstState)
    (ws : List Silmaril.Wasm.Component.Val)
    (hs : (E3 P).status x.1 x.2 = .callout (.lowered f (witFt p) {} ⟨ii⟩) ys)
    (hentry : calloutEntry M.store th (.lowered f (witFt p) {} ⟨ii⟩) = none)
    (hi : ArenaField.insts.get? M.store ⟨ii⟩ = some ιi) (hleave : ιi.mayLeave = true)
    (hf : ArenaField.funcs.get? M.store f = some (.lifted a (witFt p) {} ⟨ie⟩))
    (hie : M.store.insts[ie]? = some ιe)
    (hadd : ιe.addThread? ⟨M.store.threads.length⟩ = some (1, ιe'))
    (hrem : ιe'.removeThread? 1 =
      some (⟨M.store.threads.length⟩, InstState.removeThread 1 ιe'))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws)
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hmaxr : (ValTy.flatList p.results).length ≤ 1) :
    ∃ (pos : Nat) (C₁ : List (Option (Activation (E3 P) σ))) (M₁ : Machine.Config (E3 P) σ)
      (th' : Option ThreadId) (K' : List Flat → Canon.P (E3 P) σ (Ret (E3 P)))
      (segs' : List (Seg (E3 P) σ)) (rest' : List (Activation (E3 P) σ)) (tr : List (Label (E3 P) σ)),
      LRun prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest x) tr M₁ ∧
      M₁.ctl = ⟨th', .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws))
        K', segs'⟩ :: rest' ∧
      M₁.core = x.1 ∧ M₁.store.lockdown = false ∧ M₁.host = M.host ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat) (us : List Silmaril.Wasm.Component.Val),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = some us →
        ∃ tr', LRun prof (fun _ _ => false) (DI P impl) (retCfg M₁ th' K' segs' rest' y zs) tr'
          (coreCfg (retFrame M ie (InstState.removeThread 1 ιe')
            (nrecG ie ii M.store ys p pos (lowerArgs p.results us)) C₁)
            th K segs rest (y.1, (E3 P).resume y.1 x.2 (.values (lowerArgs p.results us))))) ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = none →
        TrapsNextD prof P impl (retCfg M₁ th' K' segs' rest' y zs) ∧
        TrapsAtSH prof P impl (retCfg M₁ th' K' segs' rest' y zs) y.1 M.host) := by
  obtain ⟨pos, M₁, K', segs', rest', tr, h₁, hc, hst, hcore, hh, -, -, -, -, hret, htrap⟩ :=
    nest_atX (prof := prof) (impl := impl) ie ii M hl ιe ιe' th K segs rest x f a p ys ιi ws hs
      hentry hi hleave hf hie hadd hrem hpf hys hmaxp hws hres hrf hmaxr
  have hS : CalleeAt ie ii M.store ys p ιe' pos (nstoreCoreG ie ii M.store ys p ιe' pos) :=
    calleeAt_self ie ii _ ys p pos (lt_of_getElem? hie) hl
  have hR : ∀ (y : CoreSt (E3 P)) (zs : List Flat),
      retCfg M₁ (some ⟨M.store.threads.length⟩) K' segs' rest' y zs =
        { M₁ with
          store := nstoreCoreG ie ii M.store ys p ιe' pos
          core := y.1
          conts := M₁.conts
          ctl := ⟨some ⟨M.store.threads.length⟩, .prog (K' zs), segs'⟩ :: rest' } := by
    intro y zs
    unfold retCfg
    rw [hst]
  refine ⟨pos, M₁.conts, M₁, _, K', segs', rest', tr, h₁, hc, hcore,
    by rw [hst, nstoreCore_eqG]; exact hl, hh, ?_, ?_⟩
  · intro y zs us hzs hus
    obtain ⟨tr', h⟩ := hret ⟨nstoreCoreG ie ii M.store ys p ιe' pos, y.1⟩ M₁.conts zs us hS hzs
      hus
    rw [retStoreG_self] at h
    exact ⟨tr', by rw [hR]; exact h⟩
  · intro y zs hzs hn
    rw [hR]
    exact htrap ⟨nstoreCoreG ie ii M.store ys p ιe' pos, y.1⟩ M₁.conts zs hS hzs hn

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
