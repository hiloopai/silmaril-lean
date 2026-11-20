module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.TrapS

/-!
# A cross-instance `canon lower` → `canon lift` call at arbitrary instances

The nested-call lemmas of `LinkCallout` (`lift_body_at`, `nest_pre`, `nest_at`, `lift_body_trap`,
`nest_trap_args`) and of `LinkedSessionFwd.TrapS` (`lift_body_atTSH`, `nest_atTSH`,
`lift_body_trapTSH`, `nest_trap_argsTSH`) fix the callee's `canon lift` at component instance
`1`, the caller's `canon lower` at instance `2`, and the caller's frame to `extN B ιe N C`
(instances `[{}, ιe, ιi]` in `Linked2`). Here the same runs are stated for

* the callee's instance `ie` and the caller's instance `ii` as parameters (with the function id
  `f` of the lifted function and its core address `a`), and
* an arbitrary caller frame `M` whose store is not locked down (the callee's instance state
  `ιe` read at `ie`, the caller's `ιi` at `ii`).

The machine compares instance indices only through these lookups (`calloutEntry`, the
instance arena), so the proofs are those of `LinkCallout` and `TrapS` with the indices
abstracted and the lockdown flag a hypothesis; no distinctness of `ie` and `ii` is needed.

* `lift_body_atG`: the callee's thread from its first activation to its core activation on the
  lowered arguments; the return of results that lift; a trap (one step away, `TrapsNextD`, and a
  specification trap at the returned core store and the frame's host state, `TrapsAtSH`) where
  they do not lift;
* `lift_body_trapG`: the callee's thread traps (a specification trap) when the arguments do not
  lift;
* `nest_preG`: the caller's side: from the callout to the callee's first activation, and from
  the callee's exit back to the caller's resumed core activation (`retFrame`);
* `nest_atG`, `nest_trap_argsG`: the whole call, and its trapping variant.

**Instances.** `nest_at_inst`, `nest_pre_inst`, `lift_body_at_inst`, `lift_body_trap_inst`,
`nest_trap_args_inst`, `lift_body_atTSH_inst`, `lift_body_trapTSH_inst`, `nest_atTSH_inst`,
`nest_trap_argsTSH_inst` restate the fixed-index lemmas and prove them from the general ones
(at `ie = 1`, `ii = 2`, `M = extN B ιe N C`); the `TS` lemmas without the host state are
derived from the `TSH` ones in `TrapS` already.
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

/-! ## The records of a nested call at instances `ie` (callee) and `ii` (caller) -/

/-- The callee's task of a nested call from store `S` at type `p`, as allocated. -/
def ntask₀G (ie : Nat) (S : CStore (E3 P)) (p : Silmaril.Wasm.Component.FuncTy) :
    Runtime.Task (E3 P) :=
  { ft := witFt p, opts := {}, inst := ⟨ie⟩, caller := ⟨S.callers.length⟩ }

/-- The callee's task once its implicit thread is registered. -/
def ntask₁G (ie : Nat) (S : CStore (E3 P)) (p : Silmaril.Wasm.Component.FuncTy) :
    Runtime.Task (E3 P) :=
  ({ ntask₀G ie S p with implicitThread := some ⟨S.threads.length⟩ } : Runtime.Task (E3 P)).addThread
    ⟨S.threads.length⟩

/-- The store of the callee's thread once its core activation starts. -/
def nstoreCoreG (ie ii : Nat) (S : CStore (E3 P)) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) (ιe' : InstState) (pos : Nat) : CStore (E3 P) :=
  LowerSt.setCallerPosSt ⟨S.callers.length⟩ pos (LowerSt.startSt ⟨S.subtasks.length⟩
    (CStore.setTaskState ⟨S.tasks.length⟩ .started
      (nstore S { inst := ⟨ii⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨ii⟩ ys p 0) (ntask₁G ie S p)
        ((thread₁ S.tasks).withIndex 1) (S.insts.set ie ιe'))))

/-- The caller's subtask of a nested call resolved with `flat`. -/
def nsubRetG (ii : Nat) (flat : List Flat) : Subtask :=
  { inst := ⟨ii⟩, state := .returned, flatResults := flat }

/-- The callee's task of a nested call once it exited. -/
def ntaskRetG (ie : Nat) (S : CStore (E3 P)) (p : Silmaril.Wasm.Component.FuncTy) :
    Runtime.Task (E3 P) :=
  { (((ntask₁G ie S p).withState .started).withState .resolved) with
    threads := (((ntask₁G ie S p).withState .started).withState .resolved).threads.erase
      ⟨S.threads.length⟩ }

/-- The store after a nested call returned `us` at core store `cs`, before the caller's
callout program resumes. -/
def nstoreRetG (ie ii : Nat) (S : CStore (E3 P)) (_cs : (E3 P).Store (CanonHost (E3 P)))
    (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy) (ιe' : InstState) (pos : Nat)
    (us : List Silmaril.Wasm.Component.Val) : CStore (E3 P) :=
  nstore S (nsubRetG ii (lowerArgs p.results us))
    (lowerRec ⟨S.subtasks.length⟩ ⟨ii⟩ ys p pos) (ntaskRetG ie S p) (nthreadRet S)
    (S.insts.set ie (InstState.removeThread 1 ιe'))

/-- The records of a nested call that returned the flat results `flat`. -/
def nrecG (ie ii : Nat) (S : CStore (E3 P)) (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy)
    (pos : Nat) (flat : List Flat) : NRec P :=
  ⟨{ nsubRetG ii flat with onCancel := .task ⟨S.tasks.length⟩, lenders := none },
    lowerRec ⟨S.subtasks.length⟩ ⟨ii⟩ ys p pos, ntaskRetG ie S p, nthreadRet S⟩

/-- **The caller's frame after a nested call**: the records `r` appended, the callee's instance
state `ι` at `ie`, the saved-continuation slots `C`. -/
def retFrame (M : Machine.Config (E3 P) σ) (ie : Nat) (ι : InstState) (r : NRec P)
    (C : List (Option (Activation (E3 P) σ))) : Machine.Config (E3 P) σ :=
  { M with conts := C, store := nstore M.store r.sub r.caller r.task r.thread (M.store.insts.set ie ι) }

/-! ## Store equations -/

theorem nstore_resumeG (ie ii : Nat) (S : CStore (E3 P)) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) :
    threadStatusSt ⟨S.threads.length⟩ .running
        (ArenaField.threads.alloc (ArenaOps.allocSt ArenaField.tasks (ntask₀G ie S p)
          (allocSC S ⟨ii⟩ ys p)) { task := ⟨S.tasks.length⟩ }).1 =
      nstore S { inst := ⟨ii⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨ii⟩ ys p 0) (ntask₀G ie S p)
        (thread₁ S.tasks) S.insts := by
  simp [threadStatusSt, allocSC, ArenaOps.allocSt, ArenaField.alloc, Arena.alloc,
    ArenaField.modify, Arena.modify, ArenaField.threads, ArenaField.tasks, ArenaField.callers,
    ArenaField.subtasks, modify_concat_length, thread₁, nstore]

theorem nstore_enterG (ie : Nat) (S : CStore (E3 P)) (sub : Subtask) (cl : Caller (E3 P))
    (p : Silmaril.Wasm.Component.FuncTy) {ιe ιe' : InstState} (hi : S.insts[ie]? = some ιe)
    (hadd : ιe.addThread? ⟨S.threads.length⟩ = some (1, ιe')) :
    CStore.registerThreadSt ⟨S.tasks.length⟩ ⟨S.threads.length⟩
        (CStore.setImplicitThread ⟨S.tasks.length⟩ ⟨S.threads.length⟩
          (nstore S sub cl (ntask₀G ie S p) (thread₁ S.tasks) S.insts)) =
      nstore S sub cl (ntask₁G ie S p) ((thread₁ S.tasks).withIndex 1) (S.insts.set ie ιe') := by
  have h₁ : (CStore.setImplicitThread ⟨S.tasks.length⟩ ⟨S.threads.length⟩
      (nstore S sub cl (ntask₀G ie S p) (thread₁ S.tasks) S.insts)).task? ⟨S.tasks.length⟩ =
      some { ntask₀G ie S p with implicitThread := some ⟨S.threads.length⟩ } :=
    tasks_get_last (tasks_modify_last rfl _)
  have h₂ : (CStore.setImplicitThread ⟨S.tasks.length⟩ ⟨S.threads.length⟩
      (nstore S sub cl (ntask₀G ie S p) (thread₁ S.tasks) S.insts)).inst? ⟨ie⟩ = some ιe := hi
  unfold CStore.registerThreadSt
  rw [h₁]
  dsimp only
  rw [show ({ ntask₀G ie S p with implicitThread := some ⟨S.threads.length⟩ } :
    Runtime.Task (E3 P)).inst = ⟨ie⟩ from rfl, h₂, Option.bind_some, hadd]
  dsimp only
  simp [nstore, CStore.setImplicitThread, ArenaField.modify, ArenaField.set, ArenaField.tasks,
    ArenaField.insts, ArenaField.threads, Arena.modify, Arena.set, modify_concat_length, ntask₁G,
    ntask₀G, Runtime.Task.addThread, Runtime.Thread.withIndex]

theorem nstoreCore_eqG (ie ii : Nat) (S : CStore (E3 P)) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) (ιe' : InstState) (pos : Nat) :
    nstoreCoreG ie ii S ys p ιe' pos =
      nstore S { inst := ⟨ii⟩, state := .started } (lowerRec ⟨S.subtasks.length⟩ ⟨ii⟩ ys p pos)
        ((ntask₁G ie S p).withState .started) ((thread₁ S.tasks).withIndex 1)
        (S.insts.set ie ιe') := by
  simp [nstoreCoreG, nstore, LowerSt.setCallerPosSt, LowerSt.startSt, CStore.setTaskState,
    ArenaField.modify, Arena.modify, ArenaField.tasks, ArenaField.callers, ArenaField.subtasks,
    modify_concat_length, lowerRec, LowerSt.Caller.withPos]

theorem nstore_returnG (ie ii : Nat) (S : CStore (E3 P)) (_cs : (E3 P).Store (CanonHost (E3 P)))
    (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy) (ιe' : InstState) (pos : Nat)
    (flat : List Flat) :
    CStore.setTaskState ⟨S.tasks.length⟩ .resolved (CStore.subtaskResolveSt ⟨S.subtasks.length⟩
        .returned flat
        (nstore S { inst := ⟨ii⟩, state := .started }
          (lowerRec ⟨S.subtasks.length⟩ ⟨ii⟩ ys p pos) ((ntask₁G ie S p).withState .started)
          ((thread₁ S.tasks).withIndex 1) (S.insts.set ie ιe'))) =
      nstore S (nsubRetG ii flat) (lowerRec ⟨S.subtasks.length⟩ ⟨ii⟩ ys p pos)
        (((ntask₁G ie S p).withState .started).withState .resolved) ((thread₁ S.tasks).withIndex 1)
        (S.insts.set ie ιe') := by
  simp [nstore, CStore.subtaskResolveSt, CStore.setTaskState, ArenaField.modify, Arena.modify,
    ArenaField.tasks, ArenaField.subtasks, modify_concat_length, nsubRetG]

theorem nstore_exitG (ie : Nat) (S : CStore (E3 P)) (_cs : (E3 P).Store (CanonHost (E3 P)))
    (sub : Subtask) (cl : Caller (E3 P)) (p : Silmaril.Wasm.Component.FuncTy) (ιe' : InstState) :
    threadStatusSt ⟨S.threads.length⟩ .exited
      (CStore.unregisterThreadSt ⟨S.tasks.length⟩ ⟨S.threads.length⟩ 1
        (nstore S sub cl
          (((ntask₁G ie S p).withState .started).withState .resolved)
          ((thread₁ S.tasks).withIndex 1) (S.insts.set ie ιe'))) =
      nstore S sub cl (ntaskRetG ie S p) (nthreadRet S)
        (S.insts.set ie (InstState.removeThread 1 ιe')) := by
  have h₁ : (nstore S sub cl
      (((ntask₁G ie S p).withState .started).withState .resolved) ((thread₁ S.tasks).withIndex 1)
      (S.insts.set ie ιe')).task? ⟨S.tasks.length⟩ =
      some (((ntask₁G ie S p).withState .started).withState .resolved) := tasks_get_last rfl
  unfold CStore.unregisterThreadSt
  rw [h₁]
  simp [nstore, threadStatusSt, ArenaField.modify, Arena.modify, ArenaField.tasks,
    ArenaField.threads, ArenaField.insts, modify_concat_length, ntaskRetG, nthreadRet]
  exact modify_set_self _ _ _ _

/-! ## The callee's thread -/

/-- **The callee's thread of a nested call** (`lift_body_at`, `lift_body_atTSH` at instances
`ie`, `ii`): from its first activation, a live run to its core activation on the lowered
arguments; when the core activation returns flat values of the result types, the thread lowers
the lifted results into the callout's subtask and exits, or traps where the lift fails (one
step away, and a specification trap at the returned core store and the host state of `M₀`). -/
theorem lift_body_atG (ie ii : Nat) (M₀ : Machine.Config (E3 P) σ) (S : CStore (E3 P))
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
      (∀ (y : CoreSt (E3 P)) (zs : List Flat) (us : List Silmaril.Wasm.Component.Val),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = some us →
        ∃ tr', LRun prof (fun _ _ => false) (DI P impl)
          (retCfg { M₀ with store := nstoreCoreG ie ii S ys p ιe' pos } (some ⟨S.threads.length⟩)
            K' segs' R y zs) tr'
          { M₀ with store := nstoreRetG ie ii S y.1 ys p ιe' pos us, core := y.1, ctl := R }) ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = none →
        TrapsNextD prof P impl
          (retCfg { M₀ with store := nstoreCoreG ie ii S ys p ιe' pos } (some ⟨S.threads.length⟩)
            K' segs' R y zs) ∧
        TrapsAtSH prof P impl
          (retCfg { M₀ with store := nstoreCoreG ie ii S ys p ιe' pos } (some ⟨S.threads.length⟩)
            K' segs' R y zs) y.1 M₀.host) := by
  obtain ⟨pos, trS, hst⟩ := runs_startL (impl := impl) (th := some ⟨S.threads.length⟩)
    (m := { M₀ with
      store := nstore S { inst := ⟨ii⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨ii⟩ ys p 0) (ntask₁G ie S p)
        ((thread₁ S.tasks).withIndex 1) (S.insts.set ie ιe') })
    (Gt := S.tasks) rfl rfl (callers_get_last rfl) (subtasks_get_last rfl) rfl hpf hys hmaxp hws
  have hlen : ie < S.insts.length := (List.getElem?_eq_some_iff.mp hie).1
  have hie' : (S.insts.set ie ιe')[ie]? = some ιe' := List.getElem?_set_self hlen
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
  · intro y zs us hzs hus
    apply Exists.intro
    unfold retCfg
    apply LRun.store_congr (S' := nstore S { inst := ⟨ii⟩, state := .started }
      (lowerRec ⟨S.subtasks.length⟩ ⟨ii⟩ ys p pos) ((ntask₁G ie S p).withState .started)
      ((thread₁ S.tasks).withIndex 1) (S.insts.set ie ιe')) (by rw [nstoreCore_eqG])
    apply RunsQ.chunk2 rfl (runs_lift_someP (impl := impl) p hres hmaxr hrf hzs hus _ _).choose_spec
      (by exact hl)
    apply RunsQ.chunk2 rfl (by exact (runs_returnL (impl := impl) (Gt := S.tasks) rfl rfl rfl rfl
        (callers_get_last rfl) (subtasks_get_last rfl) rfl hres hrf
        (Silmaril.Wasm.Component.checkList_of_liftArgs hus) hmaxr).choose_spec) (by exact hl)
    apply LRun.store_congr (nstore_returnG ie ii S y.1 ys p ιe' pos _)
    apply RunsQ.chunk rfl (runs_exitG (impl := impl) (Gt := S.tasks) (Gth := S.threads) rfl rfl rfl
      rfl rfl rfl (by exact hie') hrem) (by exact hl)
    lstep ((CStore.unregisterThreadSt_frame (E := E3 P) _ _ _ _).2.2.2.2.2.2.1.trans hl)
    exact lrun_refl_store (nstore_exitG ie S y.1 _ _ p ιe')
  · intro y zs hzs hn
    exact ⟨lrun_lift_trapP p hres hmaxr hrf hzs hn rfl (by exact hl),
      lrun_lift_trapAtSH p hres hmaxr hrf hzs hn rfl (by exact hl)⟩

/-- **The callee's thread traps when the callout's arguments do not lift** (`lift_body_trapTSH`
at instances `ie`, `ii`): a specification trap at the core store of `S` and the host state of
`M₀`. -/
theorem lift_body_trapG (ie ii : Nat) (M₀ : Machine.Config (E3 P) σ) (S : CStore (E3 P))
    (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy) {ιe ιe' : InstState}
    (a : (E3 P).FuncAddr) (R : List (Activation (E3 P) σ))
    (hie : S.insts[ie]? = some ιe) (hadd : ιe.addThread? ⟨S.threads.length⟩ = some (1, ιe'))
    (hl : S.lockdown = false)
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    TrapsAtSH prof P impl
      { M₀ with
        store := nstore S { inst := ⟨ii⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨ii⟩ ys p 0)
          (ntask₀G ie S p) (thread₁ S.tasks) S.insts
        ctl := ⟨some ⟨S.threads.length⟩,
          .prog (DI P impl (.threadBody (.liftImplicit ⟨S.tasks.length⟩ a))), []⟩ :: R }
      M₀.core M₀.host := by
  obtain ⟨trS, mT, hst, hcore, hhost⟩ := traps_startLTSH (impl := impl)
    (th := some ⟨S.threads.length⟩)
    (m := { M₀ with
      store := nstore S { inst := ⟨ii⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨ii⟩ ys p 0) (ntask₁G ie S p)
        ((thread₁ S.tasks).withIndex 1) (S.insts.set ie ιe') })
    (Gt := S.tasks) rfl rfl (callers_get_last rfl) (subtasks_get_last rfl) rfl hpf hys hmaxp hws
  have h₁ := RunsQ.lrun_at (prof := prof) (hr := fun _ _ => false)
    (runs_enterG (impl := impl) (Gt := S.tasks) (t := ⟨S.threads.length⟩)
      (m := { M₀ with
        store := nstore S { inst := ⟨ii⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨ii⟩ ys p 0)
          (ntask₀G ie S p) (thread₁ S.tasks) S.insts
        ctl := ⟨some ⟨S.threads.length⟩,
          .prog (DI P impl (.threadBody (.liftImplicit ⟨S.tasks.length⟩ a))), []⟩ :: R })
      rfl rfl (by exact hie) hadd) (by exact hl) _ rfl
  refine TrapsAtSH.lrun h₁ ?_
  rw [nstore_enterG ie S _ _ p hie hadd]
  refine TrapsAtSH.lrun (RunsQ.lrun_at (runs_getObj ArenaField.tasks _ _ (tasks_get_last rfl))
    (by exact hl) _ rfl) ?_
  refine TrapsQS.trapsAtSH rfl (hst.withCtl _) (by exact hl) ?_ ?_
  · exact hcore
  · exact hhost

/-! ## The caller's side -/

theorem nstore_retFrame (M : Machine.Config (E3 P) σ) (ie : Nat) (ι : InstState) (r : NRec P)
    (C : List (Option (Activation (E3 P) σ))) :
    nstore M.store r.sub r.caller r.task r.thread (M.store.insts.set ie ι) =
      (retFrame M ie ι r C).store := rfl

/-- **The caller's side of a nested call** (`nest_pre` at instances `ie`, `ii`, in any frame
`M` not locked down): from the callout of the caller's core activation to the callee's lifted
function `f`, a live run to the first activation of the callee's thread above the parked
callout (`R`); from the end of that thread, with the subtask resolved, the callout program
delivers the results and the caller's core activation resumes in `retFrame`. -/
theorem nest_preG (ie ii : Nat) (M : Machine.Config (E3 P) σ) (hl : M.store.lockdown = false)
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
      ∀ (cs : (E3 P).Store (CanonHost (E3 P))) (pos : Nat) (us : List Silmaril.Wasm.Component.Val),
        ∃ tr', LRun prof (fun _ _ => false) (DI P impl)
          { coreCfg M th K segs rest x with
            store := nstoreRetG ie ii M.store cs ys p ιe' pos us
            core := cs
            conts := C₁
            ctl := R } tr'
          (coreCfg (retFrame M ie (InstState.removeThread 1 ιe')
            (nrecG ie ii M.store ys p pos (lowerArgs p.results us)) C₁)
            th K segs rest (cs, (E3 P).resume cs x.2 (.values (lowerArgs p.results us)))) := by
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
  intro cs pos us
  apply Exists.intro
  apply RunsQ.chunk rfl (runs_callUnit_loop (impl := impl) (Gt := S.tasks) rfl rfl) (by exact hl)
  lstep hl
  lstep hl
  apply RunsQ.chunk rfl (runs_lowerTail (d := DI P impl)
    (X := { nsubRetG ii (lowerArgs p.results us) with onCancel := .task ⟨S.tasks.length⟩ })
    (subtasks_get_last (G := S.subtasks) (by
      simp only [LowerSt.setOnCancelSt, nstoreRetG, nstore, ArenaField.modify, Arena.modify,
        ArenaField.subtasks, ArenaField.size, coreCfg, modify_concat_length]
      rfl))
    rfl rfl) (by exact hl)
  apply LRun.store_congr (nstore_deliver _ _ _ _ _ _ _ rfl)
  repeat lstep hl
  exact lrun_refl_store (nstore_retFrame M ie (InstState.removeThread 1 ιe')
    (nrecG ie ii S ys p pos (lowerArgs p.results us)) _)

/-- **A callout of the caller answered by the callee's `canon lift`** (`nest_at`, `nest_atTSH`
at instances `ie`, `ii`, in any frame `M` not locked down): from the caller's core activation
stopped at a callout to the trampoline (of instance `ii`) of the callee's lifted function `f`
(of instance `ie`, core address `a`, type `p`), a live deterministic run to the callee's core
activation on the lowered arguments, nested above the parked callout, at the frame's core store
and host state; when it returns flat values of the result types, the lifted results are lowered
back and the caller's activation resumes with them in `retFrame` (the records `nrecG` appended,
the callee's thread table reset); where the lift of the results fails, the machine traps one
step later, and with a specification trap at the returned core store and the frame's host
state. -/
theorem nest_atG (ie ii : Nat) (M : Machine.Config (E3 P) σ) (hl : M.store.lockdown = false)
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
  obtain ⟨C₁, R, tr₁, h₁, hback⟩ := nest_preG (prof := prof) (impl := impl) ie ii M hl ιe' th K
    segs rest x f a p ys ιi hs hentry hi hleave hf
  obtain ⟨pos, K', segs', tr₂, h₂, hret, htrap⟩ := lift_body_atG (prof := prof) (impl := impl)
    ie ii { coreCfg M th K segs rest x with conts := C₁ } M.store ys p ws a R
    hie hadd hrem hl hpf hys hmaxp hws hres hrf hmaxr
  refine ⟨pos, C₁, _, _, K', segs', _, _, h₁.trans h₂, rfl, rfl, hl, rfl, ?_, htrap⟩
  intro y zs us hzs hus
  obtain ⟨tr₃, h₃⟩ := hret y zs us hzs hus
  obtain ⟨tr₄, h₄⟩ := hback y.1 pos us
  exact ⟨_, h₃.trans h₄⟩

/-- **A callout of the caller whose arguments do not lift traps** (`nest_trap_args`,
`nest_trap_argsTSH` at instances `ie`, `ii`, in any frame `M` not locked down): a specification
trap in the callee's `on_start`, at the core store of the callout and the frame's host state. -/
theorem nest_trap_argsG (ie ii : Nat) (M : Machine.Config (E3 P) σ)
    (hl : M.store.lockdown = false) (ιe ιe' : InstState) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (x : CoreSt (E3 P)) (f : FuncId) (a : (E3 P).FuncAddr)
    (p : Silmaril.Wasm.Component.FuncTy) (ys : List Flat) (ιi : InstState)
    (hs : (E3 P).status x.1 x.2 = .callout (.lowered f (witFt p) {} ⟨ii⟩) ys)
    (hentry : calloutEntry M.store th (.lowered f (witFt p) {} ⟨ii⟩) = none)
    (hi : ArenaField.insts.get? M.store ⟨ii⟩ = some ιi) (hleave : ιi.mayLeave = true)
    (hf : ArenaField.funcs.get? M.store f = some (.lifted a (witFt p) {} ⟨ie⟩))
    (hie : M.store.insts[ie]? = some ιe)
    (hadd : ιe.addThread? ⟨M.store.threads.length⟩ = some (1, ιe'))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    TrapsAtSH prof P impl (coreCfg M th K segs rest x) x.1 M.host := by
  obtain ⟨C₁, R, tr₁, h₁, -⟩ := nest_preG (prof := prof) (impl := impl) ie ii M hl ιe' th K segs
    rest x f a p ys ιi hs hentry hi hleave hf
  exact TrapsAtSH.lrun h₁ (lift_body_trapG (prof := prof) (impl := impl) ie ii
    { coreCfg M th K segs rest x with conts := C₁ } M.store ys p a R hie hadd
    hl hpf hys hmaxp hws)

/-- A specification trap with the host state is a trap. -/
theorem trapsFrom_of_SH {M : Machine.Config (E3 P) σ} {c : (E3 P).Store (CanonHost (E3 P))}
    {h : σ} (H : TrapsAtSH prof P impl M c h) : TrapsFrom prof P impl M := by
  obtain ⟨tr, mT, r, -, h₁, hl, hu, -, -⟩ := H
  exact ⟨tr, mT, r, h₁, hl, hu⟩


/-! ## Read-back -/

/-- **The read-back of a specification trap**: every run from `M` stops at a live configuration
on the way, or ends in the trapped configuration, at the core store `c` and host state `h`. -/
theorem trapsAtSH_back {M m' : Machine.Config (E3 P) σ} {c : (E3 P).Store (CanonHost (E3 P))}
    {h : σ} {tr : List (Label (E3 P) σ)} (H : TrapsAtSH prof P impl M c h)
    (r : Steps prof (fun _ _ => false) (DI P impl) M tr m') :
    Live m' ∨ ∃ (mT : Machine.Config (E3 P) σ) (rr : TrapReason), (∀ msg, rr ≠ .internal msg) ∧
      m' = trapCfg mT ∧ mT.core = c ∧ mT.host = h := by
  obtain ⟨tr₁, mT, rT, hr, hrun, hlive, hu, hc, hh⟩ := H
  rcases hrun.inv r with hl' | ⟨tr'', -, r''⟩
  · exact .inl hl'
  cases r'' with
  | refl => exact .inl hlive
  | cons s' r''' =>
    obtain ⟨rfl, rfl⟩ := hu.2 _ _ s'
    exact .inr ⟨mT, rT, hr, steps_of_locked rfl rfl r''', hc, hh⟩

/-- **The read-back of a nested call** (`nest_atG` with the inversion of its runs): the runs of
`nest_atG`, and every run from the caller's callout stops at a live configuration before the
callee's core activation `M₁` or continues from `M₁`; every run from a return of the callee whose
results lift stops at a live configuration or continues from the caller's resumed activation;
every run from a return whose results do not lift stops at a live configuration or ends in a
specification trap at the returned core store and the frame's host state. -/
theorem nest_backG (ie ii : Nat) (M : Machine.Config (E3 P) σ) (hl : M.store.lockdown = false)
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
      M₁ = coreCfg M₁ th' K' segs' rest'
        (x.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) ∧
      M₁.core = x.1 ∧ M₁.store.lockdown = false ∧ M₁.host = M.host ∧
      (∀ (tr₀ : List (Label (E3 P) σ)) (m' : Machine.Config (E3 P) σ),
        Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest x) tr₀ m' →
        Live m' ∨ ∃ tr₂, tr₀ = tr ++ tr₂ ∧ Steps prof (fun _ _ => false) (DI P impl) M₁ tr₂ m') ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat) (us : List Silmaril.Wasm.Component.Val),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = some us →
        ∃ tr', LRun prof (fun _ _ => false) (DI P impl) (retCfg M₁ th' K' segs' rest' y zs) tr'
          (coreCfg (retFrame M ie (InstState.removeThread 1 ιe')
            (nrecG ie ii M.store ys p pos (lowerArgs p.results us)) C₁)
            th K segs rest (y.1, (E3 P).resume y.1 x.2 (.values (lowerArgs p.results us)))) ∧
          ∀ (tr₀ : List (Label (E3 P) σ)) (m' : Machine.Config (E3 P) σ),
            Steps prof (fun _ _ => false) (DI P impl) (retCfg M₁ th' K' segs' rest' y zs) tr₀ m' →
            Live m' ∨ ∃ tr₂, tr₀ = tr' ++ tr₂ ∧ Steps prof (fun _ _ => false) (DI P impl)
              (coreCfg (retFrame M ie (InstState.removeThread 1 ιe')
                (nrecG ie ii M.store ys p pos (lowerArgs p.results us)) C₁)
                th K segs rest (y.1, (E3 P).resume y.1 x.2 (.values (lowerArgs p.results us))))
              tr₂ m') ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = none →
        ∀ (tr₀ : List (Label (E3 P) σ)) (m' : Machine.Config (E3 P) σ),
          Steps prof (fun _ _ => false) (DI P impl) (retCfg M₁ th' K' segs' rest' y zs) tr₀ m' →
          Live m' ∨ ∃ (mT : Machine.Config (E3 P) σ) (rr : TrapReason),
            (∀ msg, rr ≠ .internal msg) ∧ m' = trapCfg mT ∧ mT.core = y.1 ∧
            mT.host = M.host) := by
  obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ :=
    nest_atG (prof := prof) (impl := impl) ie ii M hl ιe ιe' th K segs rest x f a p ys ιi ws hs
      hentry hi hleave hf hie hadd hrem hpf hys hmaxp hws hres hrf hmaxr
  refine ⟨pos, C₁, M₁, th', K', segs', rest', tr, h₁, ?_, h₃, h₄, h₅,
    fun tr₀ m' r => h₁.inv r, fun y zs us hzs hus => ?_,
    fun y zs hzs hn tr₀ m' r => trapsAtSH_back (h₇ y zs hzs hn).2 r⟩
  · rw [← h₃]
    exact eq_coreCfg h₂
  · obtain ⟨tr', h⟩ := h₆ y zs us hzs hus
    exact ⟨tr', h, fun tr₀ m' r => h.inv r⟩

/-- **The read-back of a callout whose arguments do not lift**: every run from it stops at a
live configuration or ends in a specification trap at the callout's core store and the frame's
host state. -/
theorem nest_trap_args_backG (ie ii : Nat) (M : Machine.Config (E3 P) σ)
    (hl : M.store.lockdown = false) (ιe ιe' : InstState) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (x : CoreSt (E3 P)) (f : FuncId) (a : (E3 P).FuncAddr)
    (p : Silmaril.Wasm.Component.FuncTy) (ys : List Flat) (ιi : InstState)
    (hs : (E3 P).status x.1 x.2 = .callout (.lowered f (witFt p) {} ⟨ii⟩) ys)
    (hentry : calloutEntry M.store th (.lowered f (witFt p) {} ⟨ii⟩) = none)
    (hi : ArenaField.insts.get? M.store ⟨ii⟩ = some ιi) (hleave : ιi.mayLeave = true)
    (hf : ArenaField.funcs.get? M.store f = some (.lifted a (witFt p) {} ⟨ie⟩))
    (hie : M.store.insts[ie]? = some ιe)
    (hadd : ιe.addThread? ⟨M.store.threads.length⟩ = some (1, ιe'))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none)
    {tr : List (Label (E3 P) σ)} {m' : Machine.Config (E3 P) σ}
    (r : Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest x) tr m') :
    Live m' ∨ ∃ (mT : Machine.Config (E3 P) σ) (rr : TrapReason), (∀ msg, rr ≠ .internal msg) ∧
      m' = trapCfg mT ∧ mT.core = x.1 ∧ mT.host = M.host :=
  trapsAtSH_back (nest_trap_argsG (prof := prof) (impl := impl) ie ii M hl ιe ιe' th K segs rest x
    f a p ys ιi hs hentry hi hleave hf hie hadd hpf hys hmaxp hws) r

/-! ## The fixed-index lemmas are instances -/

section Inst

theorem ntask₀_eq (S : CStore (E3 P)) (p : Silmaril.Wasm.Component.FuncTy) :
    ntask₀ S p = ntask₀G 1 S p := rfl

theorem nstoreCore_eqG₁ (S : CStore (E3 P)) (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy)
    (ιe' : InstState) (pos : Nat) : nstoreCore S ys p ιe' pos = nstoreCoreG 1 2 S ys p ιe' pos :=
  rfl

theorem nstoreRet_eqG (S : CStore (E3 P)) (cs : (E3 P).Store (CanonHost (E3 P))) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) (ιe' : InstState) (pos : Nat)
    (us : List Silmaril.Wasm.Component.Val) :
    nstoreRet S cs ys p ιe' pos us = nstoreRetG 1 2 S cs ys p ιe' pos us := rfl

theorem nrec_eqG (S : CStore (E3 P)) (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy)
    (pos : Nat) (flat : List Flat) : nrec S ys p pos flat = nrecG 1 2 S ys p pos flat := rfl

theorem set_set_same {α : Type} : ∀ (l : List α) (i : Nat) (a b : α),
    (l.set i a).set i b = l.set i b
  | [], _, _, _ => rfl
  | _ :: _, 0, _, _ => rfl
  | c :: l, i + 1, a, b => congrArg (c :: ·) (set_set_same l i a b)

/-- `retFrame` of `extN` at instance `1` is `extN` with the record appended. -/
theorem retFrame_extN (B : Machine.Config (E3 P) σ) (ιe ι : InstState) (N : List (NRec P))
    (C C₁ : List (Option (Activation (E3 P) σ))) (r : NRec P) :
    retFrame (extN B ιe N C) 1 ι r C₁ = extN B ι (N ++ [r]) C₁ := by
  simp only [retFrame, extN, nstore, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc]
  congr 2
  exact set_set_same _ _ _ _

theorem extN_insts1 (B : Machine.Config (E3 P) σ) (ιe : InstState) (N : List (NRec P))
    (C : List (Option (Activation (E3 P) σ))) (hlen : 1 < B.store.insts.length) :
    (extN B ιe N C).store.insts[1]? = some ιe :=
  List.getElem?_set_self hlen

/-- `lift_body_at` is `lift_body_atG` at `ie = 1`, `ii = 2`. -/
theorem lift_body_at_inst (M₀ : Machine.Config (E3 P) σ) (S : CStore (E3 P)) (ys : List Flat)
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
        TrapsNextD prof P impl
          (retCfg { M₀ with store := nstoreCore S ys p ιe' pos } (some ⟨S.threads.length⟩) K'
            segs' R y zs)) := by
  obtain ⟨pos, K', segs', tr, h₁, h₂, h₃⟩ := lift_body_atG (prof := prof) (impl := impl) 1 2 M₀ S
    ys p ws a R hie hadd hrem hl hpf hys hmaxp hws hres hrf hmaxr
  exact ⟨pos, K', segs', tr, h₁, h₂, fun y zs hzs hn => (h₃ y zs hzs hn).1⟩

/-- `lift_body_atTSH` is `lift_body_atG` at `ie = 1`, `ii = 2`. -/
theorem lift_body_atTSH_inst (M₀ : Machine.Config (E3 P) σ) (S : CStore (E3 P)) (ys : List Flat)
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
        TrapsAtSH prof P impl
          (retCfg { M₀ with store := nstoreCore S ys p ιe' pos } (some ⟨S.threads.length⟩) K'
            segs' R y zs) y.1 M₀.host) := by
  obtain ⟨pos, K', segs', tr, h₁, h₂, h₃⟩ := lift_body_atG (prof := prof) (impl := impl) 1 2 M₀ S
    ys p ws a R hie hadd hrem hl hpf hys hmaxp hws hres hrf hmaxr
  exact ⟨pos, K', segs', tr, h₁, h₂, fun y zs hzs hn => (h₃ y zs hzs hn).2⟩

/-- `lift_body_trapTSH` is `lift_body_trapG` at `ie = 1`, `ii = 2`. -/
theorem lift_body_trapTSH_inst (M₀ : Machine.Config (E3 P) σ) (S : CStore (E3 P)) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) {ιe ιe' : InstState}
    (a : (E3 P).FuncAddr) (R : List (Activation (E3 P) σ))
    (hie : S.insts[1]? = some ιe) (hadd : ιe.addThread? ⟨S.threads.length⟩ = some (1, ιe'))
    (hl : S.lockdown = false)
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    TrapsAtSH prof P impl
      { M₀ with
        store := nstore S { inst := ⟨2⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p 0) (ntask₀ S p)
          (thread₁ S.tasks) S.insts
        ctl := ⟨some ⟨S.threads.length⟩,
          .prog (DI P impl (.threadBody (.liftImplicit ⟨S.tasks.length⟩ a))), []⟩ :: R }
      M₀.core M₀.host :=
  lift_body_trapG (prof := prof) (impl := impl) 1 2 M₀ S ys p a R hie hadd hl hpf hys hmaxp hws

/-- `lift_body_trap` is `lift_body_trapG` at `ie = 1`, `ii = 2`. -/
theorem lift_body_trap_inst (M₀ : Machine.Config (E3 P) σ) (S : CStore (E3 P)) (ys : List Flat)
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
          .prog (DI P impl (.threadBody (.liftImplicit ⟨S.tasks.length⟩ a))), []⟩ :: R } :=
  trapsFrom_of_SH (lift_body_trapG (prof := prof) (impl := impl) 1 2 M₀ S ys p a R hie hadd hl hpf
    hys hmaxp hws)

/-- `nest_pre` is `nest_preG` at `ie = 1`, `ii = 2`, `M = extN B ιe N C`. -/
theorem nest_pre_inst (B : Machine.Config (E3 P) σ) (ιe ιe' : InstState) (N : List (NRec P))
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
        store := nstore (extN B ιe N C).store { inst := ⟨2⟩ }
          (lowerRec ⟨(extN B ιe N C).store.subtasks.length⟩ ⟨2⟩ ys p 0)
          (ntask₀ (extN B ιe N C).store p)
          (thread₁ (extN B ιe N C).store.tasks) (extN B ιe N C).store.insts
        conts := C₁
        ctl := ⟨some ⟨(extN B ιe N C).store.threads.length⟩,
          .prog (DI P impl (.threadBody (.liftImplicit ⟨(extN B ιe N C).store.tasks.length⟩ a))),
          []⟩ :: R } ∧
      ∀ (cs : (E3 P).Store (CanonHost (E3 P))) (pos : Nat) (us : List Silmaril.Wasm.Component.Val),
        ∃ tr', LRun prof (fun _ _ => false) (DI P impl)
          { coreCfg (extN B ιe N C) th K segs rest x with
            store := nstoreRet (extN B ιe N C).store cs ys p ιe' pos us
            core := cs
            conts := C₁
            ctl := R } tr'
          (coreCfg (extN B (InstState.removeThread 1 ιe')
            (N ++ [nrec (extN B ιe N C).store ys p pos (lowerArgs p.results us)])
            C₁) th K segs rest (cs, (E3 P).resume cs x.2 (.values (lowerArgs p.results us)))) := by
  obtain ⟨C₁, R, tr, h₁, h₂⟩ := nest_preG (prof := prof) (impl := impl) 1 2 (extN B ιe N C) rfl
    ιe' th K segs rest x f a p ys ιi hs hentry hi hleave hf
  refine ⟨C₁, R, tr, h₁, fun cs pos us => ?_⟩
  obtain ⟨tr', h⟩ := h₂ cs pos us
  rw [retFrame_extN] at h
  exact ⟨tr', h⟩

/-- `nest_atTSH` is `nest_atG` at `ie = 1`, `ii = 2`, `M = extN B ιe N C`. -/
theorem nest_atTSH_inst (B : Machine.Config (E3 P) σ) (ιe ιe' : InstState) (N : List (NRec P))
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
      M₁.core = x.1 ∧ M₁.store.lockdown = false ∧ M₁.host = B.host ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat) (us : List Silmaril.Wasm.Component.Val),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = some us →
        ∃ tr', LRun prof (fun _ _ => false) (DI P impl) (retCfg M₁ th' K' segs' rest' y zs) tr'
          (coreCfg (extN B (InstState.removeThread 1 ιe')
            (N ++ [nrec (extN B ιe N C).store ys p pos (lowerArgs p.results us)])
            C₁) th K segs rest (y.1, (E3 P).resume y.1 x.2 (.values (lowerArgs p.results us))))) ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = none →
        TrapsAtSH prof P impl (retCfg M₁ th' K' segs' rest' y zs) y.1 B.host) := by
  obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ :=
    nest_atG (prof := prof) (impl := impl) 1 2 (extN B ιe N C) rfl ιe ιe' th K segs rest x f a p
      ys ιi ws hs hentry hi hleave hf (extN_insts1 B ιe N C hlen) hadd hrem hpf hys hmaxp hws hres
      hrf hmaxr
  refine ⟨pos, C₁, M₁, th', K', segs', rest', tr, h₁, h₂, h₃, h₄, h₅, fun y zs us hzs hus => ?_,
    fun y zs hzs hn => (h₇ y zs hzs hn).2⟩
  obtain ⟨tr', h⟩ := h₆ y zs us hzs hus
  rw [retFrame_extN] at h
  exact ⟨tr', h⟩

/-- `nest_at` is `nest_atG` at `ie = 1`, `ii = 2`, `M = extN B ιe N C`. -/
theorem nest_at_inst (B : Machine.Config (E3 P) σ) (ιe ιe' : InstState) (N : List (NRec P))
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
        TrapsNextD prof P impl (retCfg M₁ th' K' segs' rest' y zs)) := by
  obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr, h₁, h₂, h₃, h₄, -, h₆, h₇⟩ :=
    nest_atG (prof := prof) (impl := impl) 1 2 (extN B ιe N C) rfl ιe ιe' th K segs rest x f a p
      ys ιi ws hs hentry hi hleave hf (extN_insts1 B ιe N C hlen) hadd hrem hpf hys hmaxp hws hres
      hrf hmaxr
  refine ⟨pos, C₁, M₁, th', K', segs', rest', tr, h₁, h₂, h₃, h₄, fun y zs us hzs hus => ?_,
    fun y zs hzs hn => (h₇ y zs hzs hn).1⟩
  obtain ⟨tr', h⟩ := h₆ y zs us hzs hus
  rw [retFrame_extN] at h
  exact ⟨tr', h⟩

/-- `nest_trap_argsTSH` is `nest_trap_argsG` at `ie = 1`, `ii = 2`, `M = extN B ιe N C`. -/
theorem nest_trap_argsTSH_inst (B : Machine.Config (E3 P) σ) (ιe ιe' : InstState)
    (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ))) (th : Option ThreadId)
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
    TrapsAtSH prof P impl (coreCfg (extN B ιe N C) th K segs rest x) x.1 B.host :=
  nest_trap_argsG (prof := prof) (impl := impl) 1 2 (extN B ιe N C) rfl ιe ιe' th K segs rest x f
    a p ys ιi hs hentry hi hleave hf (extN_insts1 B ιe N C hlen) hadd hpf hys hmaxp hws

/-- `nest_trap_args` is `nest_trap_argsG` at `ie = 1`, `ii = 2`, `M = extN B ιe N C`. -/
theorem nest_trap_args_inst (B : Machine.Config (E3 P) σ) (ιe ιe' : InstState) (N : List (NRec P))
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
    TrapsFrom prof P impl (coreCfg (extN B ιe N C) th K segs rest x) :=
  trapsFrom_of_SH (nest_trap_argsTSH_inst (prof := prof) (impl := impl) B ιe ιe' N C th K segs rest
    x f a p ys ιi hs hentry hi hleave hf hlen hadd hpf hys hmaxp hws)

end Inst

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
