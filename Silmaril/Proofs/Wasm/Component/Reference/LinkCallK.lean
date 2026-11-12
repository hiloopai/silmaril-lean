module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkCall
public import Silmaril.Proofs.Wasm.Component.Reference.CallKI
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The top-level call of a linked component between other calls

`readyCfgL`: the configuration of `Linked2.toRef` between top-level calls: three component
instances (the exporter's state `ιe` at index `1`, the importer's `ιi` at index `2`), the
leftovers `G` of earlier calls (`Garb`: their tasks, threads, caller records, saved
continuations, pending calls, resolutions and `on_cancel`s) and the subtasks `ST` of their nested
calls. `afterLink` is `readyCfgL` with no leftovers (`afterLink_ready`).

`call_atLK`: from `readyCfgL`, the host's invocation of the importer's lifted export, as
top-level call `k`, runs deterministically to its core activation in instance `2` (`CallAtLK`),
in a frame for `lsegs_inv` (`LFrame`); from every extension `extN M₀ ιe' N C` of the frame by
nested calls, a return of flat values of the result types resolves the call at the next
configuration between calls (`nextGarbL`: the call's task, thread and caller record after the
leftovers, the nested calls' records after them) or traps where the lift fails. The importer's
records are no longer first in their arenas: the head lemmas of `LinkCall` are restated with
records on both sides (`runs_returnM`, `runs_exitM`, `runs_callUnit_loopM`).
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

/-! ## Configurations between linked calls -/

/-- The store between linked calls: the exporter's instance state `ιe`, the importer's `ιi`, the
leftovers `G` and the subtasks `ST` of earlier nested calls. -/
def readyStoreL (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) : CStore (E3 P) :=
  { core := cs, insts := [{}, ιe, ιi], funcs := fs, tasks := G.tasks, threads := G.threads,
    callers := G.callers, subtasks := ST }

/-- The configuration between linked calls, in host state `h`. -/
def readyCfgL (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) (h : σ) :
    Machine.Config (E3 P) σ :=
  { store := readyStoreL cs ιe ιi fs G ST, host := h, conts := G.conts, pending := G.pending,
    results := G.results, cancels := G.cancels }

/-- The configuration after the host invoked function `j` on `args` as call `k`. -/
def invokedAtL (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) (h : σ) (k j : Nat)
    (args : List Silmaril.Wasm.Component.Reference.Val) : Machine.Config (E3 P) σ :=
  { readyCfgL cs ιe ιi fs G ST h with
    pending := G.pending ++ [(⟨k⟩, ⟨j⟩, args)]
    ctl := [.ofProg none (StepDefs.invokeProg ⟨k⟩ ⟨j⟩ args)] }

/-- No leftovers. -/
def Garb.empty : Garb P σ := ⟨[], [], [], [], [], [], []⟩

theorem after3_ready (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) (h : σ) :
    after3 P cs fs h = readyCfgL cs {} {} fs Garb.empty [] h := rfl

theorem invoked3_eq (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) (h : σ) (j : Nat) (args : List Silmaril.Wasm.Component.Reference.Val) :
    invoked3 P cs fs h j args = invokedAtL cs {} {} fs Garb.empty [] h 0 j args := rfl

/-- The host invocation from a configuration between linked calls. -/
theorem invoke_invL {cs : (core3P P).Store (CanonHost (core3P P))} {ιe ιi : InstState}
    {fs : List (CFuncInst (core3P P))} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k j : Nat}
    {args : List Silmaril.Wasm.Component.Reference.Val} {m : Machine.Config (E3 P) σ}
    (h : Step prof (fun _ _ => false) (DI P impl) (readyCfgL cs ιe ιi fs G ST h₀)
      (.host (.invoke ⟨k⟩ ⟨j⟩ args)) m) :
    m = invokedAtL cs ιe ιi fs G ST h₀ k j args := by
  cases h
  rfl

/-- A tick between linked calls returns to the same configuration. -/
theorem ready_tickL (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) (h₀ : σ)
    (m₁ : Machine.Config (E3 P) σ)
    (hs : Step prof (fun _ _ => false) (DI P impl) (readyCfgL cs ιe ιi fs G ST h₀) (.host .tick)
      m₁) :
    ∃ trT, LRun prof (fun _ _ => false) (DI P impl) m₁ trT (readyCfgL cs ιe ιi fs G ST h₀) := by
  cases hs
  apply Exists.intro
  repeat mstep
  exact .refl _

/-! ## Arenas with records on both sides -/

theorem tasks_get_mid {s : CStore (E3 P)} {Gt R : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} (h : s.tasks = Gt ++ [y] ++ R) :
    ArenaField.tasks.get? s (⟨Gt.length⟩ : TaskId) = some y := by
  show (s.tasks)[Gt.length]? = some y
  rw [h, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem threads_get_mid {s : CStore (E3 P)} {Gth R : List Runtime.Thread} {z : Runtime.Thread}
    (h : s.threads = Gth ++ [z] ++ R) :
    ArenaField.threads.get? s (⟨Gth.length⟩ : ThreadId) = some z := by
  show (s.threads)[Gth.length]? = some z
  rw [h, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem insts_get_two {s : CStore (E3 P)} {ι₀ ιe ι : InstState} (h : s.insts = [ι₀, ιe, ι]) :
    ArenaField.insts.get? s (⟨2⟩ : InstId) = some ι := by
  show (s.insts)[2]? = some ι
  rw [h]
  rfl

theorem modify_mid {α : Type} (l r : List α) (a : α) (f : α → α) :
    (l ++ [a] ++ r).modify l.length f = l ++ [f a] ++ r := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    show (b :: (l ++ [a] ++ r)).modify (l.length + 1) f = b :: (l ++ [f a] ++ r)
    rw [List.modify_succ_cons, ih]

theorem setTaskState_mid {s : CStore (E3 P)} {Gt R : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} (h : s.tasks = Gt ++ [y] ++ R) (st : Async.TaskState) :
    CStore.setTaskState ⟨Gt.length⟩ st s = { s with tasks := Gt ++ [y.withState st] ++ R } := by
  obtain ⟨⟩ := s
  dsimp only at h
  subst h
  simp only [CStore.setTaskState, ArenaField.modify, ArenaField.tasks, Arena.modify, modify_mid]

theorem threadStatus_mid {s : CStore (E3 P)} {Gth R : List Runtime.Thread} {z : Runtime.Thread}
    (h : s.threads = Gth ++ [z] ++ R) (st : ThreadStatus) :
    threadStatusSt ⟨Gth.length⟩ st s =
      { s with threads := Gth ++ [{ z with status := st }] ++ R } := by
  obtain ⟨⟩ := s
  dsimp only at h
  subst h
  simp only [threadStatusSt, ArenaField.modify, ArenaField.threads, Arena.modify, modify_mid]

theorem unregisterThreadSt_mid {s : CStore (E3 P)} {Gt R : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} {ι₀ ιe ι : InstState} (t : ThreadId) (i : Nat)
    (ht : s.tasks = Gt ++ [y] ++ R) (hinst : y.inst = ⟨2⟩) (hi : s.insts = [ι₀, ιe, ι]) :
    CStore.unregisterThreadSt ⟨Gt.length⟩ t i s =
      { s with
        tasks := Gt ++ [{ y with threads := y.threads.erase t }] ++ R
        insts := [ι₀, ιe, InstState.removeThread i ι] } := by
  have h₁ : s.task? ⟨Gt.length⟩ = some y := tasks_get_mid ht
  unfold CStore.unregisterThreadSt
  rw [h₁]
  obtain ⟨⟩ := s
  dsimp only at ht hi ⊢
  subst ht hi
  simp only [ArenaField.modify, ArenaField.tasks, ArenaField.insts, Arena.modify, modify_mid,
    show y.inst.idx = 2 by rw [hinst]]
  rfl

theorem registerThreadSt_eq3 {s : CStore (E3 P)} {Gt : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} {Gth : List Runtime.Thread} {z : Runtime.Thread}
    {ι₀ ιe ι ι' : InstState} {i : Nat} (ht : s.tasks = Gt ++ [y]) (hinst : y.inst = ⟨2⟩)
    (hi : s.insts = [ι₀, ιe, ι]) (hadd : ι.addThread? ⟨Gth.length⟩ = some (i, ι'))
    (hth : s.threads = Gth ++ [z]) :
    CStore.registerThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ s =
      { s with
        tasks := Gt ++ [y.addThread ⟨Gth.length⟩]
        insts := [ι₀, ιe, ι']
        threads := Gth ++ [z.withIndex i] } := by
  have h₁ : s.task? ⟨Gt.length⟩ = some y := tasks_get_last ht
  have h₂ : s.inst? y.inst = some ι := by rw [hinst]; exact insts_get_two hi
  unfold CStore.registerThreadSt
  rw [h₁]
  dsimp only
  rw [h₂, Option.bind_some, hadd]
  dsimp only
  obtain ⟨⟩ := s
  dsimp only at ht hi hth ⊢
  subst ht hi hth
  simp only [ArenaField.modify, ArenaField.set, ArenaField.tasks, ArenaField.insts,
    ArenaField.threads, Arena.modify, Arena.set, modify_concat_length,
    show y.inst.idx = 2 by rw [hinst]]
  rfl

/-- The store after `enter_implicit_thread` in instance `2`. -/
theorem enter_eq3 {S : CStore (E3 P)} {Gt : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} {Gth : List Runtime.Thread} {z : Runtime.Thread}
    {ι₀ ιe ι ι' : InstState} (ht : S.tasks = Gt ++ [y]) (hinst : y.inst = ⟨2⟩)
    (hi : S.insts = [ι₀, ιe, ι]) (hadd : ι.addThread? ⟨Gth.length⟩ = some (1, ι'))
    (hth : S.threads = Gth ++ [z]) :
    CStore.registerThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩
        (CStore.setImplicitThread ⟨Gt.length⟩ ⟨Gth.length⟩ S) =
      { CStore.setImplicitThread ⟨Gt.length⟩ ⟨Gth.length⟩ S with
        tasks := Gt ++ [({ y with implicitThread := some ⟨Gth.length⟩ } :
          Runtime.Task (E3 P)).addThread ⟨Gth.length⟩]
        insts := [ι₀, ιe, ι']
        threads := Gth ++ [z.withIndex 1] } :=
  registerThreadSt_eq3 (tasks_modify_last ht _) hinst hi hadd hth

/-! ## The programs of the call with records on both sides -/

theorem runs_enter3 {th : ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {ι₀ ιe ι ι' : InstState}
    (htasks : m.store.tasks = Gt ++ [y]) (hasync : y.ft.async_ = false) (hinst : y.inst = ⟨2⟩)
    (hinsts : m.store.insts = [ι₀, ιe, ι]) (hadd : ι.addThread? th = some (1, ι')) :
    RunsQ (DI P impl) (some th) (Task.enterImplicitThread Quirks.none ⟨Gt.length⟩) m
      [.tau, .tau, .tau, .tau, .tau, .tau] true
      { m with store := (CStore.registerThreadSt ⟨Gt.length⟩ th
        (CStore.setImplicitThread ⟨Gt.length⟩ th m.store)) } := by
  have h₁ : (CStore.setImplicitThread ⟨Gt.length⟩ th m.store).tasks =
      Gt ++ [{ y with implicitThread := some th }] := tasks_modify_last htasks _
  have hi : ArenaField.insts.get? (CStore.setImplicitThread ⟨Gt.length⟩ th m.store) y.inst =
      some ι := by
    rw [hinst]
    exact insts_get_two hinsts
  unfold Task.enterImplicitThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_currentThreadId m)
  apply RunsQ.bind (runs_modifyStore _ m rfl)
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last h₁))
  apply RunsQ.bind (runs_ite_pure hasync _ true _)
  show RunsQ _ _ (Task.registerThread ⟨Gt.length⟩ th >>= fun _ => pure true) _ _ _ _
  apply RunsQ.bind (f := fun _ => pure true) (a := 1) ?_ (.pure _ _)
  rotate_left
  unfold Task.registerThread
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last h₁))
  apply RunsQ.bind (runs_getObj ArenaField.insts _ _ (by exact hi))
  rw [hadd]
  exact RunsQ.bind (runs_modifyStore _ _
    (CStore.registerThreadSt_frame (E := E3 P) _ _ _).2.2.2.2.2.2.1) (.pure _ _)
  rfl

/-- `Task.return_` of a task with records on both sides, its caller a host record. -/
theorem runs_returnM {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt R : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gc CL : List (Caller (E3 P))}
    {c : CallId} {args : List Silmaril.Wasm.Component.Reference.Val} (vs : List Silmaril.Wasm.Component.Reference.Val) (ht : m.store.tasks = Gt ++ [y] ++ R)
    (hy : y.caller = ⟨Gc.length⟩) (hst : y.state = .started) (hb : y.numBorrows = 0)
    (hc : m.store.callers = Gc ++ [.host c args 0] ++ CL) :
    RunsQ (DI P impl) th (Task.return_ ⟨Gt.length⟩ vs) m
      [.tau, .tau, .tau, .obs (.resolved c (some vs)), .tau, .tau] ()
      { m.resolve c (some vs) with
        store := CStore.setTaskState ⟨Gt.length⟩ .resolved m.store } := by
  unfold Task.return_
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_mid ht))
  apply RunsQ.bind (runs_trapIf (by rw [hst]; rfl) _ _)
  apply RunsQ.bind (runs_trapIf (by rw [hb]; rfl) _ _)
  rw [hy]
  unfold callUnit callRet perform Prog.lift
  apply RunsQ.bind (RunsQ.call (runs_onResolveSC (some vs) hc) (.pure _ _))
  exact runs_modifyStore _ _ rfl
  rfl

theorem runs_unregisterM {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt R : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gth R' : List Runtime.Thread}
    {z : Runtime.Thread} {ι ι' : InstState} {i : Nat} {t' : ThreadId}
    (ht : m.store.tasks = Gt ++ [y] ++ R) (hst : y.state = .resolved)
    (hthr : m.store.threads = Gth ++ [z] ++ R') (hidx : z.index = some i)
    (hi : ArenaField.insts.get? m.store y.inst = some ι)
    (hrem : ι.removeThread? i = some (t', ι')) :
    RunsQ (DI P impl) th (Task.unregisterThread ⟨Gt.length⟩ ⟨Gth.length⟩) m
      [.tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ i m.store } := by
  unfold Task.unregisterThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_mid ht))
  apply RunsQ.bind (runs_trapIf (by rw [hst]; simp) _ _)
  apply RunsQ.bind (runs_getObj ArenaField.threads _ _ (threads_get_mid hthr))
  rw [hidx]
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind (runs_getObj ArenaField.insts _ _ hi)
  rw [hrem]
  exact runs_modifyStore _ _ (CStore.unregisterThreadSt_frame (E := E3 P) _ _ _ _).2.2.2.2.2.2.2.1
  rfl

theorem runs_exitM {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt R : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {Gth R' : List Runtime.Thread}
    {z : Runtime.Thread} {ι ι' : InstState} {i : Nat} {t' : ThreadId}
    (ht : m.store.tasks = Gt ++ [y] ++ R) (himp : y.implicitThread = some ⟨Gth.length⟩)
    (hst : y.state = .resolved) (hasync : y.ft.async_ = false)
    (hthr : m.store.threads = Gth ++ [z] ++ R') (hidx : z.index = some i)
    (hi : ArenaField.insts.get? m.store y.inst = some ι)
    (hrem : ι.removeThread? i = some (t', ι')) :
    RunsQ (DI P impl) th (Task.exitImplicitThread ⟨Gt.length⟩) m [.tau, .tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ i m.store } := by
  have hu := runs_unregisterM (impl := impl) (th := th) ht hst hthr hidx hi hrem
  unfold Task.exitImplicitThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_mid ht))
  rw [himp]
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind hu
  exact runs_ite_false (by rw [hasync]; rfl) _ _
  rfl

theorem runs_callUnit_loopM {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt R : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)}
    (ht : m.store.tasks = Gt ++ [y] ++ R) (hst : y.state = .resolved) :
    RunsQ (DI P impl) th (callUnit (.loop (.syncLiftLoop ⟨Gt.length⟩))) m [.tau, .tau, .tau] ()
      m := by
  have hl : RunsQ (DI P impl) th (DI P impl (.loop (.syncLiftLoop ⟨Gt.length⟩))) m [.tau] .unit
      m := by
    show RunsQ _ _ (syncLiftLoopBody (fun _ _ => false) ⟨Gt.length⟩) _ _ _ _
    unfold syncLiftLoopBody
    apply RunsQ.bind (tr₂ := []) (runs_getObj ArenaField.tasks _ _ (tasks_get_mid ht))
    rw [hst]
    exact .pure _ _
  unfold callUnit callRet perform Prog.lift
  exact RunsQ.call hl (.pure _ _)

/-! ## Call `k` of the importer's export -/

/-- The importer's task of call `k`. -/
def taskK₀ (x : SimpleExport) (Gc : List (Caller (E3 P))) : Runtime.Task (E3 P) :=
  { ft := liftedFt x, opts := {}, inst := ⟨2⟩, caller := ⟨Gc.length⟩ }

/-- The importer's task once its implicit thread `t` is registered. -/
def taskK₁ (x : SimpleExport) (Gc : List (Caller (E3 P))) (t : ThreadId) : Runtime.Task (E3 P) :=
  ({ taskK₀ x Gc with implicitThread := some t } : Runtime.Task (E3 P)).addThread t

/-- The importer's task of call `k` once finished. -/
def taskK₂ (x : SimpleExport) (Gc : List (Caller (E3 P))) (t : ThreadId) : Runtime.Task (E3 P) :=
  { ((taskK₁ x Gc t).withState .started).withState .resolved with
    threads := (((taskK₁ x Gc t).withState .started).withState .resolved).threads.erase t }

/-- The store when the importer's thread of call `k` starts running. -/
def storeK₁ (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) (x : SimpleExport)
    (k : Nat) (args : List Silmaril.Wasm.Component.Reference.Val) : CStore (E3 P) :=
  { readyStoreL cs ιe ιi fs G ST with
    tasks := G.tasks ++ [taskK₀ x G.callers]
    threads := G.threads ++ [thread₁ G.tasks]
    callers := G.callers ++ [.host ⟨k⟩ args 0]
    nestingDepth := 1 }

/-- The store once the thread entered its task (instance state `ιi'`). -/
def storeK₂ (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi ιi' : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) (x : SimpleExport)
    (k : Nat) (args : List Silmaril.Wasm.Component.Reference.Val) : CStore (E3 P) :=
  { storeK₁ cs ιe ιi fs G ST x k args with
    tasks := G.tasks ++ [taskK₁ x G.callers ⟨G.threads.length⟩]
    insts := [{}, ιe, ιi']
    threads := G.threads ++ [(thread₁ G.tasks).withIndex 1] }

/-- The store when the importer's core activation starts. -/
def storeK₃ (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi ιi' : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) (x : SimpleExport)
    (k : Nat) (args : List Silmaril.Wasm.Component.Reference.Val) : CStore (E3 P) :=
  { storeK₂ cs ιe ιi ιi' fs G ST x k args with
    tasks := G.tasks ++ [(taskK₁ x G.callers ⟨G.threads.length⟩).withState .started] }

/-- The leftovers after call `k` of function `j` on `args` with results `rs`, whose nested calls
left the records `N`, with the saved-continuation slots `C`. -/
def nextGarbL (G : Garb P σ) (x : SimpleExport) (k j : Nat) (args rs : List Silmaril.Wasm.Component.Reference.Val)
    (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ))) : Garb P σ where
  tasks := G.tasks ++ [taskK₂ x G.callers ⟨G.threads.length⟩] ++ N.map (·.task)
  threads := G.threads ++ [{ (thread₁ G.tasks).withIndex 1 with status := .exited }] ++
    N.map (·.thread)
  callers := G.callers ++ [.host ⟨k⟩ args 0] ++ N.map (·.caller)
  conts := C
  pending := G.pending ++ [(⟨k⟩, ⟨j⟩, args)]
  results := G.results ++ [(⟨k⟩, some rs)]
  cancels := (⟨k⟩, .task ⟨G.tasks.length⟩) :: G.cancels.filter (·.1 != ⟨k⟩)

/-- From `mS` the call resolves at the configuration `mE`, under `DI P impl`. -/
def ResolvesAtL (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (mS mE : Machine.Config (E3 P) σ) : Prop :=
  ∃ tr mE', LRun prof (fun _ _ => false) (DI P impl) mS tr mE' ∧ mE' = mE

/-- The frame with the exporter's instance state it already has and no nested calls. -/
theorem extN_nil (B : Machine.Config (E3 P) σ) (ιe : InstState)
    (h1 : B.store.insts.set 1 ιe = B.store.insts) (hl : B.store.lockdown = false) :
    extN B ιe [] B.conts = B := by
  obtain ⟨⟨⟩⟩ := B
  simp only at h1 hl
  simp only [extN, h1, hl, List.map_nil, List.append_nil]

theorem start_of {M : Machine.Config (E3 P) σ} {ιe : InstState} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} {t : (E3 P).Thread (CanonHost (E3 P))}
    {cs : (core3P P).Store (CanonHost (core3P P))}
    (hc : M.ctl = ⟨th, .core t K, segs⟩ :: rest) (hcs : M.store.core = cs)
    (h1 : M.store.insts.set 1 ιe = M.store.insts) (hl : M.store.lockdown = false) :
    M = coreCfg (extN M ιe [] M.conts) th K segs rest (cs, t) := by
  rw [extN_nil M ιe h1 hl, ← hcs]
  exact eq_coreCfg hc

/-- The entry check of a callout of instance `2` from the importer's thread of call `k`, with
records of nested calls after the importer's. -/
theorem calloutEntry_mid {S : CStore (E3 P)} {Gt R : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} {Gth R' : List Runtime.Thread} {z : Runtime.Thread}
    (ht : S.tasks = Gt ++ [y] ++ R) (hth : S.threads = Gth ++ [z] ++ R')
    (hz : z.task = ⟨Gt.length⟩) (hy : y.inst = ⟨2⟩) (f : FuncId) (ft : WIT.FuncType Empty RtId)
    (opts : CanonOpts (E3 P)) :
    calloutEntry S (some ⟨Gth.length⟩) (.lowered f ft opts ⟨2⟩) = none := by
  have h₁ : ArenaField.threads.get? S (⟨Gth.length⟩ : ThreadId) = some z := threads_get_mid hth
  have h₂ : ArenaField.tasks.get? S z.task = some y := by
    rw [hz]
    exact tasks_get_mid ht
  have h₃ : instOfThread? S (some ⟨Gth.length⟩) = some ⟨2⟩ := by
    simp only [instOfThread?, h₁, h₂, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  simp only [calloutEntry, h₃, ↓reduceIte]

/-- The configuration `M₀` of call `k` runs the importer's core activation of export `x`
(address `a`) on the lowered values of `vs`, in a frame for `lsegs_inv`; from every extension of
it by nested calls, a return of flat values of the result types resolves the call at the next
configuration between calls, or traps, as the IR lift prescribes. -/
structure CallAtLK (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
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
    TrapsNextD prof P impl (retCfg (extN M₀ ιe' N C) th K segs rest y ys)

/-- **The deterministic parts of the importer's top-level call `k`** from a configuration
between linked calls. -/
theorem call_atLK (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (ιe ιi : InstState) (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask)
    (h₀ : σ) (k j a : Nat) (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val)
    (hff : floatFreeList x.ty.params = true)
    (hck : ValTy.checkList x.ty.params vs = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true) (hth : ThreadsOk ιi) (hleave : ιi.mayLeave = true)
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨2⟩)) :
    ∃ M₀ th K segs rest tr₁, LRun prof (fun _ _ => false) (DI P impl)
      (invokedAtL cs ιe ιi fs G ST h₀ k j (vs.map toRefVal)) tr₁ M₀ ∧
      CallAtLK prof P impl cs ιe (enterInst ιi ⟨G.threads.length⟩) fs G ST h₀ k j x a vs M₀ th
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
  apply CallAtLK.mk
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
    exact lrun_lift_trapP x.ty hres hmaxr hffr hys hn rfl rfl

end Silmaril.Proofs.Wasm.Component.Reference
