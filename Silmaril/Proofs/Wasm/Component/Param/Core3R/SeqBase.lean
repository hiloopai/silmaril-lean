module

public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Reference.MultiProgs
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Sequences of calls over `core3R P V IR`: the store between calls

Copies of `Silmaril.Proofs.Wasm.Component.Reference.MultiBase` and
`Silmaril.Proofs.Wasm.Component.Reference.MultiProgs` with `core3P P` replaced by `core3R P V IR`
(provenance: copies; proofs unchanged). `Garb` takes `V` and `IR` explicitly, and the task
update `Task.addThread` is copied as `Task.addThreadR`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower)

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

section Base

variable {P : Profile} {σ : Type}

/-- The specification dispatcher with no ready host waitables and the host functions `impl`:
`D P V IR` (no host functions) and `DA P g` (answering by `g`) are instances. -/
abbrev DI (P : Profile) (impl : HostImpl (E3 P V IR) σ) :
    Call (E3 P V IR) → Canon.P (E3 P V IR) σ (Ret (E3 P V IR)) :=
  Canon.dispatch Limits.spec Quirks.none (fun _ _ => false) impl

/-- The leftovers of earlier calls. -/
structure Garb (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (σ : Type := Unit) where
  /-- Tasks. -/
  tasks : List (Runtime.Task (E3 P V IR))
  /-- Threads. -/
  threads : List Runtime.Thread
  /-- Caller records. -/
  callers : List (Caller (E3 P V IR))
  /-- Saved-continuation slots. -/
  conts : List (Option (Activation (E3 P V IR) σ))
  /-- Pending top-level calls. -/
  pending : List (CallId × FuncId × List Silmaril.Wasm.Component.Reference.Val)
  /-- Resolutions. -/
  results : List (CallId × Option (List Silmaril.Wasm.Component.Reference.Val))
  /-- `on_cancel`s. -/
  cancels : List (CallId × CancelRef)

/-- The store between calls. -/
def readyStore (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ι : InstState)
    (fs : List (CFuncInst (core3R P V IR))) (G : Garb P V IR σ) : CStore (E3 P V IR) :=
  { core := cs, insts := [ι], funcs := fs, tasks := G.tasks, threads := G.threads,
    callers := G.callers }

/-- The configuration between calls, with host state `h`. -/
def readyCfgH (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ι : InstState)
    (fs : List (CFuncInst (core3R P V IR))) (G : Garb P V IR σ) (h : σ) : Machine.Config (E3 P V IR) σ :=
  { store := readyStore cs ι fs G, host := h, conts := G.conts, pending := G.pending,
    results := G.results, cancels := G.cancels }

/-- The configuration between calls. -/
abbrev readyCfg (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ι : InstState)
    (fs : List (CFuncInst (core3R P V IR))) (G : Garb P V IR) : Machine.Config (E3 P V IR) Unit :=
  readyCfgH cs ι fs G ()

/-- The thread table of the instance is empty, or has one freed slot. -/
def ThreadsOk (ι : InstState) : Prop :=
  ι.threads = ⟨#[none], []⟩ ∨ ι.threads = ⟨#[none, none], [1]⟩

/-- The garbage is fresh for call `k`: every pending call and resolution has an id below `k`. -/
structure Garb.Fresh (G : Garb P V IR σ) (k : Nat) : Prop where
  pending : ∀ x ∈ G.pending, x.1.idx < k
  results : ∀ x ∈ G.results, x.1.idx < k

/-- The configuration after the host invoked function `j` on `args` as call `k`. -/
def invokedAtH (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ι : InstState)
    (fs : List (CFuncInst (core3R P V IR))) (G : Garb P V IR σ) (h : σ) (k j : Nat) (args : List Silmaril.Wasm.Component.Reference.Val) :
    Machine.Config (E3 P V IR) σ :=
  { readyCfgH cs ι fs G h with
    pending := G.pending ++ [(⟨k⟩, ⟨j⟩, args)]
    ctl := [.ofProg none (StepDefs.invokeProg ⟨k⟩ ⟨j⟩ args)] }

/-- The configuration after the host invoked function `j` on `args` as call `k`. -/
abbrev invokedAt (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ι : InstState)
    (fs : List (CFuncInst (core3R P V IR))) (G : Garb P V IR) (k j : Nat) (args : List Silmaril.Wasm.Component.Reference.Val) :
    Machine.Config (E3 P V IR) Unit :=
  invokedAtH cs ι fs G () k j args

theorem modify_concat_length {α : Type} (l : List α) (a : α) (f : α → α) :
    (l ++ [a]).modify l.length f = l ++ [f a] := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    show (b :: (l ++ [a])).modify (l.length + 1) f = b :: (l ++ [f a])
    rw [List.modify_succ_cons, ih]

/-! ## Arenas with leftovers -/

theorem tasks_get_last {s : CStore (E3 P V IR)} {Gt : List (Runtime.Task (E3 P V IR))}
    {y : Runtime.Task (E3 P V IR)} (h : s.tasks = Gt ++ [y]) :
    ArenaField.tasks.get? s (⟨Gt.length⟩ : TaskId) = some y := by
  show (s.tasks)[Gt.length]? = some y
  rw [h, List.getElem?_concat_length]

theorem threads_get_last {s : CStore (E3 P V IR)} {Gth : List Runtime.Thread} {y : Runtime.Thread}
    (h : s.threads = Gth ++ [y]) :
    ArenaField.threads.get? s (⟨Gth.length⟩ : ThreadId) = some y := by
  show (s.threads)[Gth.length]? = some y
  rw [h, List.getElem?_concat_length]

theorem callers_get_last {s : CStore (E3 P V IR)} {Gc : List (Caller (E3 P V IR))} {y : Caller (E3 P V IR)}
    (h : s.callers = Gc ++ [y]) :
    ArenaField.callers.get? s (⟨Gc.length⟩ : CallerId) = some y := by
  show (s.callers)[Gc.length]? = some y
  rw [h, List.getElem?_concat_length]

theorem tasks_modify_last {s : CStore (E3 P V IR)} {Gt : List (Runtime.Task (E3 P V IR))}
    {y : Runtime.Task (E3 P V IR)} (h : s.tasks = Gt ++ [y]) (f : Runtime.Task (E3 P V IR) → Runtime.Task (E3 P V IR)) :
    (ArenaField.tasks.modify s (⟨Gt.length⟩ : TaskId) f).tasks = Gt ++ [f y] := by
  show (s.tasks).modify Gt.length f = _
  rw [h, Arena.modify, modify_concat_length]

theorem threads_modify_last {s : CStore (E3 P V IR)} {Gth : List Runtime.Thread} {y : Runtime.Thread}
    (h : s.threads = Gth ++ [y]) (f : Runtime.Thread → Runtime.Thread) :
    (ArenaField.threads.modify s (⟨Gth.length⟩ : ThreadId) f).threads = Gth ++ [f y] := by
  show (s.threads).modify Gth.length f = _
  rw [h, Arena.modify, modify_concat_length]

theorem insts_get_zero {s : CStore (E3 P V IR)} {ι : InstState} (h : s.insts = [ι]) :
    ArenaField.insts.get? s (⟨0⟩ : InstId) = some ι := by
  show (s.insts)[0]? = some ι
  rw [h]
  rfl

theorem threadIs_last {s : CStore (E3 P V IR)} {Gth : List Runtime.Thread} {b : TaskId}
    (h : s.threads = Gth ++ [{ task := b }]) :
    s.threadIs Runtime.Thread.waiting ⟨Gth.length⟩ = false := by
  unfold CStore.threadIs CStore.thread?
  rw [threads_get_last h]
  rfl

theorem threadStatus_last {s : CStore (E3 P V IR)} {Gth : List Runtime.Thread} {z : Runtime.Thread}
    (h : s.threads = Gth ++ [z]) (st : ThreadStatus) :
    threadStatusSt ⟨Gth.length⟩ st s = { s with threads := Gth ++ [{ z with status := st }] } := by
  obtain ⟨⟩ := s
  dsimp only at h
  subst h
  simp only [threadStatusSt, ArenaField.modify, ArenaField.threads, Arena.modify,
    modify_concat_length]

theorem setTaskState_last {s : CStore (E3 P V IR)} {Gt : List (Runtime.Task (E3 P V IR))}
    {y : Runtime.Task (E3 P V IR)} (h : s.tasks = Gt ++ [y]) (st : Async.TaskState) :
    CStore.setTaskState ⟨Gt.length⟩ st s = { s with tasks := Gt ++ [y.withState st] } := by
  obtain ⟨⟩ := s
  dsimp only at h
  subst h
  simp only [CStore.setTaskState, ArenaField.modify, ArenaField.tasks, Arena.modify,
    modify_concat_length]

/-- Replace the store of a live run's start by an equal one. -/
theorem LRun.store_congr {prof : ProfileKind} {hr : HostReady σ}
    {d : Call (E3 P V IR) → Canon.P (E3 P V IR) σ (Ret (E3 P V IR))} {m M₂ : Machine.Config (E3 P V IR) σ}
    {tr : List (Label (E3 P V IR) σ)} {S' : CStore (E3 P V IR)} (h : m.store = S')
    (r : LRun prof hr d { m with store := S' } tr M₂) :
    LRun prof hr d m tr M₂ := by
  obtain ⟨⟩ := m
  dsimp only at h
  subst h
  exact r

/-! ## Store updates of a call -/

/-- A task with one more thread. -/
def _root_.Silmaril.Wasm.Component.Runtime.Task.addThreadR (y : Runtime.Task (E3 P V IR))
    (t : ThreadId) : Runtime.Task (E3 P V IR) :=
  { y with threads := y.threads ++ [t] }


theorem registerThreadSt_eq {s : CStore (E3 P V IR)} {Gt : List (Runtime.Task (E3 P V IR))}
    {y : Runtime.Task (E3 P V IR)} {Gth : List Runtime.Thread} {z : Runtime.Thread}
    {ι ι' : InstState} {i : Nat} (ht : s.tasks = Gt ++ [y]) (hinst : y.inst = ⟨0⟩)
    (hi : s.insts = [ι]) (hadd : ι.addThread? ⟨Gth.length⟩ = some (i, ι'))
    (hth : s.threads = Gth ++ [z]) :
    CStore.registerThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ s =
      { s with
        tasks := Gt ++ [y.addThreadR ⟨Gth.length⟩]
        insts := [ι']
        threads := Gth ++ [z.withIndex i] } := by
  have h₁ : s.task? ⟨Gt.length⟩ = some y := tasks_get_last ht
  have h₂ : s.inst? y.inst = some ι := by rw [hinst]; exact insts_get_zero hi
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
    show y.inst.idx = 0 by rw [hinst]]
  rfl

/-- The store after `enter_implicit_thread`. -/
theorem enter_eq {S : CStore (E3 P V IR)} {Gt : List (Runtime.Task (E3 P V IR))}
    {y : Runtime.Task (E3 P V IR)} {Gth : List Runtime.Thread} {z : Runtime.Thread}
    {ι ι' : InstState} (ht : S.tasks = Gt ++ [y]) (hinst : y.inst = ⟨0⟩)
    (hi : S.insts = [ι]) (hadd : ι.addThread? ⟨Gth.length⟩ = some (1, ι'))
    (hth : S.threads = Gth ++ [z]) :
    CStore.registerThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩
        (CStore.setImplicitThread ⟨Gt.length⟩ ⟨Gth.length⟩ S) =
      { CStore.setImplicitThread ⟨Gt.length⟩ ⟨Gth.length⟩ S with
        tasks := Gt ++ [({ y with implicitThread := some ⟨Gth.length⟩ } : Runtime.Task (E3 P V IR)).addThreadR
          ⟨Gth.length⟩]
        insts := [ι']
        threads := Gth ++ [z.withIndex 1] } :=
  registerThreadSt_eq (tasks_modify_last ht _) hinst hi hadd hth

theorem unregisterThreadSt_eq {s : CStore (E3 P V IR)} {Gt : List (Runtime.Task (E3 P V IR))}
    {y : Runtime.Task (E3 P V IR)} {ι : InstState} (t : ThreadId) (i : Nat)
    (ht : s.tasks = Gt ++ [y]) (hinst : y.inst = ⟨0⟩) (hi : s.insts = [ι]) :
    CStore.unregisterThreadSt ⟨Gt.length⟩ t i s =
      { s with
        tasks := Gt ++ [{ y with threads := y.threads.erase t }]
        insts := [InstState.removeThread i ι] } := by
  have h₁ : s.task? ⟨Gt.length⟩ = some y := tasks_get_last ht
  unfold CStore.unregisterThreadSt
  rw [h₁]
  obtain ⟨⟩ := s
  dsimp only at ht hi ⊢
  subst ht hi
  simp only [ArenaField.modify, ArenaField.tasks, ArenaField.insts, Arena.modify,
    modify_concat_length, show y.inst.idx = 0 by rw [hinst]]
  rfl

/-- A host frame of call `k` returning its `on_cancel` at the bottom of the chain. -/
theorem hostFinish_cancel (m : Machine.Config (E3 P V IR) σ) (Pd : List (CallId × FuncId × List Silmaril.Wasm.Component.Reference.Val))
    (c : CallId) (f : FuncId) (args : List Silmaril.Wasm.Component.Reference.Val) (cr : CancelRef)
    (hp : m.pending = Pd ++ [(c, f, args)]) :
    hostFinish (.cancel cr) [] m = ({ m with ctl := [] } : Machine.Config (E3 P V IR) σ).setCancel c cr := by
  have hl : lastCall? m = some c := by
    unfold lastCall?
    rw [hp, List.getLast?_concat]
    rfl
  unfold hostFinish
  rw [hl]

end Base

section Progs

variable {P : Profile} {σ : Type} {impl : HostImpl (E3 P V IR) σ}

/-! ## Small programs -/

theorem RunsQ.of_tr {α : Type} {th : Option ThreadId} {p : Canon.P (E3 P V IR) σ α}
    {m m' : Machine.Config (E3 P V IR) σ} {a : α} {tr tr' : List (Label (E3 P V IR) σ)}
    (h : RunsQ (DI P impl) th p m tr a m') (e : tr = tr') : RunsQ (DI P impl) th p m tr' a m' :=
  e ▸ h


theorem runs_currentThreadId {th : ThreadId} (m : Machine.Config (E3 P V IR) σ) :
    RunsQ (DI P impl) (some th) currentThreadId m [.tau] th m :=
  .currentThread (.pure _ _)

theorem runs_modifyStore {th : Option ThreadId} (f : CStore (E3 P V IR) → CStore (E3 P V IR))
    (m : Machine.Config (E3 P V IR) σ) (hl : (f m.store).lockdown = m.store.lockdown) :
    RunsQ (DI P impl) th (modifyStore f) m [.tau] () { m with store := f m.store } :=
  .modify hl (.pure _ _)

theorem runs_ite_false {th : Option ThreadId} {b : Bool} (hb : b = false)
    (X : Canon.P (E3 P V IR) σ Unit) (m : Machine.Config (E3 P V IR) σ) :
    RunsQ (DI P impl) th (if b = true then X else pure ()) m [] () m := by
  subst hb
  exact .pure _ _

theorem runs_ite_pure {α : Type} {th : Option ThreadId} {b : Bool} (hb : b = false)
    (X : Canon.P (E3 P V IR) σ α) (a : α) (m : Machine.Config (E3 P V IR) σ) :
    RunsQ (DI P impl) th (if b = true then X else pure a) m [] a m := by
  subst hb
  exact .pure _ _

/-! ## `enter_implicit_thread` -/

theorem runs_enter {m : Machine.Config (E3 P V IR) σ} {Gt : List (Runtime.Task (E3 P V IR))}
    {y : Runtime.Task (E3 P V IR)} {t : ThreadId} {ι ι' : InstState}
    (htasks : m.store.tasks = Gt ++ [y]) (hasync : y.ft.async_ = false) (hinst : y.inst = ⟨0⟩)
    (hinsts : m.store.insts = [ι]) (hadd : ι.addThread? t = some (1, ι')) :
    RunsQ (DI P impl) (some t) (Task.enterImplicitThread Quirks.none ⟨Gt.length⟩) m
      [.tau, .tau, .tau, .tau, .tau, .tau] true
      { m with store := (CStore.registerThreadSt ⟨Gt.length⟩ t
        (CStore.setImplicitThread ⟨Gt.length⟩ t m.store)) } := by
  have h₁ : (CStore.setImplicitThread ⟨Gt.length⟩ t m.store).tasks =
      Gt ++ [{ y with implicitThread := some t }] := tasks_modify_last htasks _
  have hi : ArenaField.insts.get? (CStore.setImplicitThread ⟨Gt.length⟩ t m.store) y.inst =
      some ι := by
    rw [hinst]
    exact insts_get_zero hinsts
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
  apply RunsQ.bind (runs_getObj ArenaField.insts _ _ (by exact hi))
  rw [hadd]
  exact RunsQ.bind (runs_modifyStore _ _
    (CStore.registerThreadSt_frame (E := E3 P V IR) _ _ _).2.2.2.2.2.2.1) (.pure _ _)
  rfl

/-! ## Caller records of top-level calls -/

theorem runs_onStart {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ}
    {Gc : List (Caller (E3 P V IR))} {c : CallId} {args : List Silmaril.Wasm.Component.Reference.Val}
    (hc : m.store.callers = Gc ++ [.host c args 0]) :
    RunsQ (DI P impl) th (DI P impl (.onStart ⟨Gc.length⟩)) m [.tau, .obs (.started c)] (.vals args) m := by
  show RunsQ _ _ (callerOnStart Limits.spec Quirks.none ⟨Gc.length⟩) _ _ _ _
  unfold callerOnStart
  exact RunsQ.bind (runs_getObj ArenaField.callers _ _ (callers_get_last hc))
    (RunsQ.bind (tr₁ := [.obs (.started c)]) (.emit (.pure _ _)) (.pure _ _))

theorem runs_onResolve {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ}
    {Gc : List (Caller (E3 P V IR))} {c : CallId} {args : List Silmaril.Wasm.Component.Reference.Val} (r : Option (List Silmaril.Wasm.Component.Reference.Val))
    (hc : m.store.callers = Gc ++ [.host c args 0]) :
    RunsQ (DI P impl) th (DI P impl (.onResolve ⟨Gc.length⟩ r)) m [.tau, .obs (.resolved c r)] .unit
      (m.resolve c r) := by
  show RunsQ _ _ (callerOnResolve Limits.spec Quirks.none ⟨Gc.length⟩ r) _ _ _ _
  unfold callerOnResolve
  exact RunsQ.bind (runs_getObj ArenaField.callers _ _ (callers_get_last hc))
    (RunsQ.bind (tr₁ := [.obs (.resolved c r)]) (.emit (.pure _ _)) (.pure _ _))

/-! ## `Task.start` and `Task.return_` -/

theorem runs_start {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ}
    {Gt : List (Runtime.Task (E3 P V IR))} {y : Runtime.Task (E3 P V IR)} {Gc : List (Caller (E3 P V IR))}
    {c : CallId} {args : List Silmaril.Wasm.Component.Reference.Val} (ht : m.store.tasks = Gt ++ [y])
    (hy : y.caller = ⟨Gc.length⟩) (hc : m.store.callers = Gc ++ [.host c args 0]) :
    RunsQ (DI P impl) th (Task.start ⟨Gt.length⟩) m [.tau, .tau, .tau, .tau, .obs (.started c), .tau] args
      { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store } := by
  unfold Task.start
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  apply RunsQ.bind (runs_modifyStore _ _ rfl)
  rw [hy]
  unfold callVals callRet perform Prog.lift
  exact RunsQ.call (runs_onStart hc) (.pure _ _)
  rfl

theorem runs_trapIf {th : Option ThreadId} {b : Bool} (hb : b = false) (r : TrapReason)
    (m : Machine.Config (E3 P V IR) σ) : RunsQ (DI P impl) th (trapIf b r) m [] () m := by
  subst hb
  exact .pure _ _

theorem runs_return {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ}
    {Gt : List (Runtime.Task (E3 P V IR))} {y : Runtime.Task (E3 P V IR)} {Gc : List (Caller (E3 P V IR))}
    {c : CallId} {args : List Silmaril.Wasm.Component.Reference.Val} (vs : List Silmaril.Wasm.Component.Reference.Val) (ht : m.store.tasks = Gt ++ [y])
    (hy : y.caller = ⟨Gc.length⟩) (hst : y.state = .started) (hb : y.numBorrows = 0)
    (hc : m.store.callers = Gc ++ [.host c args 0]) :
    RunsQ (DI P impl) th (Task.return_ ⟨Gt.length⟩ vs) m
      [.tau, .tau, .tau, .obs (.resolved c (some vs)), .tau, .tau] ()
      { m.resolve c (some vs) with
        store := CStore.setTaskState ⟨Gt.length⟩ .resolved m.store } := by
  unfold Task.return_
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  apply RunsQ.bind (runs_trapIf (by rw [hst]; rfl) _ _)
  apply RunsQ.bind (runs_trapIf (by rw [hb]; rfl) _ _)
  rw [hy]
  unfold callUnit callRet perform Prog.lift
  apply RunsQ.bind (RunsQ.call (runs_onResolve (some vs) hc) (.pure _ _))
  exact runs_modifyStore _ _ rfl
  rfl

/-! ## `exit_implicit_thread` and the synchronous loop -/

theorem runs_unregister {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ}
    {Gt : List (Runtime.Task (E3 P V IR))} {y : Runtime.Task (E3 P V IR)} {Gth : List Runtime.Thread}
    {z : Runtime.Thread} {ι ι' : InstState} {i : Nat} {t' : ThreadId}
    (ht : m.store.tasks = Gt ++ [y]) (hst : y.state = .resolved)
    (hthr : m.store.threads = Gth ++ [z]) (hidx : z.index = some i) (hinst : y.inst = ⟨0⟩)
    (hinsts : m.store.insts = [ι]) (hrem : ι.removeThread? i = some (t', ι')) :
    RunsQ (DI P impl) th (Task.unregisterThread ⟨Gt.length⟩ ⟨Gth.length⟩) m [.tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ i m.store } := by
  have hi : ArenaField.insts.get? m.store y.inst = some ι := by
    rw [hinst]
    exact insts_get_zero hinsts
  unfold Task.unregisterThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  apply RunsQ.bind (runs_trapIf (by rw [hst]; simp) _ _)
  apply RunsQ.bind (runs_getObj ArenaField.threads _ _ (threads_get_last hthr))
  rw [hidx]
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind (runs_getObj ArenaField.insts _ _ hi)
  rw [hrem]
  exact runs_modifyStore _ _ (CStore.unregisterThreadSt_frame (E := E3 P V IR) _ _ _ _).2.2.2.2.2.2.2.1
  rfl

theorem runs_exit {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ}
    {Gt : List (Runtime.Task (E3 P V IR))} {y : Runtime.Task (E3 P V IR)} {Gth : List Runtime.Thread}
    {z : Runtime.Thread} {ι ι' : InstState} {i : Nat} {t' : ThreadId}
    (ht : m.store.tasks = Gt ++ [y]) (himp : y.implicitThread = some ⟨Gth.length⟩)
    (hst : y.state = .resolved) (hasync : y.ft.async_ = false)
    (hthr : m.store.threads = Gth ++ [z]) (hidx : z.index = some i) (hinst : y.inst = ⟨0⟩)
    (hinsts : m.store.insts = [ι]) (hrem : ι.removeThread? i = some (t', ι')) :
    RunsQ (DI P impl) th (Task.exitImplicitThread ⟨Gt.length⟩) m [.tau, .tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ i m.store } := by
  have hu := runs_unregister (impl := impl) (th := th) ht hst hthr hidx hinst hinsts hrem
  unfold Task.exitImplicitThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  rw [himp]
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind hu
  exact runs_ite_false (by rw [hasync]; rfl) _ _
  rfl

theorem runs_loop {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ}
    {Gt : List (Runtime.Task (E3 P V IR))} {y : Runtime.Task (E3 P V IR)}
    (ht : m.store.tasks = Gt ++ [y]) (hst : y.state = .resolved) :
    RunsQ (DI P impl) th (DI P impl (.loop (.syncLiftLoop ⟨Gt.length⟩))) m [.tau] .unit m := by
  show RunsQ _ _ (syncLiftLoopBody (fun _ _ => false) ⟨Gt.length⟩) _ _ _ _
  unfold syncLiftLoopBody
  apply RunsQ.bind (tr₂ := []) (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
  rw [hst]
  exact .pure _ _

theorem runs_callUnit_loop {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ}
    {Gt : List (Runtime.Task (E3 P V IR))} {y : Runtime.Task (E3 P V IR)}
    (ht : m.store.tasks = Gt ++ [y]) (hst : y.state = .resolved) :
    RunsQ (DI P impl) th (callUnit (.loop (.syncLiftLoop ⟨Gt.length⟩))) m [.tau, .tau, .tau] () m := by
  unfold callUnit callRet perform Prog.lift
  exact RunsQ.call (runs_loop ht hst) (.pure _ _)

end Progs

end Silmaril.Proofs.Wasm.Component.Param.Core3R
