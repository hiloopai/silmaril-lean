module

public import Silmaril.Proofs.Wasm.Component.Reference.CallPath

/-!
# Configurations between export calls

`readyCfg`: the machine configuration between top-level calls of the instance of a simple
component: the host in control, the core store `cs`, the one component instance `ι`, the lifted
functions `fs`, and the tasks, threads and caller records `Gt`, `Gth`, `Gc` left by earlier
calls, with arbitrary saved-continuation slots, pending calls, results and `on_cancel`s.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {σ : Type}

/-- The specification dispatcher with no ready host waitables and the host functions `impl`:
`D P` (no host functions) and `DA P g` (answering by `g`) are instances. -/
abbrev DI (P : Profile) (impl : HostImpl (E3 P) σ) :
    Call (E3 P) → Canon.P (E3 P) σ (Ret (E3 P)) :=
  Canon.dispatch Limits.spec Quirks.none (fun _ _ => false) impl

/-- The leftovers of earlier calls. -/
structure Garb (P : Profile) (σ : Type := Unit) where
  /-- Tasks. -/
  tasks : List (Runtime.Task (E3 P))
  /-- Threads. -/
  threads : List Runtime.Thread
  /-- Caller records. -/
  callers : List (Caller (E3 P))
  /-- Saved-continuation slots. -/
  conts : List (Option (Activation (E3 P) σ))
  /-- Pending top-level calls. -/
  pending : List (CallId × FuncId × List Silmaril.Wasm.Component.Reference.Val)
  /-- Resolutions. -/
  results : List (CallId × Option (List Silmaril.Wasm.Component.Reference.Val))
  /-- `on_cancel`s. -/
  cancels : List (CallId × CancelRef)

/-- The store between calls. -/
def readyStore (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) : CStore (E3 P) :=
  { core := cs, insts := [ι], funcs := fs, tasks := G.tasks, threads := G.threads,
    callers := G.callers }

/-- The configuration between calls, with host state `h`. -/
def readyCfgH (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (h : σ) : Machine.Config (E3 P) σ :=
  { store := readyStore cs ι fs G, host := h, conts := G.conts, pending := G.pending,
    results := G.results, cancels := G.cancels }

/-- The configuration between calls. -/
abbrev readyCfg (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P) : Machine.Config (E3 P) Unit :=
  readyCfgH cs ι fs G ()

/-- The thread table of the instance is empty, or has one freed slot. -/
def ThreadsOk (ι : InstState) : Prop :=
  ι.threads = ⟨#[none], []⟩ ∨ ι.threads = ⟨#[none, none], [1]⟩

/-- The garbage is fresh for call `k`: every pending call and resolution has an id below `k`. -/
structure Garb.Fresh (G : Garb P σ) (k : Nat) : Prop where
  pending : ∀ x ∈ G.pending, x.1.idx < k
  results : ∀ x ∈ G.results, x.1.idx < k

/-- The configuration after the host invoked function `j` on `args` as call `k`. -/
def invokedAtH (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (h : σ) (k j : Nat) (args : List Silmaril.Wasm.Component.Reference.Val) :
    Machine.Config (E3 P) σ :=
  { readyCfgH cs ι fs G h with
    pending := G.pending ++ [(⟨k⟩, ⟨j⟩, args)]
    ctl := [.ofProg none (StepDefs.invokeProg ⟨k⟩ ⟨j⟩ args)] }

/-- The configuration after the host invoked function `j` on `args` as call `k`. -/
abbrev invokedAt (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P) (k j : Nat) (args : List Silmaril.Wasm.Component.Reference.Val) :
    Machine.Config (E3 P) Unit :=
  invokedAtH cs ι fs G () k j args

theorem modify_concat_length {α : Type} (l : List α) (a : α) (f : α → α) :
    (l ++ [a]).modify l.length f = l ++ [f a] := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    show (b :: (l ++ [a])).modify (l.length + 1) f = b :: (l ++ [f a])
    rw [List.modify_succ_cons, ih]

/-! ## Arenas with leftovers -/

theorem tasks_get_last {s : CStore (E3 P)} {Gt : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} (h : s.tasks = Gt ++ [y]) :
    ArenaField.tasks.get? s (⟨Gt.length⟩ : TaskId) = some y := by
  show (s.tasks)[Gt.length]? = some y
  rw [h, List.getElem?_concat_length]

theorem threads_get_last {s : CStore (E3 P)} {Gth : List Runtime.Thread} {y : Runtime.Thread}
    (h : s.threads = Gth ++ [y]) :
    ArenaField.threads.get? s (⟨Gth.length⟩ : ThreadId) = some y := by
  show (s.threads)[Gth.length]? = some y
  rw [h, List.getElem?_concat_length]

theorem callers_get_last {s : CStore (E3 P)} {Gc : List (Caller (E3 P))} {y : Caller (E3 P)}
    (h : s.callers = Gc ++ [y]) :
    ArenaField.callers.get? s (⟨Gc.length⟩ : CallerId) = some y := by
  show (s.callers)[Gc.length]? = some y
  rw [h, List.getElem?_concat_length]

theorem tasks_modify_last {s : CStore (E3 P)} {Gt : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} (h : s.tasks = Gt ++ [y]) (f : Runtime.Task (E3 P) → Runtime.Task (E3 P)) :
    (ArenaField.tasks.modify s (⟨Gt.length⟩ : TaskId) f).tasks = Gt ++ [f y] := by
  show (s.tasks).modify Gt.length f = _
  rw [h, Arena.modify, modify_concat_length]

theorem threads_modify_last {s : CStore (E3 P)} {Gth : List Runtime.Thread} {y : Runtime.Thread}
    (h : s.threads = Gth ++ [y]) (f : Runtime.Thread → Runtime.Thread) :
    (ArenaField.threads.modify s (⟨Gth.length⟩ : ThreadId) f).threads = Gth ++ [f y] := by
  show (s.threads).modify Gth.length f = _
  rw [h, Arena.modify, modify_concat_length]

theorem insts_get_zero {s : CStore (E3 P)} {ι : InstState} (h : s.insts = [ι]) :
    ArenaField.insts.get? s (⟨0⟩ : InstId) = some ι := by
  show (s.insts)[0]? = some ι
  rw [h]
  rfl

theorem threadIs_last {s : CStore (E3 P)} {Gth : List Runtime.Thread} {b : TaskId}
    (h : s.threads = Gth ++ [{ task := b }]) :
    s.threadIs Runtime.Thread.waiting ⟨Gth.length⟩ = false := by
  unfold CStore.threadIs CStore.thread?
  rw [threads_get_last h]
  rfl

theorem threadStatus_last {s : CStore (E3 P)} {Gth : List Runtime.Thread} {z : Runtime.Thread}
    (h : s.threads = Gth ++ [z]) (st : ThreadStatus) :
    threadStatusSt ⟨Gth.length⟩ st s = { s with threads := Gth ++ [{ z with status := st }] } := by
  obtain ⟨⟩ := s
  dsimp only at h
  subst h
  simp only [threadStatusSt, ArenaField.modify, ArenaField.threads, Arena.modify,
    modify_concat_length]

theorem setTaskState_last {s : CStore (E3 P)} {Gt : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} (h : s.tasks = Gt ++ [y]) (st : Async.TaskState) :
    CStore.setTaskState ⟨Gt.length⟩ st s = { s with tasks := Gt ++ [y.withState st] } := by
  obtain ⟨⟩ := s
  dsimp only at h
  subst h
  simp only [CStore.setTaskState, ArenaField.modify, ArenaField.tasks, Arena.modify,
    modify_concat_length]

/-- Replace the store of a live run's start by an equal one. -/
theorem LRun.store_congr {prof : ProfileKind} {hr : HostReady σ}
    {d : Call (E3 P) → Canon.P (E3 P) σ (Ret (E3 P))} {m M₂ : Machine.Config (E3 P) σ}
    {tr : List (Label (E3 P) σ)} {S' : CStore (E3 P)} (h : m.store = S')
    (r : LRun prof hr d { m with store := S' } tr M₂) :
    LRun prof hr d m tr M₂ := by
  obtain ⟨⟩ := m
  dsimp only at h
  subst h
  exact r

/-! ## Store updates of a call -/

/-- A task with one more thread. -/
def _root_.Silmaril.Wasm.Component.Runtime.Task.addThread (y : Runtime.Task (E3 P))
    (t : ThreadId) : Runtime.Task (E3 P) :=
  { y with threads := y.threads ++ [t] }

/-- A thread with its table index. -/
def _root_.Silmaril.Wasm.Component.Runtime.Thread.withIndex (z : Runtime.Thread) (i : Nat) :
    Runtime.Thread :=
  { z with index := some i }

theorem registerThreadSt_eq {s : CStore (E3 P)} {Gt : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} {Gth : List Runtime.Thread} {z : Runtime.Thread}
    {ι ι' : InstState} {i : Nat} (ht : s.tasks = Gt ++ [y]) (hinst : y.inst = ⟨0⟩)
    (hi : s.insts = [ι]) (hadd : ι.addThread? ⟨Gth.length⟩ = some (i, ι'))
    (hth : s.threads = Gth ++ [z]) :
    CStore.registerThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ s =
      { s with
        tasks := Gt ++ [y.addThread ⟨Gth.length⟩]
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
theorem enter_eq {S : CStore (E3 P)} {Gt : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} {Gth : List Runtime.Thread} {z : Runtime.Thread}
    {ι ι' : InstState} (ht : S.tasks = Gt ++ [y]) (hinst : y.inst = ⟨0⟩)
    (hi : S.insts = [ι]) (hadd : ι.addThread? ⟨Gth.length⟩ = some (1, ι'))
    (hth : S.threads = Gth ++ [z]) :
    CStore.registerThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩
        (CStore.setImplicitThread ⟨Gt.length⟩ ⟨Gth.length⟩ S) =
      { CStore.setImplicitThread ⟨Gt.length⟩ ⟨Gth.length⟩ S with
        tasks := Gt ++ [({ y with implicitThread := some ⟨Gth.length⟩ } : Runtime.Task (E3 P)).addThread
          ⟨Gth.length⟩]
        insts := [ι']
        threads := Gth ++ [z.withIndex 1] } :=
  registerThreadSt_eq (tasks_modify_last ht _) hinst hi hadd hth

theorem unregisterThreadSt_eq {s : CStore (E3 P)} {Gt : List (Runtime.Task (E3 P))}
    {y : Runtime.Task (E3 P)} {ι : InstState} (t : ThreadId) (i : Nat)
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
theorem hostFinish_cancel (m : Machine.Config (E3 P) σ) (Pd : List (CallId × FuncId × List Silmaril.Wasm.Component.Reference.Val))
    (c : CallId) (f : FuncId) (args : List Silmaril.Wasm.Component.Reference.Val) (cr : CancelRef)
    (hp : m.pending = Pd ++ [(c, f, args)]) :
    hostFinish (.cancel cr) [] m = ({ m with ctl := [] } : Machine.Config (E3 P) σ).setCancel c cr := by
  have hl : lastCall? m = some c := by
    unfold lastCall?
    rw [hp, List.getLast?_concat]
    rfl
  unfold hostFinish
  rw [hl]

end Silmaril.Proofs.Wasm.Component.Reference
