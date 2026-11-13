module

public import Silmaril.X86.Concurrency.Bridge.Defs

/-!
# The TSO pool as a store-buffer run, and store-buffer candidates as litmus candidates: definitions

Two of the missing pieces of
`Bridge.Task.tsoRunCir` (gap 1), in the numbering of that Task's plan:

* **(4) the pool run is an `OpAx.Run`.** A run of the byte-granular TSO pool over
  `Atomic9.step` (`TsoReach atomic9Ev`) is recorded with the actions of each instruction step
  (`RunA`, built from `StepA`): an action list of the shape every branch of `stepSym` has
  (`Shape`: only fences, or one memory action), whose events are the instruction's access
  list and whose reads and writes are the real step's on the thread's view (`ActsOk`). Each
  thread's recorded actions, turned into store-buffer events (`histX`, i.e. `traceX` of the thread's
  trace `poolTraces`), form a program `poolProg` that the store-buffer machine runs to the
  pool's final state (`opRun_of_runA` in `PoolRun/Thms.lean`). Any `TsoReach` run is a
  `RunA` run when every reachable step has such actions (`runA_of_reach`).
* **(6) Store-buffer candidates are litmus candidates.** A TSO-consistent candidate that
  `OpAx.Explains` a run of `trs.mapIdx traceX` (the units: positions `2k`, no
  `lfence`/`sfence` units) gives a
  well-formed TSO candidate over the units of `trs` (`Litmus.units`: consecutive positions,
  every fence a unit), so a final state of `AxReach` (`axReach_of_explains`). The side
  conditions: the actions have the sizes and `locked` tags both encodings agree on (`TracesOk`),
  no access is split into bytes (`NoTear`), and the initial memory of the run agrees with the
  test's on every byte a thread reads (`InitReads`).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Bridge.PoolRun

open Silmaril.X86 (State)
open Silmaril.Process (Memory)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (SeqStep Act)
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace Test actX accUnits tearAcc)
open Silmaril.X86.Pool (TPool TsoFlush overlay syncs storeEntries atomic9Ev)
open Silmaril.X86.Concurrency.Bridge (ActsOk)

/-! ## (4) Recorded pool runs -/

/-- **The shape of one instruction's actions**: every action is a fence that reads and writes
nothing, or there is exactly one action, a non-empty memory access (a plain load or store being
unlocked) whose byte lists have the access's size. Every branch of `stepSym` has this
shape (`stepSym_shape`). -/
def Shape (acts : List XAct) : Prop :=
  (∀ a ∈ acts, (∃ k, a.ev.kind = .fence k) ∧ a.rd = [] ∧ a.wr = []) ∨
  ∃ a, acts = [a] ∧ (∀ k, a.ev.kind ≠ .fence k) ∧
    (a.ev.kind = .load → a.ev.locked = false) ∧ (a.ev.kind = .store → a.ev.locked = false) ∧
    0 < a.ev.size ∧
    (a.ev.kind.reads = true → a.rd.length = a.ev.size) ∧
    (a.ev.kind.writes = true → a.wr.length = a.ev.size)

/-- **The actions of one real step**: of the right shape, with the instruction's access
list as events, the memory before the step answering the reads and the writes giving the memory
after it (`ActsOk`). -/
def StepActs (acts : List XAct) (i : Atomic9.Instr) (c : State) (n : Nat) (q : SeqStep) : Prop :=
  Shape acts ∧ acts.map Act.ev = MemEvent.atomic9Accesses i c n ∧ ActsOk acts q

/-- One observed instruction step of a pool thread: the core before it, its actions, and the
thread's view before it, the core after it and the view after it. -/
structure Obs where
  pre : State
  acts : List XAct
  q : SeqStep

/-- **One TSO instruction step with its actions**: `TsoStep atomic9Ev`, recording the step on
the thread's view (for a synchronising step the buffer is empty, so the view is memory). -/
inductive StepA (Fin : Nat → State → Prop) : TPool Nat → Nat → Obs → TPool Nat → Prop
  | sync {p : TPool Nat} {t : Nat} {c c' : State} {i : Atomic9.Instr} {n : Nat} {mem' : Memory}
      {acts : List XAct} (ht : p.threads t = some c) (hnf : ¬ Fin t c)
      (hf : atomic9Ev.fetch (overlay p.memory (p.buffer t)) c.rip.toNat = some (i, n))
      (hs : syncs (atomic9Ev.accesses i c n) = true) (he : p.buffer t = [])
      (hx : atomic9Ev.exec i c p.memory n = .ok c' mem')
      (ha : StepActs acts i c n ⟨p.memory, c', mem'⟩) :
      StepA Fin p t ⟨c, acts, ⟨p.memory, c', mem'⟩⟩
        { p with threads := Function.update p.threads t (some c'), memory := mem' }
  | buffered {p : TPool Nat} {t : Nat} {c c' : State} {i : Atomic9.Instr} {n : Nat}
      {view' : Memory} {acts : List XAct} (ht : p.threads t = some c) (hnf : ¬ Fin t c)
      (hf : atomic9Ev.fetch (overlay p.memory (p.buffer t)) c.rip.toNat = some (i, n))
      (hs : syncs (atomic9Ev.accesses i c n) = false)
      (hx : atomic9Ev.exec i c (overlay p.memory (p.buffer t)) n = .ok c' view')
      (ha : StepActs acts i c n ⟨overlay p.memory (p.buffer t), c', view'⟩) :
      StepA Fin p t ⟨c, acts, ⟨overlay p.memory (p.buffer t), c', view'⟩⟩
        { p with
          threads := Function.update p.threads t (some c'),
          buffer := Function.update p.buffer t
            (p.buffer t ++ storeEntries (atomic9Ev.accesses i c n) view') }

/-- **A recorded TSO pool run** from `p₀`: instruction steps with their actions (appended to
the thread's history `H t`, oldest first) and flushes. -/
inductive RunA (Fin : Nat → State → Prop) (p₀ : TPool Nat) :
    (Nat → List Obs) → TPool Nat → Prop
  | refl : RunA Fin p₀ (fun _ => []) p₀
  | step {H : Nat → List Obs} {p : TPool Nat} {t : Nat} {o : Obs} {p' : TPool Nat}
      (h : RunA Fin p₀ H p) (hs : StepA Fin p t o p') :
      RunA Fin p₀ (Function.update H t (H t ++ [o])) p'
  | flush {H : Nat → List Obs} {p p' : TPool Nat} (h : RunA Fin p₀ H p) (hf : TsoFlush p p') :
      RunA Fin p₀ H p'

/-- The store-buffer events of thread `k`'s recorded steps. -/
def histX (k : Nat) (os : List Obs) : List (Silmaril.X86.MemoryModel.Tso.XEvent Nat) :=
  (os.flatMap Obs.acts).flatMap (actX k)

/-- The trace of a thread's recorded steps, ending at core `fin`. -/
def Obs.trace (os : List Obs) (fin : State) : XTrace :=
  ⟨os.map fun o => ⟨o.acts, o.q.post⟩, fin⟩

/-- The traces of threads `0, …, N - 1` (final cores `fin k`). -/
def poolTraces (N : Nat) (H : Nat → List Obs) (fin : Nat → State) : List XTrace :=
  (List.range N).map fun k => Obs.trace (H k) (fin k)

/-- **The store-buffer program of a recorded run**: thread `k < N` runs the events of its history.
-/
def poolProg (N : Nat) (H : Nat → List Obs) : List (List (Silmaril.X86.MemoryModel.Tso.XEvent Nat)) :=
  (List.range N).map fun k => histX k (H k)

/-- **A thread's history is a run of the thread** from core `c` to core `c'`: each step starts
at the previous core and is an `Atomic9.step` on its view, with actions as `StepActs` says. -/
inductive Chain : State → List Obs → State → Prop
  | nil (c : State) : Chain c [] c
  | cons {c : State} {o : Obs} {os : List Obs} {c' : State} (hpre : o.pre = c)
      (hs : Atomic9.step ⟨c, o.q.pre⟩ = some ⟨o.q.post, o.q.mem⟩)
      (ha : ∃ i n, MemEvent.atomic9Fetch o.q.pre c.rip.toNat = some (i, n) ∧
        StepActs o.acts i c n o.q)
      (tl : Chain o.q.post os c') : Chain c (o :: os) c'

/-! ## (6) From store-buffer candidates to litmus candidates -/

/-- **An action both encodings read alike**: plain loads and stores are unlocked, the bytes
read and written have the access's size, and memory accesses are not empty. (The store-buffer
machine sizes a unit by its byte list and tags only `rmw`s as locked; the litmus checker uses
the event's size and tag.) -/
def ActOk (a : XAct) : Prop :=
  (a.ev.kind = .load → a.ev.locked = false) ∧ (a.ev.kind = .store → a.ev.locked = false) ∧
  (a.ev.kind.reads = true → a.rd.length = a.ev.size) ∧
  (a.ev.kind.writes = true → a.wr.length = a.ev.size) ∧
  ((a.ev.kind.reads || a.ev.kind.writes) = true → 0 < a.ev.size)

/-- Every action of every trace is `ActOk`. -/
def TracesOk (trs : List XTrace) : Prop := ∀ tr ∈ trs, ∀ a ∈ tr.acts, ActOk a

/-- **No access tears**: the litmus checker splits no unit of the traces into bytes (`Litmus.units`
is `accUnits`), as for aligned accesses of at most eight bytes in cells. -/
def NoTear (trs : List XTrace) : Prop :=
  ∀ u ∈ accUnits trs, tearAcc (accUnits trs) u.1 = false

/-- **The run's initial memory is the test's on every byte read**: every byte some action of
the traces reads has the same initial value (unmapped reading as `0`) in `init` and in the
test (`Test.initB`). -/
def InitReads (t : Test) (init : Silmaril.X86.MemoryModel.Tso.Mem) (trs : List XTrace) : Prop :=
  ∀ tr ∈ trs, ∀ a ∈ tr.acts, a.ev.kind.reads = true → ∀ y, a.ev.addr ≤ y →
    y < a.ev.addr + a.ev.size → (init y).getD 0 = t.initB y

end Silmaril.X86.Concurrency.Bridge.PoolRun
