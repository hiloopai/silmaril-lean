module

public import Silmaril.X86.Concurrency.Bridge.PoolRun.Defs
public import Silmaril.X86.MemoryModel.OpAx.Thms
import Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Compose
import Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Shape
public import Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Example

/-!
# The TSO pool as a store-buffer run, and store-buffer candidates as litmus candidates: theorems

PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/Concurrency/Bridge/PoolRun/{Transport,Units,Ax,Run,Compose,Shape}.lean`).
Two of the missing pieces of `Bridge.Task.tsoRunCir` (numbered as in that Task's plan):

* **(4) the pool run is an `OpAx.Run`**: `opRun_of_runA`. A recorded run of the byte-granular
  TSO pool over `Atomic9.step` (`RunA`: `TsoReach atomic9Ev` with each instruction step's
  actions) from empty buffers, ending drained, is a complete run of the store-buffer machine
  (`Litmus.AStep`) on the program of the threads' events (`poolProg`, which is `traceX` of the
  threads' traces, `poolProg_eq`), from the initial memory to the pool's final state
  (`TPool.toX`). `runA_of_reach`: every `TsoReach` run is recorded when every step it can take
  has `StepActs` actions; `stepSym_shape`: every branch of `stepSym` has the `Shape` those
  actions need. `runA_chain`: each thread's history is a run of that thread on its views.
* **(6) Store-buffer candidates are litmus candidates**: `axReach_of_explains`. A TSO-consistent
  candidate that `OpAx.Explains` a store-buffer run of `trs.mapIdx traceX`, with paired locked
  read-modify-writes (`run_explains_tso_paired` gives one), yields a well-formed
  TSO-consistent candidate over the units of `trs` whose reads return the traces' bytes, i.e.
  an `AxReach` final state; its memory is the run's final memory on every byte some access
  writes and on every byte whose initial value the run and the test share. Hypotheses:
  `TracesOk` (sizes and `locked` tags both encodings read alike; automatic for recorded runs,
  `tracesOk_pool`), `NoTear` (the litmus checker splits no unit) and `InitReads` (the run's initial
  memory is the test's on every byte read).
* **Composed** (with piece (5)): `explains_of_runA`, `axReach_of_runA`.
* **Non-vacuity** (`sb_axReach`): for SB's traces (both loads `0`), the store-buffer run,
  which no SC candidate explains (`OpAx.sb_weak_not_sc`), meets every hypothesis of
  `axReach_of_explains`, which turns it into an x86-TSO `AxReach` final state of the SB test;
  the same traces have no SC `AxReach` final state (`sb_not_axReach_sc`).

Not here: pieces (1)-(3) and (7) of the plan (per-thread runs as CIR runs, the run-level
`tvRun_sound`, the witness). `Bridge.tsoRunCir_holds` composes these pieces into
`Task.tsoRunCir`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Bridge.PoolRun

open Silmaril.X86 (State)
open Silmaril.Process (Memory)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (Act stepSym)
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace Test traceX AxReach finalOf)
open Silmaril.X86.MemoryModel.Tso (XState Mem)
open Silmaril.X86.MemoryModel.OpAx (Explains RmwPaired ThreadCells ThreadsOk)
open Silmaril.X86.Pool (TPool TsoReach overlay atomic9Ev Drained)

/-! ## (4) The pool run is an `OpAx.Run` -/

/-- **(4) A drained recorded TSO pool run is a complete run of the machine** on the threads'
events, from the initial memory to the pool's final state. -/
theorem opRun_of_runA {Fin : Nat → State → Prop} {N : Nat} {p₀ : TPool Nat} {H : Nat → List Obs}
    {p : TPool Nat} (h : RunA Fin p₀ H p) (hb : ∀ t, p₀.buffer t = [])
    (hN : ∀ t, N ≤ t → p₀.threads t = none) (hd : Drained p) :
    Silmaril.X86.MemoryModel.OpAx.Run (poolProg N H) (fun a => p₀.memory.bytes[a]?) p.toX :=
  Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.opRun_of_runA h hb hN hd

/-- A recorded run is a `TsoReach` run. -/
theorem runA_reach {Fin : Nat → State → Prop} {p₀ : TPool Nat} {H : Nat → List Obs}
    {p : TPool Nat} (h : RunA Fin p₀ H p) : TsoReach atomic9Ev Fin p₀ p :=
  Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.runA_reach h

/-- **Every `TsoReach` run is recorded** when every step it can take has `StepActs` actions on
the thread's view. -/
theorem runA_of_reach {Fin : Nat → State → Prop} {p₀ p : TPool Nat}
    (h : TsoReach atomic9Ev Fin p₀ p)
    (hA : ∀ (p₁ : TPool Nat) (t : Nat) (c : State) (i : Atomic9.Instr) (n : Nat) (c' : State)
      (m' : Memory), TsoReach atomic9Ev Fin p₀ p₁ → p₁.threads t = some c → ¬ Fin t c →
      atomic9Ev.fetch (overlay p₁.memory (p₁.buffer t)) c.rip.toNat = some (i, n) →
      atomic9Ev.exec i c (overlay p₁.memory (p₁.buffer t)) n = .ok c' m' →
      ∃ acts, StepActs acts i c n ⟨overlay p₁.memory (p₁.buffer t), c', m'⟩) :
    ∃ H, RunA Fin p₀ H p :=
  Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.runA_of_reach h hA

/-- **Each thread's history is a run of the thread** (`Chain`): from its initial core to its
current core, each step an `Atomic9.step` on the thread's view with `StepActs` actions; a
thread that does not exist takes no step. -/
theorem runA_chain {Fin : Nat → State → Prop} {p₀ : TPool Nat} {H : Nat → List Obs}
    {p : TPool Nat} (h : RunA Fin p₀ H p) (t : Nat) :
    (∀ c₀, p₀.threads t = some c₀ → ∃ c, p.threads t = some c ∧ Chain c₀ (H t) c) ∧
      (p₀.threads t = none → p.threads t = none ∧ H t = []) :=
  Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.runA_chain h t

/-- **Every branch of `stepSym` has the recorded `Shape`.** -/
theorem stepSym_shape {t : Silmaril.X86.Litmus.Thread} {dom : List Nat} {s : State}
    {outs : List (List XAct × State)} (h : stepSym t dom s = some outs) :
    ∀ o ∈ outs, Shape o.1 :=
  Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.stepSym_shape h

/-- The store-buffer program of a recorded run is `traceX` of the threads' traces. -/
theorem poolProg_eq (N : Nat) (H : Nat → List Obs) (fin : Nat → State) :
    poolProg N H = (poolTraces N H fin).mapIdx traceX :=
  Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.poolProg_eq N H fin

/-- The events of the store-buffer program of a recorded run name their threads. -/
theorem threadsOk_poolProg (N : Nat) (H : Nat → List Obs) : ThreadsOk (poolProg N H) :=
  Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.threadsOk_poolProg N H

/-- The actions of a recorded run are `ActOk`. -/
theorem tracesOk_pool {Fin : Nat → State → Prop} {p₀ : TPool Nat} {H : Nat → List Obs}
    {p : TPool Nat} (h : RunA Fin p₀ H p) (N : Nat) (fin : Nat → State) :
    TracesOk (poolTraces N H fin) :=
  Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.tracesOk_pool h N fin

/-! ## (6) Store-buffer candidates are litmus candidates -/

/-- **(6) From `OpAx.Explains` to `AxReach`**: a TSO candidate with paired `rmw`s explaining a
store-buffer run of `trs.mapIdx traceX` gives an x86-TSO `AxReach` final state of any test whose
trace sets contain `trs`, with the traces' registers and a memory that is the run's final memory on
every byte, except possibly where the run's and the test's initial values differ and no
access writes. -/
theorem axReach_of_explains {t : Test} {T : List (List XTrace)} {trs : List XTrace}
    (hT : List.Forall₂ (· ∈ ·) trs T) (hok : TracesOk trs) (hnt : NoTear trs)
    {init : Silmaril.X86.MemoryModel.Tso.Mem} (hI : InitReads t init trs) {s : XState Nat} {x : Silmaril.X86.MemoryModel.Axiomatic.Exec}
    (hx : Explains Silmaril.X86.MemoryModel.Axiomatic.Exec.Tso (trs.mapIdx traceX) init s x)
    (hp : RmwPaired x) :
    ∃ m, AxReach t T Silmaril.X86.MemoryModel.Axiomatic.Exec.Tso (finalOf trs m) ∧
      ∀ y, m y = s.memory y ∨ (m y = t.initMem y ∧ s.memory y = init y) :=
  Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.axReach_of_explains hT hok hnt hI hx hp

/-- **Non-vacuity of (6)**: SB's weak outcome is, through `axReach_of_explains`, an x86-TSO
`AxReach` final state of the SB test. -/
theorem sb_axReach : ∃ m, AxReach Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Example.sbTest
    [[Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Example.sbTr0],
      [Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Example.sbTr1]]
    Silmaril.X86.MemoryModel.Axiomatic.Exec.Tso
    (finalOf Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Example.sbTrs m) :=
  Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Example.sb_axReach

/-- **The target is still weak**: SB's traces with both loads reading `0` have no
SC `AxReach` final state, so `sb_axReach` is a TSO-only outcome. -/
theorem sb_not_axReach_sc (f : Silmaril.X86.MemoryModel.Litmus.Final) :
    ¬ AxReach Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Example.sbTest
      [[Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Example.sbTr0],
        [Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Example.sbTr1]]
      Silmaril.X86.MemoryModel.Axiomatic.Exec.Sc f :=
  Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Example.sb_not_axReach_sc f

/-! ## Composed with the store-buffer run -/

/-- **(4) + (5)**: a drained recorded run whose threads have cells is explained by an x86-TSO
candidate with paired locked read-modify-writes. -/
theorem explains_of_runA {Fin : Nat → State → Prop} {N : Nat} {p₀ : TPool Nat}
    {H : Nat → List Obs} {p : TPool Nat} (h : RunA Fin p₀ H p) (hb : ∀ t, p₀.buffer t = [])
    (hN : ∀ t, N ≤ t → p₀.threads t = none) (hd : Drained p) (hC : ThreadCells (poolProg N H)) :
    ∃ x, Explains Silmaril.X86.MemoryModel.Axiomatic.Exec.Tso (poolProg N H)
      (fun a => p₀.memory.bytes[a]?) p.toX x ∧ RmwPaired x :=
  Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.explains_of_runA h hb hN hd hC

/-- **(4) + (5) + (6)**: the final state of a drained recorded TSO pool run is, up to bytes
nobody writes whose initial values differ, an x86-TSO `AxReach` final state of a test whose
trace sets contain the threads' traces. -/
theorem axReach_of_runA {Fin : Nat → State → Prop} {N : Nat} {p₀ : TPool Nat}
    {H : Nat → List Obs} {p : TPool Nat} (h : RunA Fin p₀ H p) (hb : ∀ t, p₀.buffer t = [])
    (hN : ∀ t, N ≤ t → p₀.threads t = none) (hd : Drained p) (hC : ThreadCells (poolProg N H))
    (fin : Nat → State) {t : Test} {T : List (List XTrace)}
    (hT : List.Forall₂ (· ∈ ·) (poolTraces N H fin) T) (hnt : NoTear (poolTraces N H fin))
    (hI : InitReads t (fun a => p₀.memory.bytes[a]?) (poolTraces N H fin)) :
    ∃ m, AxReach t T Silmaril.X86.MemoryModel.Axiomatic.Exec.Tso (finalOf (poolTraces N H fin) m) ∧
      ∀ y, m y = p.memory.bytes[y]? ∨
        (m y = t.initMem y ∧ p.memory.bytes[y]? = p₀.memory.bytes[y]?) :=
  Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.axReach_of_runA h hb hN hd hC fin hT hnt hI

end Silmaril.X86.Concurrency.Bridge.PoolRun
