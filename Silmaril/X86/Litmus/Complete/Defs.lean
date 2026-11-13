module

public import Silmaril.X86.Litmus.Extract.Defs

/-!
# Completeness of litmus event extraction: definitions

`extract_sound` says every extracted trace replays on the sequential machine `Atomic9.step`.
This module states the converse, **completeness relative to the value domain**: every run of
the sequential machine whose reads all return values of the domain is one of the extracted
traces.

A run is taken **one step at a time with interference** (`DomRun`): before each step the
memory may be any memory with the thread's regions and code loaded (other threads may have
changed it), so the statement covers every interleaving a memory model can choose, as
`Replay` does. The only restriction is the one extraction makes by design: each read of the
step (the access list `MemEvent.atomic9Accesses` of the decoded instruction) returns the
little-endian bytes of a value of the domain (`DomReads`).

The theorem is `extract_complete` in `Complete/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Litmus

open Silmaril.X86 (State)
open Silmaril.Process (Memory)
open MemEvent (Event)

/-- Every read event of `es` returns, in memory `m`, the bytes of some value of `dom` (at the
event's size). -/
def DomReads (dom : List Nat) (m : Memory) (es : List Event) : Prop :=
  ∀ e ∈ es, e.kind.reads = true → ∃ v ∈ dom, m.readBytes e.addr e.size = some (valBytes v e.size)

/-- One step of a sequential run: the memory before the step, and the core and memory after
it. -/
structure SeqStep where
  pre : Memory
  post : State
  mem : Memory

/-- **A domain-bounded sequential run of a thread**, from core `s` to the finished core `fin`.
At every step the thread has not finished (`rip ≠ endRip`), the memory before the step has the
thread's regions and code, the step's reads return values of `dom`, and `Atomic9.step` goes to
the recorded core and memory. Memory may change arbitrarily between steps (the next step starts
from its own `pre`), so other threads can interfere. -/
inductive DomRun (t : Thread) (dom : List Nat) : State → List SeqStep → State → Prop
  | done (s : State) (h : s.rip = t.endRip) : DomRun t dom s [] s
  | step (s : State) (q : SeqStep) (rest : List SeqStep) (fin : State)
      (hne : s.rip ≠ t.endRip) (hR : q.pre.regions = t.regions)
      (hl : Silmaril.X86.Ext.Loaded q.pre t.base t.code)
      (hd : ∀ i n, t.fetch s = some (i, n) →
        DomReads dom q.pre (MemEvent.atomic9Accesses i s n))
      (hs : Atomic9.step ⟨s, q.pre⟩ = some ⟨q.post, q.mem⟩)
      (tail : DomRun t dom q.post rest fin) : DomRun t dom s (q :: rest) fin

/-- A trace **matches** a run: the same number of steps, each step reaching the run's core,
answering the run's reads and writing exactly the run's memory change; the same final core. -/
def Trace.Matches (tr : Trace) (run : List SeqStep) (fin : State) : Prop :=
  tr.final = fin ∧ List.Forall₂ (fun (r : StepRec) (q : SeqStep) =>
    r.post = q.post ∧ Answers q.pre r.acts ∧ applyWrites q.pre r.acts = some q.mem) tr.steps run

end Silmaril.X86.Litmus
