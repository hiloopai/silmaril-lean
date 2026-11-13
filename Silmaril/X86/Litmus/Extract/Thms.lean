module

public import Silmaril.X86.Litmus.Extract.Defs
public import Silmaril.X86.MemEvent.Thms
public import Silmaril.X86.Atomic9.Thms
import Silmaril.Proofs.X86.Litmus.Extract

/-!
# Litmus event extraction: what is proved

All statements are PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/Litmus/Extract.lean`).

* `extract_sound`: **every extracted trace replays** on the sequential machine
  `Atomic9.step` (`Replay`): at each step, on every memory with the thread's regions, its code
  loaded, and answering the step's reads with the trace's bytes, one step reaches the
  trace's next core and writes exactly the trace's bytes. Since the hypothesis is per step,
  other threads may have changed memory in between.
* `Replay.reaches`: the single-thread corollary (`Solo`): with no interference the machine
  reaches the trace's final core and memory.
* `stepSym_sound`: the one-step form.
* `allPlaced_satisfiable`: **non-vacuity**: when the decidable check `Thread.allPlaced`
  holds, every step's replay hypothesis is satisfied by some memory (built from the code and
  the read bytes), so `Replay` is not vacuously true.
* `stepSym_events`: the actions of a step are exactly the access list
  `MemEvent.atomic9Accesses` of the instruction decoded at `rip` (kinds, addresses, sizes,
  `locked` tags), so the axiomatic models read these events.

Not claimed: that the extracted set is **complete** (every sequential behaviour whose read
values lie in the domain is among the traces). It is true by construction for the supported
forms (`memStep` has one branch per domain value, and `Atomic9.exec` is a function), but it is
not stated or proved here.
-/

@[expose] public section

namespace Silmaril.X86.Litmus

open Silmaril.X86 (State)
open Silmaril.Process (Memory)

/-- **Extraction is sound**: every extracted trace replays on `Atomic9.step`. -/
theorem extract_sound {t : Thread} {dom : List Nat} {fuel : Nat} {trs : List Trace}
    (h : extract t dom fuel = some trs) : ∀ tr ∈ trs, Replay t t.init tr.steps tr.final :=
  Silmaril.Proofs.X86.Litmus.extract_sound h

/-- **A replayed trace runs solo** on `Atomic9.step`. -/
theorem Replay.reaches {t : Thread} {s s' : State} {steps : List StepRec}
    (h : Replay t s steps s') {m m' : Memory} (hs : Solo t m steps m') :
    Silmaril.Machine.Execution.Reaches Atomic9.step ⟨s, m⟩ ⟨s', m'⟩ :=
  Silmaril.Proofs.X86.Litmus.Replay.reaches h hs

/-- **One symbolic step is sound.** -/
theorem stepSym_sound {t : Thread} {dom : List Nat} {s : State} {outs : List (List Act × State)}
    (h : stepSym t dom s = some outs) {o : List Act × State} (ho : o ∈ outs) (m : Memory)
    (hR : m.regions = t.regions) (hl : Silmaril.X86.Ext.Loaded m t.base t.code)
    (hans : Answers m o.1) :
    ∃ m', Atomic9.step ⟨s, m⟩ = some ⟨o.2, m'⟩ ∧ applyWrites m o.1 = some m' :=
  Silmaril.Proofs.X86.Litmus.stepSym_sound h ho m hR hl hans

/-- **The actions of a step are the access list.** -/
theorem stepSym_events {t : Thread} {dom : List Nat} {s : State}
    {outs : List (List Act × State)} (h : stepSym t dom s = some outs) {o : List Act × State}
    (ho : o ∈ outs) :
    ∃ i n, t.fetch s = some (i, n) ∧ o.1.map Act.ev = MemEvent.atomic9Accesses i s n :=
  Silmaril.Proofs.X86.Litmus.stepSym_events h ho

/-- **Non-vacuity of `Replay`**: if every step is `placed`, each step's replay hypothesis is
satisfied by some memory. -/
theorem allPlaced_satisfiable {t : Thread} {trs : List Trace} (h : t.allPlaced trs = true) :
    ∀ tr ∈ trs, ∀ r ∈ tr.steps, ∃ m : Memory, m.regions = t.regions ∧
      Silmaril.X86.Ext.Loaded m t.base t.code ∧ Answers m r.acts :=
  Silmaril.Proofs.X86.Litmus.allPlaced_satisfiable h

end Silmaril.X86.Litmus
