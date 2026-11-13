module

public import Silmaril.X86.Litmus.Complete.Defs
public import Silmaril.X86.Litmus.Extract.Thms
import Silmaril.Proofs.X86.Litmus.Complete

/-!
# Completeness of litmus event extraction: what is proved

All statements are PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/Litmus/Complete.lean`).

* `extract_complete`: **every domain-bounded sequential run is an extracted trace**. If
  extraction of a thread over `dom` succeeds, then every run of `Atomic9.step` from the
  thread's initial core to its end (`DomRun`), with any memory before each step (so other
  threads may interfere) and every read of every step returning a value of `dom`, is matched
  by some extracted trace: the same cores step by step, the trace's reads answered by the run's
  memories, and the trace's writes exactly the run's memory changes (`Trace.Matches`).
* `stepSym_complete`: the one-step form.

With `extract_sound` this makes the extracted set **exact** relative to the domain:
sound (every trace replays) and complete (every domain-bounded run is a trace). Whether a
given domain contains every value a concurrent execution can read is a separate question
(`Silmaril.X86.MemoryModel.Litmus.Closure`).
-/

@[expose] public section

namespace Silmaril.X86.Litmus

open Silmaril.X86 (State)

/-- **Extraction is complete** relative to the value domain. -/
theorem extract_complete {t : Thread} {dom : List Nat} {fuel : Nat} {trs : List Trace}
    (h : extract t dom fuel = some trs) {run : List SeqStep} {fin : State}
    (hr : DomRun t dom t.init run fin) : ∃ tr ∈ trs, tr.Matches run fin :=
  Silmaril.Proofs.X86.Litmus.extract_complete h hr

/-- **One symbolic step is complete**: a machine step whose reads return domain values is one
of the step's branches. -/
theorem stepSym_complete {t : Thread} {dom : List Nat} {s : State}
    {outs : List (List Act × State)} (h : stepSym t dom s = some outs) {q : SeqStep}
    (hR : q.pre.regions = t.regions) (hl : Silmaril.X86.Ext.Loaded q.pre t.base t.code)
    (hd : ∀ i n, t.fetch s = some (i, n) → DomReads dom q.pre (MemEvent.atomic9Accesses i s n))
    (hs : Atomic9.step ⟨s, q.pre⟩ = some ⟨q.post, q.mem⟩) :
    ∃ o ∈ outs, o.2 = q.post ∧ Answers q.pre o.1 ∧ applyWrites q.pre o.1 = some q.mem :=
  Silmaril.Proofs.X86.Litmus.stepSym_complete h hR hl hd hs

end Silmaril.X86.Litmus
