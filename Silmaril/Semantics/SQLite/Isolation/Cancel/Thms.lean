module

public import Silmaril.Semantics.SQLite.Isolation.Cancel.Defs
import Silmaril.Proofs.Semantics.SQLite.Isolation.Cancel.Liveness
import Silmaril.Proofs.Semantics.SQLite.Isolation.Cancel.Witnesses
import Silmaril.Proofs.Semantics.SQLite.Isolation.Cancel.Compile

public section

/-!
# Cancellation liveness: statements

For the abstract work-tick machine of `Defs`, over arbitrary raw code, arbitrary raw input
and arbitrary machine state:

* `MState.step_rank_decreases`: with a visible cancel and helpers that poll, every counted
  step either stops the operation or strictly lowers `MState.rank`.
* `MState.drive_stops_by_next_poll`: `rank + 1` counted steps suffice to stop; the stop is the
  next poll's observation or an earlier stop (halt or fault).
* `cancel_liveness`: once a relevant cancel is visible, fair scheduling, returning external
  calls and coherent management make the operation stop.
* `counted_steps_le_rank`: while it has not stopped, the operation has taken at most `rank`
  counted steps since the cancel became visible, however scheduling and host calls interleave.
* `stutter_countermodel`: polling at an outer-loop cadence alone does not give liveness when a
  helper can stutter between polls.
* `incoherent_witness`, `no_return_witness`, `unfair_witness`: each premise is needed.

Boundary: the conclusion is quiescence of the abstract machine (`MState.Stopped`), counted in
modeled steps. API return, finalization, cleanup, rollback and wall-clock time are not modeled.
The source language is connected to the machine only by `compile_decode`: compiled code
decodes to the emitted instructions; there is no simulation theorem between source and
compiled behaviour. `compiled_cancel_liveness` holds because `cancel_liveness` covers all raw
code, not because of compiler correctness. Nothing here is about native SQLite, a C compiler
or ELF code.

The positive theorems assume `HelperDiscipline.pollsInside`: helper ticks are counted and
polled. A helper that makes progress but polls only at the outer loop is checked on one
concrete run (`Checks`), not proved in general.

Native bridge (outstanding, not claimed): for pinned SQLite 3.54.1 on arbitrary SQL and
database bytes, one would have to show that every compiled or reprepared VDBE program reaches
an interrupt check within a bounded number of its own steps, that every helper the VDBE calls
(B-tree, pager, sorter, built-in functions) checks the flag itself or makes bounded progress
between checks (`stutter_countermodel` shows this cannot be dropped), and eventually that the
native x86-64 Linux ELF refines that machine.

Design context: `docs/projects/sqlite-interrupt-progress-liveness.md` (uncompiled design
note). This module is a smaller work-tick machine, not its `Vdbe.RawProgram` responsiveness
target. Against the note: the countdown `MState.rank` plays `PollBound K`;
`counted_steps_le_rank` is its tick-bounded cancellation with no unwind (`U = 0`);
`cancel_liveness` is its fairness bridge, assuming `RelevantVisible` instead of a
visibility hypothesis; `incoherent_witness` is its startup-clear/reprepare clobber race; and
`stutter_countermodel` is its fair-host negative witness. Not modeled here: `xProgress` as a
separate per-statement mechanism, unwinding and rollback bounds, yielded rows, connection
quiescence (`nVdbeActive = 0`), OOM, and wall-clock corollaries.
-/

namespace Silmaril.Semantics.SQLite.Isolation.Cancel

namespace MState

variable {P : Profile} {H : HelperDiscipline} {code : List Nat} {vis : Bool} {s : MState}

/-- Quiescence is absorbing: a stopped operation takes no further step. -/
theorem step_stopped {r : StopReason} (h : s.status = .stopped r) : s.step P H code vis = s :=
  Proofs.Semantics.SQLite.Isolation.Cancel.stopped_step h

/-- A host return does not restart a stopped operation. -/
theorem resume_stopped {r : StopReason} (h : s.status = .stopped r) : s.resume = s :=
  Proofs.Semantics.SQLite.Isolation.Cancel.stopped_resume h

/-- The internal rank decreases: with a visible cancel and helpers that poll, each counted
step of a running operation stops it or leaves it active with strictly smaller rank. -/
theorem step_rank_decreases (code : List Nat) (hH : H.pollsInside = true)
    (hs : s.status = .running) :
    (s.step P H code true).Stopped ∨
      ((s.step P H code true).active = true ∧ (s.step P H code true).rank P < s.rank P) :=
  Proofs.Semantics.SQLite.Isolation.Cancel.step_vis code hH hs

/-- A due poll observes a visible cancel. -/
theorem poll_due_observes (code : List Nat) (hs : s.status = .running)
    (hp : P.period ≤ s.sincePoll) (hh : s.helperLeft = 0 ∨ H.pollsInside = true) :
    s.step P H code true = s.stopWith .cancelled :=
  Proofs.Semantics.SQLite.Isolation.Cancel.poll_due code hs hp hh

/-- Next poll or earlier stop: with external calls returning at once, `rank + 1` counted steps
stop a running operation that sees a cancel. -/
theorem drive_stops_by_next_poll (code : List Nat) (hH : H.pollsInside = true)
    (hs : s.status = .running) : (drive P H code true (s.rank P + 1) s).Stopped :=
  Proofs.Semantics.SQLite.Isolation.Cancel.drive_stops code hH _ hs (Nat.lt_succ_self _)

end MState

namespace Sys

variable {P : Profile} {H : HelperDiscipline} {code : List Nat} {s : Sys}

/-- A cancel naming another operation is inert. -/
theorem deliver_stale {e : Nat} (h : e ≠ s.epoch) : s.step P H code (.deliver e) = s := by
  simp [step, h]

/-- Delivery alone makes nothing visible. -/
theorem deliver_visible (e : Nat) : (s.step P H code (.deliver e)).visible = s.visible := by
  by_cases h : e = s.epoch ∧ s.mach.active = true <;> simp [step, h]

/-- Publication makes a delivered cancel visible. -/
theorem publish_visible (h : s.pending = true) : (s.step P H code .publish).visible = true := by
  simp [step, h]

/-- A new operation cannot start while the current one is active. -/
theorem begin_active {e : Nat} {m : MState} (h : s.mach.active = true) :
    s.step P H code (.begin e m) = s := by
  simp [step, h]

end Sys

variable {P : Profile} {H : HelperDiscipline} {code : List Nat} {s₀ : Sys} {ev : Nat → Ev}

/-- **Cancellation liveness.** Once a relevant cancel is visible at `t` to the active
operation, no raw code, raw input or machine state keeps it running forever, provided helpers
poll, scheduling is fair, external calls return and the cancel is not cleared. -/
theorem cancel_liveness (hH : H.pollsInside = true) {t : Nat} (hfair : FairFrom ev t)
    (hext : ExternalReturnsFrom P H code s₀ ev t) (hcoh : CoherentFrom ev t)
    (hvis : (run P H code s₀ ev t).RelevantVisible) :
    ∃ m, t ≤ m ∧ (run P H code s₀ ev m).mach.Stopped :=
  Proofs.Semantics.SQLite.Isolation.Cancel.cancel_liveness hH hfair hext hcoh hvis

/-- **Counted-step bound.** While the operation has not stopped, it has taken at most
`rank` counted steps in the `k` events after the cancel became visible. No fairness or host
assumption is needed: scheduling gaps and external calls are not counted. -/
theorem counted_steps_le_rank (hH : H.pollsInside = true) {t : Nat} (hcoh : CoherentFrom ev t)
    (hvis : (run P H code s₀ ev t).RelevantVisible) (k : Nat)
    (hact : ∀ j, j ≤ k → (run P H code s₀ ev (t + j)).mach.active = true) :
    countedAfter P H code s₀ ev t k ≤ (run P H code s₀ ev t).mach.rank P :=
  Nat.le_of_add_right_le
    (Proofs.Semantics.SQLite.Isolation.Cancel.counted_bound hH hcoh hvis k hact).1

/-! ## Source programs -/

/-- Supported instructions round-trip through the raw encoding. -/
theorem decode_encode {i : Instr} (h : i.Supported) : decode (encode i) = i :=
  Proofs.Semantics.SQLite.Isolation.Cancel.decode_encode h

/-- Compiled code decodes to the instructions the compiler emitted. -/
theorem compile_decode (w : Work) : (compile w).map decode = compileAt w 0 ++ [.halt] :=
  Proofs.Semantics.SQLite.Isolation.Cancel.compile_decode w

/-- Compiled source programs inherit cancellation liveness from the raw-code theorem. -/
theorem compiled_cancel_liveness (w : Work) {ev : Nat → Ev} (hH : H.pollsInside = true)
    {t : Nat} (hfair : FairFrom ev t) (hext : ExternalReturnsFrom P H (compile w) s₀ ev t)
    (hcoh : CoherentFrom ev t) (hvis : (run P H (compile w) s₀ ev t).RelevantVisible) :
    ∃ m, t ≤ m ∧ (run P H (compile w) s₀ ev m).mach.Stopped :=
  cancel_liveness hH hfair hext hcoh hvis

/-! ## Countermodel and premise witnesses -/

/-- **Countermodel.** Polling at an outer-loop cadence does not give liveness if a helper can
stutter between polls: the schedule is fair, no external call is pending, the cancel stays
visible and the outer poll budget never exceeds its period, yet the operation never stops. -/
theorem stutter_countermodel :
    FairFrom alwaysRun 0 ∧
    ExternalReturnsFrom onePoll stutterHelper helperCode cancelledAtStart alwaysRun 0 ∧
    CoherentFrom alwaysRun 0 ∧
    (run onePoll stutterHelper helperCode cancelledAtStart alwaysRun 0).RelevantVisible ∧
    ∀ n,
      ¬ (run onePoll stutterHelper helperCode cancelledAtStart alwaysRun n).mach.Stopped ∧
      (run onePoll stutterHelper helperCode cancelledAtStart alwaysRun n).mach.sincePoll ≤
        onePoll.period ∧
      (run onePoll stutterHelper helperCode cancelledAtStart alwaysRun n).visible = true :=
  Proofs.Semantics.SQLite.Isolation.Cancel.stutter_countermodel

/-- The same stuttering helper, charged to the poll budget, observes the cancel at step 2. -/
theorem chargedStutter_stops :
    (run onePoll chargedStutterHelper helperCode cancelledAtStart alwaysRun 2).mach.status =
      .stopped .cancelled := rfl

/-- Coherent management is needed: clearing a visible cancel lets a compiled loop run forever. -/
theorem incoherent_witness :
    FairFrom clearThenRun 0 ∧
    ExternalReturnsFrom onePoll chargedStutterHelper loopCode cancelledAtStart clearThenRun 0 ∧
    (run onePoll chargedStutterHelper loopCode cancelledAtStart clearThenRun 0).RelevantVisible ∧
    ¬ CoherentFrom clearThenRun 0 ∧
    ∀ n,
      ¬ (run onePoll chargedStutterHelper loopCode cancelledAtStart clearThenRun n).mach.Stopped :=
  Proofs.Semantics.SQLite.Isolation.Cancel.incoherent_witness

/-- External return is needed: an operation parked in a call that never returns never stops. -/
theorem no_return_witness :
    FairFrom alwaysRun 0 ∧ CoherentFrom alwaysRun 0 ∧
    (run onePoll chargedStutterHelper callCode cancelledAtStart alwaysRun 0).RelevantVisible ∧
    ¬ ExternalReturnsFrom onePoll chargedStutterHelper callCode cancelledAtStart alwaysRun 0 ∧
    ∀ n,
      ¬ (run onePoll chargedStutterHelper callCode cancelledAtStart alwaysRun n).mach.Stopped :=
  Proofs.Semantics.SQLite.Isolation.Cancel.no_return_witness

/-- Fair scheduling is needed: an operation never scheduled never stops. -/
theorem unfair_witness :
    ExternalReturnsFrom onePoll chargedStutterHelper loopCode cancelledAtStart neverRun 0 ∧
    CoherentFrom neverRun 0 ∧
    (run onePoll chargedStutterHelper loopCode cancelledAtStart neverRun 0).RelevantVisible ∧
    ¬ FairFrom neverRun 0 ∧
    ∀ n,
      ¬ (run onePoll chargedStutterHelper loopCode cancelledAtStart neverRun n).mach.Stopped :=
  Proofs.Semantics.SQLite.Isolation.Cancel.unfair_witness

end Silmaril.Semantics.SQLite.Isolation.Cancel
