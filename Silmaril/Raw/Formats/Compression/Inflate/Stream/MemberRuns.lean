module

public import Silmaril.Raw.Formats.Compression.Inflate.Stream.MemberStep

/-!
# Compositional incremental member schedules

Finite schedules preserve the exact remaining member meaning under every
future input. This covers suspension, checksumming, malformed headers/bodies/
trailers, and successful completion, without assuming a schedule completes.
The institution contract transport exposes the same continuation abstraction
to clients without exposing the physical reservoir or checked raw state.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.MemberMachine

open Silmaril.Formats.Compression
open MemberSemantics

theorem start_normalizes (kind : Kind) (initial : List UInt8) :
    Reservoir.Normalizes (start kind initial).reservoir (ContainerFields.alignedReader initial) := by
  cases kind <;> exact Blocks.ofBytes_normalizes initial

theorem start_wellFormed (kind : Kind) (initial : List UInt8) :
    WellFormed (start kind initial) (ContainerFields.alignedReader initial) := by
  cases kind
  · trivial
  · exact ⟨rfl, rfl⟩

theorem runCalls_correct_feed (version : Version) (machine : MemberMachine)
    (reader : LSBReader) (calls : List RawMachine.Call)
    (hnorm : Reservoir.Normalizes machine.reservoir reader)
    (hwf : machine.WellFormed reader) :
    ∃ rest, Reservoir.Normalizes (runCalls version machine calls).reservoir rest ∧
      WellFormed (runCalls version machine calls) rest ∧
      ∀ future, denote machine (Reservoir.readerFeed reader (RawRuns.deliveredInput calls ++ future)) =
        denote (runCalls version machine calls) (Reservoir.readerFeed rest future) := by
  induction calls generalizing machine reader with
  | nil => exact ⟨reader, hnorm, hwf, fun _ => rfl⟩
  | cons call calls ih =>
    obtain ⟨middle, hm, hwm, first⟩ := step_correct_feed version (machine.feed call.input)
      (Reservoir.readerFeed reader call.input) call.schedulerFuel call.capacity
      (feed_normalizes machine call.input reader hnorm) (feed_wellFormed machine call.input reader hwf)
    obtain ⟨rest, hr, hwr, later⟩ := ih _ middle hm hwm
    refine ⟨rest, hr, hwr, ?_⟩
    intro future
    change denote machine (Reservoir.readerFeed reader (call.input ++ RawRuns.deliveredInput calls ++ future)) = _
    rw [List.append_assoc, ← Reservoir.readerFeed_append,
      ← feed_denote machine call.input _, first (RawRuns.deliveredInput calls ++ future)]
    exact later future

/-- Completed schedules produce the exact logical result and untouched suffix.
The starting point may already be a saved header/body/trailer continuation. -/
theorem done_correct_feed (version : Version) (machine : MemberMachine)
    (reader : LSBReader) (calls : List RawMachine.Call) (completed : RawState)
    (hnorm : Reservoir.Normalizes machine.reservoir reader)
    (hwf : machine.WellFormed reader)
    (hdone : runCalls version machine calls = .done completed) :
    ∃ rest, Reservoir.Normalizes completed.reservoir rest ∧ ∀ future,
      denote machine (Reservoir.readerFeed reader (RawRuns.deliveredInput calls ++ future)) =
        some (completed.output, Reservoir.readerFeed rest future) := by
  obtain ⟨rest, hr, _, observations⟩ := runCalls_correct_feed version machine reader calls hnorm hwf
  rw [hdone] at hr observations
  exact ⟨rest, hr, observations⟩

/-- An actually terminal malformed member remains rejected under later input.
This is stronger than rejecting only the bytes delivered so far. -/
theorem bad_correct_feed (version : Version) (machine : MemberMachine)
    (reader : LSBReader) (calls : List RawMachine.Call) (error : MemberError) (failed : RawState)
    (hnorm : Reservoir.Normalizes machine.reservoir reader)
    (hwf : machine.WellFormed reader)
    (hbad : runCalls version machine calls = .bad error failed) :
    ∀ future, denote machine
      (Reservoir.readerFeed reader (RawRuns.deliveredInput calls ++ future)) = none := by
  obtain ⟨rest, _, _, observations⟩ := runCalls_correct_feed version machine reader calls hnorm hwf
  rw [hbad] at observations
  exact observations

theorem checked_step_eq (first second : Version) (kind : Kind) (checked : CheckedRaw.State)
    (fuel capacity : Nat) :
    CheckedRaw.step kind.checksumKind first checked fuel capacity =
      CheckedRaw.step kind.checksumKind second checked fuel capacity := by
  simp only [CheckedRaw.step, RawEmission.stepEmitted, RawMachine.step_eq first second]

/-- Equality of these mathematical dispatchers does not identify execution of
the two distinct source revisions. Each source needs its own refinement edge. -/
theorem step_eq (first second : Version) (machine : MemberMachine) (fuel capacity : Nat) :
    step first machine fuel capacity = step second machine fuel capacity := by
  cases machine with
  | body kind checked =>
    cases hm : checked.machine <;> simp only [step, hm, checked_step_eq first second]
  | header _ _ _ | gzipHeader _ | trailer _ _ | done _ | bad _ _ => rfl

theorem runCalls_eq (first second : Version) (machine : MemberMachine) (calls : List RawMachine.Call) :
    runCalls first machine calls = runCalls second machine calls := by
  induction calls generalizing machine with
  | nil => rfl
  | cons call calls ih =>
    change runCalls first (applyCall first machine call) calls =
      runCalls second (applyCall second machine call) calls
    rw [show applyCall first machine call = applyCall second machine call from
      step_eq first second (machine.feed call.input) call.schedulerFuel call.capacity]
    exact ih _

end Silmaril.Formats.Compression.Inflate.Stream.MemberMachine
