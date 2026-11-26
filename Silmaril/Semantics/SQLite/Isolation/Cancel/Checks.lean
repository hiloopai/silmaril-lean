module

import Silmaril.Semantics.SQLite.Isolation.Cancel.Thms

namespace Silmaril.Semantics.SQLite.Isolation.Cancel.Checks

open Silmaril.Semantics.SQLite.Isolation.Cancel

/-! Raw decoding is total: malformed operands and unsupported opcodes are explicit faults. -/

example : decode 9 = .malformed 9 := rfl
example : decode 7 = .unsupported 7 := rfl
example : decode (8 * 5 + 2) = .jump 5 := rfl
example : loopCode = [1, 2, 0] := rfl

private def fault (code : List Nat) (input : List Nat) : Status :=
  (MState.step ⟨4⟩ chargedStutterHelper code false ⟨0, 0, 0, input, .running⟩).status

example : fault [7] [] = .stopped .unsupported := rfl
example : fault [9] [] = .stopped .malformed := rfl
example : fault [] [] = .stopped .pcOutOfRange := rfl
example : fault [encode (.branch 0)] [] = .stopped .inputExhausted := rfl

/-! Without a cancel the compiled loop `forever tick` cycles: four counted steps under period
`1` (work, poll, jump, poll) return it to its start. -/

example : MState.drive onePoll chargedStutterHelper loopCode false 4 fresh = fresh := rfl

/-! Delivery is not visibility: a delivered, unpublished cancel is not observed. -/

private def deliverThenRun : Nat → Ev
  | 0 => .deliver 0
  | _ + 1 => .run

private def start : Sys := ⟨0, fresh, false, false⟩

example : (run onePoll chargedStutterHelper loopCode start deliverThenRun 9).mach.status =
    .running := rfl
example : (run onePoll chargedStutterHelper loopCode start deliverThenRun 9).visible = false := rfl

/-! Publication makes it visible; the next due poll observes it. -/

private def deliverPublishRun : Nat → Ev
  | 0 => .deliver 0
  | 1 => .publish
  | _ + 2 => .run

example : (run onePoll chargedStutterHelper loopCode start deliverPublishRun 4).mach.status =
    .stopped .cancelled := rfl

/-! A cancel for another epoch is stale and never becomes visible. -/

private def staleThenRun : Nat → Ev
  | 0 => .deliver 1
  | 1 => .publish
  | _ + 2 => .run

example : (run onePoll chargedStutterHelper loopCode start staleThenRun 9).visible = false := rfl
example : (run onePoll chargedStutterHelper loopCode start staleThenRun 9).mach.status =
    .running := rfl

/-! A helper with a large count, charged to the poll budget, still stops by the next poll. -/

private def bigHelper : MState := ⟨0, 0, 1000000, [], .running⟩

example : (MState.drive onePoll chargedStutterHelper [] true (bigHelper.rank onePoll + 1)
    bigHelper).Stopped :=
  MState.drive_stops_by_next_poll [] rfl rfl

/-! A helper that makes progress but polls only at the outer loop also stops on this example.
This is a concrete run, not a theorem about uncharged helpers. -/

example : (run onePoll ⟨(· - 1), false⟩ helperCode cancelledAtStart alwaysRun 3).mach.status =
    .stopped .cancelled := rfl

/-! The liveness theorem applies to every compiled program. -/

example (ev : Nat → Ev) (t : Nat) (hfair : FairFrom ev t)
    (hext : ExternalReturnsFrom onePoll chargedStutterHelper loopCode cancelledAtStart ev t)
    (hcoh : CoherentFrom ev t)
    (hvis : (run onePoll chargedStutterHelper loopCode cancelledAtStart ev t).RelevantVisible) :
    ∃ m, t ≤ m ∧
      (run onePoll chargedStutterHelper loopCode cancelledAtStart ev m).mach.Stopped :=
  compiled_cancel_liveness (.forever .tick) rfl hfair hext hcoh hvis

end Silmaril.Semantics.SQLite.Isolation.Cancel.Checks
