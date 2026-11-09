module

public import Silmaril.Formats.Compression.Inflate.Stream.RawEmission
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.RawMachine
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.Checksums

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.RawEmission`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.RawEmission

open Silmaril.Formats.Compression

theorem token_finish_output (state : Reservoir) (pending : TokenOutput) :
    (TokenMachine.finish state pending).output = pending.output := by
  cases hp : pending.phase <;> simp only [TokenMachine.finish, hp, TokenMachine.output]

theorem token_emit_extension (state : Reservoir) (pending : TokenOutput) (capacity : Nat) :
    ∃ emitted, (TokenMachine.emit state pending capacity).output = pending.output ++ emitted ∧
      emitted.length ≤ capacity := by
  by_cases havailable : pending.DistanceAvailable
  · simp only [TokenMachine.emit, TokenOutput.step, havailable, ite_true]
    exact ⟨pending.emitted capacity,
      (token_finish_output state _).trans (pending.advance_append_emitted capacity),
      pending.emitted_capacity capacity⟩
  · simp only [TokenMachine.emit, TokenOutput.step, havailable, ite_false, TokenMachine.output]
    exact ⟨[], (List.append_nil _).symm, Nat.zero_le _⟩

theorem token_step_extension (machine : TokenMachine) (fuel capacity : Nat) :
    ∃ emitted, (machine.step fuel capacity).output = machine.output ++ emitted ∧
      emitted.length ≤ capacity := by
  cases machine with
  | parsing parser state history bytes =>
    cases hp : Parser.run fuel parser state with
    | done token rest =>
      simpa only [TokenMachine.step, hp, TokenOutput.start, TokenMachine.output] using
        token_emit_extension rest (TokenOutput.start history bytes token) capacity
    | error err rest | needInput next rest | yield next rest =>
      exact ⟨[], by simp only [TokenMachine.step, hp, TokenMachine.output, List.append_nil],
        Nat.zero_le _⟩
  | emitting state pending => exact token_emit_extension state pending capacity
  | done state completed | error err state history bytes =>
    exact ⟨[], (List.append_nil _).symm, Nat.zero_le _⟩

theorem acceptToken_output (last : Bool) (litLen dist : HuffmanTable) (machine : TokenMachine) :
    (RawMachine.acceptToken last litLen dist machine).output = machine.output := by
  cases machine with
  | parsing parser state history bytes | emitting state pending | error err state history bytes => rfl
  | done state completed =>
    cases hp : completed.phase with
    | literal byte | matchBytes count distance | endBlock =>
      simp only [RawMachine.acceptToken, hp, RawMachine.output, RawMachine.state,
        RawState.ofTokenMachine, TokenMachine.output]
    | complete flag =>
      cases flag
      · simp only [RawMachine.acceptToken, hp, RawMachine.output, RawMachine.state,
          RawState.ofTokenMachine, TokenMachine.start, TokenMachine.output]
      · simpa only [RawMachine.acceptToken, hp, TokenMachine.output] using
          RawMachine.finishBlock_output last ⟨state, completed.window, completed.output⟩

/-- The whole controller preserves its output prefix and respects the offered
capacity, without assuming valid input, a successful parse, or completion. -/
theorem step_extension (version : Version) (machine : RawMachine) (fuel capacity : Nat) :
    ∃ emitted, (RawMachine.step version machine fuel capacity).output = machine.output ++ emitted ∧
      emitted.length ≤ capacity := by
  cases machine with
  | header parser state =>
    cases hp : Parser.run fuel parser state.reservoir with
    | done pair rest =>
      obtain ⟨last, kind⟩ := pair
      refine ⟨[], ?_, Nat.zero_le _⟩
      simp only [RawMachine.step, hp]
      rw [RawMachine.dispatch_output]
      exact (List.append_nil _).symm
    | error err rest | needInput next rest | yield next rest =>
      exact ⟨[], by simp only [RawMachine.step, hp, RawMachine.output,
        RawMachine.state, List.append_nil], Nat.zero_le _⟩
  | storedHeader last parser state =>
    cases hp : Parser.run fuel parser state.reservoir <;>
      exact ⟨[], by simp only [RawMachine.step, hp, RawMachine.output,
        RawMachine.state, List.append_nil], Nat.zero_le _⟩
  | storedCopy last remaining state =>
    cases remaining with
    | zero =>
      refine ⟨[], ?_, Nat.zero_le _⟩
      change (RawMachine.finishBlock last state).output = state.output ++ []
      rw [RawMachine.finishBlock_output, List.append_nil]
    | succ count =>
      by_cases hc : capacity = 0
      · exact ⟨[], by simp only [RawMachine.step, hc, ite_true, List.append_nil], Nat.zero_le _⟩
      · cases hb : Reservoir.readBits 8 state.reservoir with
        | needInput rest =>
          exact ⟨[], by simp only [RawMachine.step, hc, ite_false, hb,
            RawMachine.output, RawMachine.state, List.append_nil], Nat.zero_le _⟩
        | value byte rest =>
          exact ⟨[UInt8.ofNat byte], by simp only [RawMachine.step, hc, ite_false, hb,
            RawMachine.output, RawMachine.state, RawState.emitByte], by simpa using Nat.one_le_iff_ne_zero.mpr hc⟩
  | dynamicTables last parser state =>
    cases hp : Parser.run fuel parser state.reservoir with
    | done pair rest =>
      obtain ⟨litLen, dist⟩ := pair
      exact ⟨[], by simp only [RawMachine.step, hp, RawMachine.output,
        RawMachine.state, RawState.ofTokenMachine, TokenMachine.start,
        TokenMachine.output, List.append_nil], Nat.zero_le _⟩
    | error err rest | needInput next rest | yield next rest =>
      exact ⟨[], by simp only [RawMachine.step, hp, RawMachine.output,
        RawMachine.state, List.append_nil], Nat.zero_le _⟩
  | symbols last litLen dist token =>
    obtain ⟨emitted, hout, hbound⟩ := token_step_extension token fuel capacity
    refine ⟨emitted, ?_, hbound⟩
    change (RawMachine.acceptToken last litLen dist (token.step fuel capacity)).output =
      token.output ++ emitted
    rw [acceptToken_output]
    exact hout
  | done state | bad err state => exact ⟨[], (List.append_nil _).symm, Nat.zero_le _⟩

theorem step_output (version : Version) (machine : RawMachine) (fuel capacity : Nat) :
    (RawMachine.step version machine fuel capacity).output =
      machine.output ++ stepEmitted version machine fuel capacity := by
  obtain ⟨emitted, hout, _⟩ := step_extension version machine fuel capacity
  simp only [stepEmitted, hout, List.drop_left]

theorem step_emitted_capacity (version : Version) (machine : RawMachine) (fuel capacity : Nat) :
    (stepEmitted version machine fuel capacity).length ≤ capacity := by
  obtain ⟨emitted, hout, hbound⟩ := step_extension version machine fuel capacity
  simpa only [stepEmitted, hout, List.drop_left] using hbound

/-- Incremental Adler/CRC update using exactly the bytes emitted by this step. -/
theorem step_checksum (kind : Protocol.ChecksumKind) (version : Version)
    (machine : RawMachine) (fuel capacity : Nat) :
    Checksums.update kind (Checksums.checksum kind machine.output)
        (stepEmitted version machine fuel capacity) =
      Checksums.checksum kind (RawMachine.step version machine fuel capacity).output := by
  rw [Checksums.update_prefix, ← step_output]

theorem call_output (version : Version) (machine : RawMachine) (call : RawMachine.Call) :
    (RawMachine.applyCall version machine call).output =
      machine.output ++ callEmitted version machine call := by
  simpa only [RawMachine.applyCall, callEmitted, RawMachine.feed_output] using
    step_output version (machine.feed call.input) call.schedulerFuel call.capacity

theorem call_emitted_capacity (version : Version) (machine : RawMachine) (call : RawMachine.Call) :
    (callEmitted version machine call).length ≤ call.capacity :=
  step_emitted_capacity version (machine.feed call.input) call.schedulerFuel call.capacity

theorem call_checksum (kind : Protocol.ChecksumKind) (version : Version)
    (machine : RawMachine) (call : RawMachine.Call) :
    Checksums.update kind (Checksums.checksum kind machine.output) (callEmitted version machine call) =
      Checksums.checksum kind (RawMachine.applyCall version machine call).output := by
  rw [Checksums.update_prefix, ← call_output]

/-- Output extension composes for arbitrary finite schedules, even schedules
that suspend, fail, or supply no output capacity. -/
theorem run_extension (version : Version) (machine : RawMachine) (calls : List RawMachine.Call) :
    ∃ emitted, (RawMachine.runCalls version machine calls).output = machine.output ++ emitted ∧
      emitted.length ≤ (calls.map RawMachine.Call.capacity).sum := by
  induction calls generalizing machine with
  | nil => exact ⟨[], (List.append_nil _).symm, Nat.le_refl _⟩
  | cons call calls ih =>
    obtain ⟨later, hlater, hbound⟩ := ih (RawMachine.applyCall version machine call)
    refine ⟨callEmitted version machine call ++ later, ?_, ?_⟩
    · change (RawMachine.runCalls version (RawMachine.applyCall version machine call) calls).output = _
      rw [hlater, call_output, List.append_assoc]
    · simp only [List.length_append, List.map_cons, List.sum_cons]
      exact Nat.add_le_add (call_emitted_capacity version machine call) hbound

theorem run_output (version : Version) (machine : RawMachine) (calls : List RawMachine.Call) :
    (RawMachine.runCalls version machine calls).output =
      machine.output ++ runEmitted version machine calls := by
  obtain ⟨emitted, hout, _⟩ := run_extension version machine calls
  simp only [runEmitted, hout, List.drop_left]

theorem run_emitted_capacity (version : Version) (machine : RawMachine) (calls : List RawMachine.Call) :
    (runEmitted version machine calls).length ≤ (calls.map RawMachine.Call.capacity).sum := by
  obtain ⟨emitted, hout, hbound⟩ := run_extension version machine calls
  simpa only [runEmitted, hout, List.drop_left] using hbound

/-- Iterating real emission increments computes the checksum of the final
logical output. No completed decoding or successful input premise is needed. -/
theorem runChecksum_correct (kind : Protocol.ChecksumKind) (version : Version)
    (machine : RawMachine) (calls : List RawMachine.Call) :
    runChecksum kind version machine (Checksums.checksum kind machine.output) calls =
      Checksums.checksum kind (RawMachine.runCalls version machine calls).output := by
  induction calls generalizing machine with
  | nil => rfl
  | cons call calls ih =>
    simp only [runChecksum, call_checksum]
    exact ih (RawMachine.applyCall version machine call)

/-- A nonzero stored-byte step emits exactly A; zero capacity emits nothing. -/
theorem stored_emission_checked :
    stepEmitted .v131 RawMachine.storedOneReady 8 1 = [65] ∧
      stepEmitted .develop RawMachine.storedOneReady 8 0 = [] := by
  exact ⟨rfl, rfl⟩

end Silmaril.Formats.Compression.Inflate.Stream.RawEmission
