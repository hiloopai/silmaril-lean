module

public import Silmaril.Formats.Compression.Inflate.Stream.RawMachine
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.Blocks
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.TokenMachine

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.RawMachine`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

namespace RawState

theorem feed_valid {state : RawState} (h : state.Valid) (added : List UInt8) :
    (state.feed added).Valid := ⟨Reservoir.feed_valid h.1 added, h.2⟩

theorem emitByte_valid {state : RawState} (h : state.Valid) {rest : Reservoir}
    (hrest : rest.Valid) (byte : UInt8) : (state.emitByte rest byte).Valid :=
  ⟨hrest, Window.push_represents state.window state.output byte h.2⟩

end RawState

namespace RawMachine

theorem start_valid (bytes : List UInt8) : (start bytes).state.Valid := by
  simp only [start, state, RawState.Valid]
  exact ⟨Reservoir.ofBytes_valid bytes, rfl⟩

theorem finishBlock_window (last : Bool) (state : RawState) :
    (finishBlock last state).window = state.window := by
  cases last <;> rfl

theorem finishBlock_output (last : Bool) (state : RawState) :
    (finishBlock last state).output = state.output := by
  cases last <;> rfl

theorem finishBlock_reservoir (last : Bool) (state : RawState) :
    (finishBlock last state).reservoir =
      if last then state.reservoir.byteBits else state.reservoir := by
  cases last <;> rfl

theorem fixed_state (last : Bool) (state : RawState) :
    (fixed last state).state = state := by
  unfold fixed
  generalize Deflate.fixedLitLenTable = litLen
  generalize Deflate.fixedDistTable = dist
  cases litLen <;> cases dist <;> cases state <;> rfl

theorem dispatch131_state (kind : Nat) (last : Bool) (state : RawState) :
    (dispatch131 kind last state).state = state := by
  unfold dispatch131
  split
  · rfl
  · split
    · exact fixed_state last state
    · split <;> rfl

theorem dispatchDevelop_state (kind : Nat) (last : Bool) (state : RawState) :
    (dispatchDevelop kind last state).state = state := by
  cases kind with
  | zero => rfl
  | succ kind =>
    cases kind with
    | zero => exact fixed_state last state
    | succ kind => cases kind <;> rfl

/-- Dispatch changes the mode, never the reservoir, history, or output trace. -/
theorem dispatch_state (version : Version) (kind : Nat) (last : Bool) (state : RawState) :
    (dispatch version kind last state).state = state := by
  cases version with
  | v131 => exact dispatch131_state kind last state
  | develop => exact dispatchDevelop_state kind last state

theorem dispatch_reservoir (version : Version) (kind : Nat) (last : Bool) (state : RawState) :
    (dispatch version kind last state).reservoir = state.reservoir :=
  congrArg RawState.reservoir (dispatch_state version kind last state)

theorem dispatch_window (version : Version) (kind : Nat) (last : Bool) (state : RawState) :
    (dispatch version kind last state).window = state.window :=
  congrArg RawState.window (dispatch_state version kind last state)

theorem dispatch_output (version : Version) (kind : Nat) (last : Bool) (state : RawState) :
    (dispatch version kind last state).output = state.output :=
  congrArg RawState.output (dispatch_state version kind last state)

/-- The independently written version dispatchers implement the same four
abstract block cases. This does not identify their source-level executions. -/
theorem dispatch131_eq_dispatchDevelop (kind : Nat) (last : Bool) (state : RawState) :
    dispatch131 kind last state = dispatchDevelop kind last state := by
  cases kind with
  | zero => simp only [dispatch131, dispatchDevelop, ↓reduceIte]
  | succ kind =>
    cases kind with
    | zero => simp only [dispatch131, dispatchDevelop, Nat.reduceEqDiff, ↓reduceIte]
    | succ kind =>
      cases kind <;> simp [dispatch131, dispatchDevelop]

theorem dispatch_eq (first second : Version) (kind : Nat) (last : Bool) (state : RawState) :
    dispatch first kind last state = dispatch second kind last state := by
  cases first <;> cases second
  · rfl
  · exact dispatch131_eq_dispatchDevelop kind last state
  · exact (dispatch131_eq_dispatchDevelop kind last state).symm
  · rfl

/-- Version-specific entry points share this mathematical scheduling behavior.
Each version still needs its own correspondence proof for the compiled source. -/
theorem step_eq (first second : Version) (machine : RawMachine) (schedulerFuel capacity : Nat) :
    step first machine schedulerFuel capacity = step second machine schedulerFuel capacity := by
  cases machine with
  | header continuation state =>
    simp only [step]
    cases Parser.run schedulerFuel continuation state.reservoir with
    | done pair rest =>
      obtain ⟨last, kind⟩ := pair
      exact dispatch_eq first second kind last { state with reservoir := rest }
    | error _ _ | needInput _ _ | yield _ _ => rfl
  | storedHeader _ _ _ | storedCopy _ _ _ | dynamicTables _ _ _ | symbols _ _ _ _
    | done _ | bad _ _ => rfl

theorem applyCall_eq (first second : Version) (machine : RawMachine) (call : Call) :
    applyCall first machine call = applyCall second machine call :=
  step_eq first second (machine.feed call.input) call.schedulerFuel call.capacity

theorem runCalls_eq (first second : Version) (machine : RawMachine) (calls : List Call) :
    runCalls first machine calls = runCalls second machine calls := by
  induction calls generalizing machine with
  | nil => rfl
  | cons call calls ih =>
    change runCalls first (applyCall first machine call) calls =
      runCalls second (applyCall second machine call) calls
    rw [applyCall_eq first second]
    exact ih _

theorem feed_output (machine : RawMachine) (added : List UInt8) :
    (machine.feed added).output = machine.output := by
  cases machine <;> simp only [feed, output, state, RawState.feed,
    RawState.ofTokenMachine, TokenMachine.feed_output]

theorem feed_window (machine : RawMachine) (added : List UInt8) :
    (machine.feed added).window = machine.window := by
  cases machine <;> simp only [feed, window, state, RawState.feed,
    RawState.ofTokenMachine, TokenMachine.feed_window]

theorem feed_reservoir (machine : RawMachine) (added : List UInt8) :
    (machine.feed added).reservoir = machine.reservoir.feed added := by
  cases machine <;> simp only [feed, reservoir, state, RawState.feed,
    RawState.ofTokenMachine, TokenMachine.feed_reservoir]

theorem storedCopy_zero_capacity (version : Version) (last : Bool) (remaining : Nat)
    (state : RawState) (schedulerFuel : Nat) :
    step version (.storedCopy last (remaining + 1) state) schedulerFuel 0 =
      .storedCopy last (remaining + 1) state := rfl

theorem runCalls_append (version : Version) (machine : RawMachine) (first second : List Call) :
    runCalls version machine (first ++ second) =
      runCalls version (runCalls version machine first) second := by
  exact List.foldl_append

/-! ## A stored block through the actual controller -/

theorem storedOne_waits_for_output :
    step .v131 storedOneReady 8 0 = storedOneReady := rfl

theorem storedOne_copy_retains_history :
    match storedOneCopied with
    | .storedCopy true 0 state =>
      state.reservoir = ⟨0, 0, [], 48⟩ ∧ state.output = [65] ∧ state.window.bytes = [65]
    | _ => False := by exact ⟨rfl, rfl, rfl⟩

theorem storedOne_completes :
    step .v131 storedOneCopied 0 0 = .done ⟨⟨0, 0, [], 48⟩, ⟨[65]⟩, [65]⟩ := rfl

end RawMachine
end Silmaril.Formats.Compression.Inflate.Stream
