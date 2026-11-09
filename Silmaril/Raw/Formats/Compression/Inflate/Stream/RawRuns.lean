module

public import Silmaril.Formats.Compression.Inflate.Stream.RawRuns
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.RawStep

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.RawRuns`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.RawRuns

open Silmaril.Formats.Compression

theorem deliveredInput_nil : deliveredInput [] = [] := rfl

theorem deliveredInput_cons (call : RawMachine.Call) (calls : List RawMachine.Call) :
    deliveredInput (call :: calls) = call.input ++ deliveredInput calls := rfl

theorem deliveredInput_append (first second : List RawMachine.Call) :
    deliveredInput (first ++ second) = deliveredInput first ++ deliveredInput second :=
  List.flatMap_append

/-- Feeding changes only physical input storage. Denotation always receives
its logical reader explicitly, so the reservoir itself is not interpreted twice. -/
theorem feed_denote (machine : RawMachine) (reader : LSBReader) (added : List UInt8) :
    RawSemantics.denote (machine.feed added) reader = RawSemantics.denote machine reader := by
  cases machine <;> simp only [RawMachine.feed, RawState.feed, RawSemantics.denote,
    TokenContinuation.feed_denote]

theorem feed_wellFormed (machine : RawMachine) (reader : LSBReader) (added : List UInt8)
    (h : RawSemantics.WellFormed machine reader) :
    RawSemantics.WellFormed (machine.feed added) (Reservoir.readerFeed reader added) := by
  refine ⟨?_, ?_⟩
  · rw [RawMachine.feed_window, RawMachine.feed_output]
    exact h.1
  · cases machine with
    | symbols last litLen dist token => exact TokenContinuation.feed_wellFormed token reader added h.2
    | header parser state | storedHeader last parser state | storedCopy last remaining state
      | dynamicTables last parser state | done state | bad err state => trivial

theorem feed_normalizes (machine : RawMachine) (reader : LSBReader) (added : List UInt8)
    (h : Reservoir.Normalizes machine.reservoir reader) :
    Reservoir.Normalizes (machine.feed added).reservoir (Reservoir.readerFeed reader added) := by
  rw [RawMachine.feed_reservoir]
  exact h.feed added

theorem start_wellFormed (initial : List UInt8) (reader : LSBReader) :
    RawSemantics.WellFormed (RawMachine.start initial) reader := by
  simp only [RawSemantics.WellFormed, RawMachine.start, RawMachine.window,
    RawMachine.output, RawMachine.state, Window.Represents, Window.ofOutput]
  trivial

theorem start_normalizes (initial : List UInt8) :
    Reservoir.Normalizes (RawMachine.start initial).reservoir (Blocks.initialReader initial) :=
  Blocks.ofBytes_normalizes initial

/-- Initial input and all later input are viewed as one logical byte stream. -/
theorem start_denote (initial added : List UInt8) :
    RawSemantics.denote (RawMachine.start initial)
        (Reservoir.readerFeed (Blocks.initialReader initial) added) =
      RawSemantics.format (Blocks.initialReader (initial ++ added)) [] := by
  exact (RawSemantics.format_unfold (Blocks.initialReader (initial ++ added)) []).symm

/-- The shared byte-oriented raw decoder observes the suffix after final-byte
padding is discarded. Alignment retains all complete unread bytes. -/
theorem format_inputView (input : List UInt8) :
    Blocks.inputView (RawSemantics.format (Blocks.initialReader input) []) =
      Deflate.deflateTake input := by
  simp only [RawSemantics.format, RawSemantics.alignResult, Blocks.inputView,
    Deflate.deflateTake, Blocks.initialReader]
  cases Deflate.decompressBlocks ((LSBReader.mk 0 0 input 0).bitsLeft + 1)
      (LSBReader.mk 0 0 input 0) [] <;> rfl

theorem runCalls_correct_feed_of_step (version : Version) (stepLaw : StepLaw version)
    (machine : RawMachine) (reader : LSBReader) (calls : List RawMachine.Call)
    (hnorm : Reservoir.Normalizes machine.reservoir reader)
    (hwf : RawSemantics.WellFormed machine reader) :
    ∃ rest, Reservoir.Normalizes (RawMachine.runCalls version machine calls).reservoir rest ∧
      RawSemantics.WellFormed (RawMachine.runCalls version machine calls) rest ∧ ∀ future,
      RawSemantics.denote machine (Reservoir.readerFeed reader (deliveredInput calls ++ future)) =
        RawSemantics.denote (RawMachine.runCalls version machine calls) (Reservoir.readerFeed rest future) := by
  induction calls generalizing machine reader with
  | nil =>
    exact ⟨reader, hnorm, hwf, fun _ => rfl⟩
  | cons call calls ih =>
    obtain ⟨middle, hmiddle, hwfmiddle, first⟩ :=
      stepLaw (machine.feed call.input) (Reservoir.readerFeed reader call.input)
        call.schedulerFuel call.capacity (feed_normalizes machine reader call.input hnorm)
        (feed_wellFormed machine reader call.input hwf)
    obtain ⟨rest, hrest, hwfrest, later⟩ := ih _ middle hmiddle hwfmiddle
    refine ⟨rest, hrest, hwfrest, ?_⟩
    intro future
    change RawSemantics.denote machine
        (Reservoir.readerFeed reader (call.input ++ deliveredInput calls ++ future)) = _
    rw [List.append_assoc, ← Reservoir.readerFeed_append,
      ← feed_denote machine _ call.input, first (deliveredInput calls ++ future)]
    exact later future

theorem start_runCalls_correct_feed_of_step (version : Version) (stepLaw : StepLaw version)
    (initial : List UInt8) (calls : List RawMachine.Call) :
    ∃ rest, Reservoir.Normalizes (RawMachine.runCalls version (RawMachine.start initial) calls).reservoir rest ∧
      RawSemantics.WellFormed (RawMachine.runCalls version (RawMachine.start initial) calls) rest ∧ ∀ future,
      RawSemantics.format (Blocks.initialReader (initial ++ deliveredInput calls ++ future)) [] =
        RawSemantics.denote (RawMachine.runCalls version (RawMachine.start initial) calls)
          (Reservoir.readerFeed rest future) := by
  obtain ⟨rest, hrest, hwfrest, observations⟩ :=
    runCalls_correct_feed_of_step version stepLaw (RawMachine.start initial) (Blocks.initialReader initial)
      calls (start_normalizes initial) (start_wellFormed initial _)
  refine ⟨rest, hrest, hwfrest, ?_⟩
  intro future
  simpa only [start_denote, List.append_assoc] using observations future

/-- A successful suffix theorem is conditional on the actual controller being
done, rather than on an assumed adequate scheduler or output-space budget. -/
theorem done_correct_feed_of_step (version : Version) (stepLaw : StepLaw version)
    (initial : List UInt8) (calls : List RawMachine.Call) (completed : RawState)
    (hdone : RawMachine.runCalls version (RawMachine.start initial) calls = .done completed) :
    ∃ rest, Reservoir.Normalizes completed.reservoir rest ∧ ∀ future,
      Deflate.deflateTake (initial ++ deliveredInput calls ++ future) =
        .ok (completed.output, rest.input ++ future) := by
  obtain ⟨rest, hrest, _, observations⟩ := start_runCalls_correct_feed_of_step version stepLaw initial calls
  rw [hdone] at hrest observations
  refine ⟨rest, hrest, ?_⟩
  intro future
  have observed := congrArg Blocks.inputView (observations future)
  rw [format_inputView] at observed
  exact observed

/-- Arbitrary finite schedules preserve the raw computation for either
version, including schedules that suspend before any block has completed. -/
theorem runCalls_correct_feed (version : Version)
    (machine : RawMachine) (reader : LSBReader) (calls : List RawMachine.Call)
    (hnorm : Reservoir.Normalizes machine.reservoir reader)
    (hwf : RawSemantics.WellFormed machine reader) :
    ∃ rest, Reservoir.Normalizes (RawMachine.runCalls version machine calls).reservoir rest ∧
      RawSemantics.WellFormed (RawMachine.runCalls version machine calls) rest ∧ ∀ future,
      RawSemantics.denote machine (Reservoir.readerFeed reader (deliveredInput calls ++ future)) =
        RawSemantics.denote (RawMachine.runCalls version machine calls) (Reservoir.readerFeed rest future) :=
  runCalls_correct_feed_of_step version (RawStep.step_correct_feed version) machine reader calls hnorm hwf

theorem start_runCalls_correct_feed (version : Version)
    (initial : List UInt8) (calls : List RawMachine.Call) :
    ∃ rest, Reservoir.Normalizes (RawMachine.runCalls version (RawMachine.start initial) calls).reservoir rest ∧
      RawSemantics.WellFormed (RawMachine.runCalls version (RawMachine.start initial) calls) rest ∧ ∀ future,
      RawSemantics.format (Blocks.initialReader (initial ++ deliveredInput calls ++ future)) [] =
        RawSemantics.denote (RawMachine.runCalls version (RawMachine.start initial) calls)
          (Reservoir.readerFeed rest future) :=
  start_runCalls_correct_feed_of_step version (RawStep.step_correct_feed version) initial calls

/-- Even an unfinished schedule denotes exactly the shared byte-oriented raw
format decoder on all delivered bytes and arbitrary future input. -/
theorem start_take_correct_feed (version : Version) (initial : List UInt8)
    (calls : List RawMachine.Call) :
    ∃ rest, Reservoir.Normalizes (RawMachine.runCalls version (RawMachine.start initial) calls).reservoir rest ∧
      RawSemantics.WellFormed (RawMachine.runCalls version (RawMachine.start initial) calls) rest ∧ ∀ future,
      Deflate.deflateTake (initial ++ deliveredInput calls ++ future) =
        Blocks.inputView (RawSemantics.denote
          (RawMachine.runCalls version (RawMachine.start initial) calls) (Reservoir.readerFeed rest future)) := by
  obtain ⟨rest, hrest, hwfrest, observations⟩ := start_runCalls_correct_feed version initial calls
  refine ⟨rest, hrest, hwfrest, ?_⟩
  intro future
  have observed := congrArg Blocks.inputView (observations future)
  rwa [format_inputView] at observed

/-- Actual completion yields exact output and suffix correctness. This theorem
has no premise about the number of calls, total capacities, future input length
or success of a separate mathematical decoding run. -/
theorem done_correct_feed (version : Version) (initial : List UInt8)
    (calls : List RawMachine.Call) (completed : RawState)
    (hdone : RawMachine.runCalls version (RawMachine.start initial) calls = .done completed) :
    ∃ rest, Reservoir.Normalizes completed.reservoir rest ∧ ∀ future,
      Deflate.deflateTake (initial ++ deliveredInput calls ++ future) =
        .ok (completed.output, rest.input ++ future) :=
  done_correct_feed_of_step version (RawStep.step_correct_feed version) initial calls completed hdone

end Silmaril.Formats.Compression.Inflate.Stream.RawRuns
