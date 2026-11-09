module

public import Silmaril.Formats.Compression.Inflate.Stream.ParserBridge
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.ParserPhases
public import Mathlib.CategoryTheory.Discrete.Basic

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.ParserBridge`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

theorem Reservoir.readerFeed_append (reader : LSBReader) (first second : List UInt8) :
    Reservoir.readerFeed (Reservoir.readerFeed reader first) second =
      Reservoir.readerFeed reader (first ++ second) := by
  simp [Reservoir.readerFeed, List.append_assoc]

/-- Resumption preserves the continuation observation under every further
input extension; a result can therefore be resumed repeatedly. -/
theorem RunResult.resume_correct_feed {α : Type} (result : RunResult α)
    (fuel : Nat) (added : List UInt8) {reader : LSBReader}
    (h : Reservoir.Normalizes result.state reader) :
    ∃ rest, Reservoir.Normalizes (result.resume fuel added).state rest ∧
      ∀ future, result.observe (Reservoir.readerFeed reader (added ++ future)) =
        (result.resume fuel added).observe (Reservoir.readerFeed rest future) := by
  cases result with
  | done value state =>
    refine ⟨Reservoir.readerFeed reader added, h.feed added, ?_⟩
    intro future
    simp only [resume, observe, Reservoir.readerFeed_append]
  | error err state =>
    exact ⟨Reservoir.readerFeed reader added, h.feed added, fun _ => rfl⟩
  | needInput continuation state =>
    obtain ⟨rest, hrest, observations⟩ := Parser.run_correct_feed fuel continuation (h.feed added)
    refine ⟨rest, hrest, ?_⟩
    intro future
    simpa only [observe, resume, Reservoir.readerFeed, List.append_assoc, RunResult.state]
      using observations future
  | yield continuation state =>
    obtain ⟨rest, hrest, observations⟩ := Parser.run_correct_feed fuel continuation (h.feed added)
    refine ⟨rest, hrest, ?_⟩
    intro future
    simpa only [observe, resume, Reservoir.readerFeed, List.append_assoc, RunResult.state]
      using observations future

theorem RunResult.resume_correct {α : Type} (result : RunResult α)
    (fuel : Nat) (added : List UInt8) {reader : LSBReader}
    (h : Reservoir.Normalizes result.state reader) :
    ∃ rest, Reservoir.Normalizes (result.resume fuel added).state rest ∧
      result.observe (Reservoir.readerFeed reader added) =
        (result.resume fuel added).observe rest := by
  obtain ⟨rest, hrest, observations⟩ := result.resume_correct_feed fuel added h
  exact ⟨rest, hrest, by simpa only [List.append_nil, Reservoir.readerFeed_nil] using observations []⟩

theorem Parser.run_resume_correct_feed {α : Type} (firstFuel nextFuel : Nat)
    (parser : Parser α) (added : List UInt8) {state : Reservoir} {reader : LSBReader}
    (h : Reservoir.Normalizes state reader) :
    ∃ rest, Reservoir.Normalizes ((Parser.run firstFuel parser state).resume nextFuel added).state rest ∧
      ∀ future, parser.eval (Reservoir.readerFeed reader (added ++ future)) =
        ((Parser.run firstFuel parser state).resume nextFuel added).observe
          (Reservoir.readerFeed rest future) := by
  obtain ⟨middle, hmiddle, first⟩ := Parser.run_correct_feed firstFuel parser h
  obtain ⟨rest, hrest, second⟩ :=
    (Parser.run firstFuel parser state).resume_correct_feed nextFuel added hmiddle
  exact ⟨rest, hrest, fun future => (first (added ++ future)).trans (second future)⟩

namespace ParserBridge

theorem token_run (litLen dist : HuffmanTable) (fuel : Nat)
    {state : Reservoir} {reader : LSBReader} (h : Reservoir.Normalizes state reader) :
    ∃ rest, Reservoir.Normalizes (Parser.run fuel (ParserPhases.token litLen dist) state).state rest ∧
      ∀ added, Manual.parseToken litLen dist (Reservoir.readerFeed reader added) =
        (Parser.run fuel (ParserPhases.token litLen dist) state).observe
          (Reservoir.readerFeed rest added) := by
  simpa only [ParserPhases.token_eval] using
    Parser.run_correct_feed fuel (ParserPhases.token litLen dist) h

theorem storedHeader_run (fuel : Nat)
    {state : Reservoir} {reader : LSBReader} (h : Reservoir.Normalizes state reader) :
    ∃ rest, Reservoir.Normalizes (Parser.run fuel ParserPhases.storedHeader state).state rest ∧
      ∀ added, Manual.readStoredHeader (Reservoir.readerFeed reader added) =
        (Parser.run fuel ParserPhases.storedHeader state).observe
          (Reservoir.readerFeed rest added) := by
  simpa only [ParserPhases.storedHeader_eval] using
    Parser.run_correct_feed fuel ParserPhases.storedHeader h

theorem stored_run (fuel : Nat)
    {state : Reservoir} {reader : LSBReader} (h : Reservoir.Normalizes state reader) :
    ∃ rest, Reservoir.Normalizes (Parser.run fuel ParserPhases.stored state).state rest ∧
      ∀ added, Deflate.decompressStored (Reservoir.readerFeed reader added) =
        (Parser.run fuel ParserPhases.stored state).observe (Reservoir.readerFeed rest added) := by
  simpa only [ParserPhases.stored_eval, Manual.decompressStored_eq] using
    Parser.run_correct_feed fuel ParserPhases.stored h

theorem dynamicTables_run (fuel : Nat)
    {state : Reservoir} {reader : LSBReader} (h : Reservoir.Normalizes state reader) :
    ∃ rest, Reservoir.Normalizes (Parser.run fuel ParserPhases.dynamicTables state).state rest ∧
      ∀ added, dynamicTablesSpec (Reservoir.readerFeed reader added) =
        (Parser.run fuel ParserPhases.dynamicTables state).observe
          (Reservoir.readerFeed rest added) := by
  obtain ⟨rest, hrest, observations⟩ := Parser.run_correct_feed fuel ParserPhases.dynamicTables h
  refine ⟨rest, hrest, ?_⟩
  intro added
  have observation := observations added
  rw [ParserPhases.dynamicTables_eval] at observation
  cases result : Deflate.readDynamicTables (Reservoir.readerFeed reader added) with
  | error err => simpa only [dynamicTablesSpec, result] using observation
  | ok pair =>
    rcases pair with ⟨literals, distances, next⟩
    simpa only [dynamicTablesSpec, result] using observation

/-- Scheduler fuel and the format specification's token fuel are independent. -/
theorem symbols_run (litLen dist : HuffmanTable) (schedulerFuel tokenFuel : Nat)
    (output : List UInt8) {state : Reservoir} {reader : LSBReader}
    (h : Reservoir.Normalizes state reader) :
    ∃ rest, Reservoir.Normalizes
        (Parser.run schedulerFuel (ParserPhases.symbols litLen dist tokenFuel output) state).state rest ∧
      ∀ added, Deflate.decodeSymbolsFuel litLen dist tokenFuel
          (Reservoir.readerFeed reader added) output =
        (Parser.run schedulerFuel (ParserPhases.symbols litLen dist tokenFuel output) state).observe
          (Reservoir.readerFeed rest added) := by
  simpa only [ParserPhases.symbols_eval] using
    Parser.run_correct_feed schedulerFuel (ParserPhases.symbols litLen dist tokenFuel output) h

/-! ## Kernel-checked split-input executions -/

theorem storedHeader_split_inside_len :
    match headerLenPrefix with
    | .needInput _ state => state = ⟨3, 8, [], 0⟩
    | _ => False := by rfl

theorem storedHeader_split_inside_nlen :
    match headerNlenPrefix with
    | .needInput _ state => state = ⟨0xfc, 8, [], 16⟩
    | _ => False := by rfl

theorem storedHeader_three_chunks :
    headerNlenPrefix.resume 8 [0xff] = .done 3 ⟨0, 0, [], 32⟩ := rfl

theorem storedHeader_scheduler_yields :
    match headerYield with
    | .yield _ state => state = Reservoir.ofBytes [3, 0, 0xfc, 0xff]
    | _ => False := by rfl

theorem storedHeader_yield_resume :
    headerYield.resume 8 [] = .done 3 ⟨0, 0, [], 32⟩ := rfl

theorem token_split_inside_code :
    match tokenPrefix with
    | .needInput _ state => state = ⟨0, 0, [], 8⟩
    | _ => False := by rfl

theorem token_code_resume :
    tokenPrefix.resume 32 [0] = .done (.literal 144) ⟨0, 7, [], 9⟩ := rfl

end ParserBridge
end Silmaril.Formats.Compression.Inflate.Stream
