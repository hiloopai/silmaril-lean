module

public import Silmaril.Raw.Formats.Compression.Inflate.Stream.RawDispatch

/-!
# Whole raw controller step preservation

Every physical controller step preserves its logical remaining computation for
all later input. The representation invariant is maintained through partial
field reads, stored bytes, dynamic tables, pending literals and overlapping
matches. No semantic block/token fuel or declared final input length is required.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.RawStep

open Silmaril.Formats.Compression
open RawSemantics

theorem step_correct_feed (version : Version) (machine : RawMachine)
    (reader : LSBReader) (schedulerFuel capacity : Nat)
    (hnorm : Reservoir.Normalizes machine.reservoir reader)
    (hwf : WellFormed machine reader) :
    ∃ rest, Reservoir.Normalizes
        (RawMachine.step version machine schedulerFuel capacity).reservoir rest ∧
      WellFormed (RawMachine.step version machine schedulerFuel capacity) rest ∧
      ∀ future, denote machine (Reservoir.readerFeed reader future) =
        denote (RawMachine.step version machine schedulerFuel capacity)
          (Reservoir.readerFeed rest future) := by
  cases machine with
  | header parser state =>
    obtain ⟨nextReader, hn, observations⟩ := Parser.run_correct_feed schedulerFuel parser
      (show Reservoir.Normalizes state.reservoir reader from hnorm)
    cases hp : Parser.run schedulerFuel parser state.reservoir with
    | done parsed rest =>
      obtain ⟨last, kind⟩ := parsed
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [RawMachine.step, hp]
      refine ⟨nextReader, ?_, dispatch_wellFormed version kind last _ nextReader hwf.1, ?_⟩
      · simpa only [RawMachine.dispatch_reservoir] using hn
      · intro future
        simp only [denote, observations future]
        exact (dispatch_denote version kind last { state with reservoir := rest }
          (Reservoir.readerFeed nextReader future)).symm
    | error err rest =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [RawMachine.step, hp]
      refine ⟨nextReader, hn, ⟨hwf.1, trivial⟩, ?_⟩
      intro future
      simp only [denote, observations future]
    | needInput next rest =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [RawMachine.step, hp]
      refine ⟨nextReader, hn, ⟨hwf.1, trivial⟩, ?_⟩
      intro future
      simp only [denote, observations future]
    | yield next rest =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [RawMachine.step, hp]
      refine ⟨nextReader, hn, ⟨hwf.1, trivial⟩, ?_⟩
      intro future
      simp only [denote, observations future]
  | storedHeader last parser state =>
    obtain ⟨nextReader, hn, observations⟩ := Parser.run_correct_feed schedulerFuel parser
      (show Reservoir.Normalizes state.reservoir reader from hnorm)
    cases hp : Parser.run schedulerFuel parser state.reservoir with
    | done count rest =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [RawMachine.step, hp]
      refine ⟨nextReader, hn, ⟨hwf.1, trivial⟩, ?_⟩
      intro future
      simp only [denote, observations future]
    | error err rest =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [RawMachine.step, hp]
      refine ⟨nextReader, hn, ⟨hwf.1, trivial⟩, ?_⟩
      intro future
      simp only [denote, observations future]
    | needInput next rest =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [RawMachine.step, hp]
      refine ⟨nextReader, hn, ⟨hwf.1, trivial⟩, ?_⟩
      intro future
      simp only [denote, observations future]
    | yield next rest =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [RawMachine.step, hp]
      refine ⟨nextReader, hn, ⟨hwf.1, trivial⟩, ?_⟩
      intro future
      simp only [denote, observations future]
  | storedCopy last remaining state =>
    cases remaining with
    | zero =>
      simpa only [RawMachine.step, denote, Deflate.readStoredBytes, afterDecodedBlock] using
        finishBlock_correct last state reader hnorm hwf.1
    | succ count =>
      by_cases hc : capacity = 0
      · simp only [RawMachine.step, hc, ite_true]
        exact ⟨reader, hnorm, hwf, fun _ => rfl⟩
      · simp only [RawMachine.step, hc, ite_false]
        cases hb : Reservoir.readBits 8 state.reservoir with
        | needInput rest =>
          simp only
          refine ⟨reader, hnorm.readBits_needInput hb, ⟨hwf.1, trivial⟩, ?_⟩
          intro future
          rfl
        | value byte rest =>
          simp only
          obtain ⟨nextReader, hr, hn⟩ := hnorm.readBits hb
          refine ⟨nextReader, hn, ⟨?_, trivial⟩, ?_⟩
          · exact Window.push_represents state.window state.output (UInt8.ofNat byte) hwf.1
          · intro future
            simp only [denote, Deflate.readStoredBytes, LSBReader.readByte,
              Reservoir.readerFeed_readBits 8 hr future, RawState.emitByte]
  | dynamicTables last parser state =>
    obtain ⟨nextReader, hn, observations⟩ := Parser.run_correct_feed schedulerFuel parser
      (show Reservoir.Normalizes state.reservoir reader from hnorm)
    cases hp : Parser.run schedulerFuel parser state.reservoir with
    | done tables rest =>
      obtain ⟨litLen, dist⟩ := tables
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [RawMachine.step, hp]
      refine ⟨nextReader, hn, ?_, ?_⟩
      · exact ⟨hwf.1, TokenContinuation.start_wellFormed litLen dist rest
          state.window state.output nextReader hwf.1⟩
      · intro future
        simp only [denote, observations future, TokenContinuation.start_denote,
          Manual.decodeStep_eq_spec]
        exact (afterToken_unfold last litLen dist _ _).symm
    | error err rest =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [RawMachine.step, hp]
      refine ⟨nextReader, hn, ⟨hwf.1, trivial⟩, ?_⟩
      intro future
      simp only [denote, observations future]
    | needInput next rest =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [RawMachine.step, hp]
      refine ⟨nextReader, hn, ⟨hwf.1, trivial⟩, ?_⟩
      intro future
      simp only [denote, observations future]
    | yield next rest =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [RawMachine.step, hp]
      refine ⟨nextReader, hn, ⟨hwf.1, trivial⟩, ?_⟩
      intro future
      simp only [denote, observations future]
  | symbols last litLen dist token =>
    obtain ⟨middle, hm, hwm, tokenObservations⟩ :=
      TokenContinuation.step_correct_feed token reader schedulerFuel capacity hnorm hwf.2
    obtain ⟨rest, hn, hw, accepted⟩ :=
      acceptToken_correct last litLen dist (token.step schedulerFuel capacity) middle hm hwm
    refine ⟨rest, hn, hw, ?_⟩
    intro future
    change afterToken last litLen dist (TokenContinuation.denote token
      (Reservoir.readerFeed reader future)) = _
    rw [tokenObservations future]
    exact accepted future
  | done state => exact ⟨reader, hnorm, hwf, fun _ => rfl⟩
  | bad err state => exact ⟨reader, hnorm, hwf, fun _ => rfl⟩

end Silmaril.Formats.Compression.Inflate.Stream.RawStep
