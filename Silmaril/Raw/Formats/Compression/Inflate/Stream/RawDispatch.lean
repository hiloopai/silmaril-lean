module

public import Silmaril.Raw.Formats.Compression.Inflate.Stream.RawSemantics

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.RawSemantics

open Silmaril.Formats.Compression

/-!
# Compositional raw-controller dispatch

Block completion, block-kind dispatch, and token acceptance preserve the raw
continuation meaning. The normalization witness changes only when final-block
padding is removed. Every equality remains valid under future input extension.
These are mathematical controller laws, not C/Core execution correspondence.
-/

theorem finishBlock_correct (last : Bool) (state : RawState) (reader : LSBReader)
    (hnorm : Reservoir.Normalizes state.reservoir reader)
    (hrep : state.window.Represents state.output) :
    ∃ nextReader,
      Reservoir.Normalizes (RawMachine.finishBlock last state).reservoir nextReader ∧
      WellFormed (RawMachine.finishBlock last state) nextReader ∧
      ∀ future, afterBlock last state.output (Reservoir.readerFeed reader future) =
        denote (RawMachine.finishBlock last state) (Reservoir.readerFeed nextReader future) := by
  cases last with
  | true =>
    refine ⟨reader.alignToByte, hnorm.byteBits, ⟨hrep, trivial⟩, fun _ => rfl⟩
  | false =>
    refine ⟨reader, hnorm, ⟨hrep, trivial⟩, ?_⟩
    intro future
    exact format_unfold (Reservoir.readerFeed reader future) state.output

theorem fixed_denote (last : Bool) (state : RawState) (reader : LSBReader) :
    denote (RawMachine.fixed last state) reader =
      afterDecodedBlock last
        (match Deflate.fixedLitLenTable, Deflate.fixedDistTable with
        | some litLen, some dist => Deflate.decodeSymbol litLen dist reader state.output
        | _, _ => .error .badFixedTable) := by
  unfold RawMachine.fixed
  cases hl : Deflate.fixedLitLenTable with
  | none => cases Deflate.fixedDistTable <;> rfl
  | some litLen =>
    cases hd : Deflate.fixedDistTable with
    | none => rfl
    | some dist =>
      change afterToken last litLen dist
        (TokenContinuation.denote
          (TokenMachine.start litLen dist state.reservoir state.window state.output) reader) = _
      rw [TokenContinuation.start_denote, Manual.decodeStep_eq_spec]
      exact afterToken_unfold last litLen dist reader state.output

set_option maxRecDepth 4096 in
theorem dispatch_denote (version : Version) (kind : Nat) (last : Bool)
    (state : RawState) (reader : LSBReader) :
    denote (RawMachine.dispatch version kind last state) reader =
      afterDecodedBlock last (Deflate.decompressBlockBody kind reader state.output) := by
  rw [RawMachine.dispatch_eq version .v131]
  change denote (RawMachine.dispatch131 kind last state) reader = _
  by_cases h0 : kind = 0
  · subst kind
    simp only [RawMachine.dispatch131, ↓reduceIte, denote]
    rw [← StoredContinuation.storedHeader_copy_eq_blockBody state.output reader]
    cases ParserPhases.storedHeader.eval reader with
    | error err => rfl
    | ok pair => cases pair; rfl
  · by_cases h1 : kind = 1
    · subst kind
      simp only [RawMachine.dispatch131, Deflate.decompressBlockBody,
        Nat.reduceEqDiff, ↓reduceIte]
      exact fixed_denote last state reader
    · by_cases h2 : kind = 2
      · subst kind
        simp only [RawMachine.dispatch131, Deflate.decompressBlockBody,
          Nat.reduceEqDiff, ↓reduceIte, denote, ParserPhases.dynamicTables_eval]
        cases Deflate.readDynamicTables reader with
        | error err => rfl
        | ok triple => obtain ⟨litLen, dist, rest⟩ := triple; rfl
      · simp only [RawMachine.dispatch131, Deflate.decompressBlockBody,
          h0, h1, h2, ite_false, denote, afterDecodedBlock]

theorem fixed_wellFormed (last : Bool) (state : RawState) (reader : LSBReader)
    (hrep : state.window.Represents state.output) :
    WellFormed (RawMachine.fixed last state) reader := by
  unfold RawMachine.fixed
  cases Deflate.fixedLitLenTable with
  | none => cases Deflate.fixedDistTable <;> exact ⟨hrep, trivial⟩
  | some litLen =>
    cases Deflate.fixedDistTable with
    | none => exact ⟨hrep, trivial⟩
    | some dist =>
      exact ⟨hrep, TokenContinuation.start_wellFormed litLen dist
        state.reservoir state.window state.output reader hrep⟩

theorem dispatch_wellFormed (version : Version) (kind : Nat) (last : Bool)
    (state : RawState) (reader : LSBReader) (hrep : state.window.Represents state.output) :
    WellFormed (RawMachine.dispatch version kind last state) reader := by
  rw [RawMachine.dispatch_eq version .v131]
  change WellFormed (RawMachine.dispatch131 kind last state) reader
  unfold RawMachine.dispatch131
  split
  · exact ⟨hrep, trivial⟩
  · split
    · exact fixed_wellFormed last state reader hrep
    · split <;> exact ⟨hrep, trivial⟩

theorem acceptToken_correct (last : Bool) (litLen dist : HuffmanTable)
    (machine : TokenMachine) (reader : LSBReader)
    (hnorm : Reservoir.Normalizes machine.reservoir reader)
    (htoken : TokenContinuation.WellFormed machine reader) :
    ∃ rest,
      Reservoir.Normalizes (RawMachine.acceptToken last litLen dist machine).reservoir rest ∧
      WellFormed (RawMachine.acceptToken last litLen dist machine) rest ∧
      ∀ future, afterToken last litLen dist
        (TokenContinuation.denote machine (Reservoir.readerFeed reader future)) =
        denote (RawMachine.acceptToken last litLen dist machine) (Reservoir.readerFeed rest future) := by
  cases machine with
  | parsing parser state history bytes =>
    exact ⟨reader, hnorm, ⟨htoken.1, htoken⟩, fun _ => rfl⟩
  | emitting state pending =>
    exact ⟨reader, hnorm, ⟨htoken.1, htoken⟩, fun _ => rfl⟩
  | error err state history bytes =>
    exact ⟨reader, hnorm, ⟨htoken, trivial⟩, fun _ => rfl⟩
  | done state completed =>
    obtain ⟨hvalid, flag, hphase⟩ := htoken
    cases flag with
    | true =>
      obtain ⟨rest, hrest, hwf, observations⟩ :=
        finishBlock_correct last ⟨state, completed.window, completed.output⟩ reader hnorm hvalid.1
      refine ⟨rest, ?_, ?_, ?_⟩
      · simpa only [RawMachine.acceptToken, hphase] using hrest
      · simpa only [RawMachine.acceptToken, hphase] using hwf
      · intro future
        rw [TokenContinuation.done_denote state completed (Reservoir.readerFeed reader future)
          true hphase]
        simpa only [afterToken, RawMachine.acceptToken, hphase, ↓reduceIte] using observations future
    | false =>
      refine ⟨reader, ?_, ?_, ?_⟩
      · simpa only [RawMachine.acceptToken, hphase, RawMachine.reservoir, RawMachine.state,
          RawState.ofTokenMachine, TokenMachine.reservoir, TokenMachine.start] using hnorm
      · simp only [RawMachine.acceptToken, hphase]
        exact ⟨hvalid.1, TokenContinuation.start_wellFormed litLen dist state
          completed.window completed.output reader hvalid.1⟩
      · intro future
        rw [TokenContinuation.done_denote state completed (Reservoir.readerFeed reader future)
          false hphase]
        simp only [afterToken, RawMachine.acceptToken, hphase, denote]
        rw [TokenContinuation.start_denote, Manual.decodeStep_eq_spec]
        exact (afterToken_unfold last litLen dist
          (Reservoir.readerFeed reader future) completed.output).symm

end Silmaril.Formats.Compression.Inflate.Stream.RawSemantics
