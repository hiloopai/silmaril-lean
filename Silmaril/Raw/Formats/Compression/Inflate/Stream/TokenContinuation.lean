module

public import Silmaril.Formats.Compression.Inflate.Stream.TokenContinuation
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.TokenMachine

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.TokenContinuation`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.TokenContinuation

open Silmaril.Formats.Compression

theorem token_parser_admissible (litLen dist : HuffmanTable) (reader : LSBReader) :
    ParserAdmissible (ParserPhases.token litLen dist) reader := by
  intro future token rest parsed
  cases token with
  | literal byte | endBlock => trivial
  | matchBytes length distance => exact TokenBounds.parser_match_bounds parsed

theorem ParserAdmissible.feed {parser : Parser Manual.Token} {reader : LSBReader}
    (h : ParserAdmissible parser reader) (added : List UInt8) :
    ParserAdmissible parser (Reservoir.readerFeed reader added) := by
  intro future token rest parsed
  rw [Reservoir.readerFeed_append] at parsed
  exact h (added ++ future) token rest parsed

/-- Enough output capacity gives the same final state, including all fields,
regardless of excess capacity. This is independent of history validity. -/
theorem advance_saturates (pending : TokenOutput) (capacity : Nat)
    (henough : pending.remaining ≤ capacity) :
    pending.advance capacity = pending.advance pending.remaining := by
  cases hp : pending.phase with
  | literal byte =>
    have hc : capacity ≠ 0 := by
      simp only [TokenOutput.remaining, hp] at henough
      omega
    simp only [TokenOutput.advance, TokenOutput.remaining, hp, ite_eq_right hc,
      Nat.one_ne_zero, ite_false]
  | matchBytes count distance =>
    have hc : count ≤ capacity := by simpa only [TokenOutput.remaining, hp] using henough
    simp only [TokenOutput.advance, hp, TokenOutput.remaining, TokenOutput.asMatch,
      PendingMatch.advance, Nat.min_eq_left hc, Nat.min_self]
  | endBlock | complete _ => simp only [TokenOutput.advance, hp]

theorem outputDenote_valid (pending : TokenOutput) (reader : LSBReader)
    (h : pending.Valid) :
    outputDenote pending reader =
      match (pending.advance pending.remaining).observe reader with
      | some result => .ok result
      | none => .error .decodeOverrun := by
  simp only [outputDenote, pending.step_ok pending.remaining h]
  rfl

/-- Partial copying preserves the completed-token meaning. Saturation plus
the exact output-buffer composition law avoids reparsing or recopying a prefix. -/
theorem outputDenote_advance (pending : TokenOutput) (capacity : Nat) (reader : LSBReader)
    (h : pending.Valid) :
    outputDenote (pending.advance capacity) reader = outputDenote pending reader := by
  rw [outputDenote_valid _ _ (pending.advance_valid capacity h), outputDenote_valid _ _ h]
  rw [pending.advance_add, pending.advance_remaining]
  have henough : pending.remaining ≤ capacity + (pending.remaining - min pending.remaining capacity) := by
    omega
  rw [advance_saturates pending _ henough]

theorem outputDenote_start (history : Window) (bytes : List UInt8) (token : Manual.Token)
    (reader : LSBReader) (hrep : history.Represents bytes) (hfits : TokenFitsHistory bytes token) :
    outputDenote (TokenOutput.start history bytes token) reader = Manual.applyToken bytes token reader := by
  rw [outputDenote_valid _ _ (TokenOutput.start_valid history bytes token hrep hfits)]
  have complete := TokenOutput.complete_eq_applyToken history bytes token reader (tokenLength token)
    hrep hfits (Nat.le_refl _)
  rw [TokenOutput.start_remaining]
  cases applied : Manual.applyToken bytes token reader with
  | error err => simp only [applied, Except.map] at complete; cases complete
  | ok result =>
    simp only [applied, Except.map, Except.ok.injEq] at complete
    rw [complete]

theorem start_wellFormed (litLen dist : HuffmanTable) (state : Reservoir)
    (history : Window) (bytes : List UInt8) (reader : LSBReader)
    (hrep : history.Represents bytes) :
    WellFormed (TokenMachine.start litLen dist state history bytes) reader :=
  ⟨hrep, token_parser_admissible litLen dist reader⟩

theorem start_denote (litLen dist : HuffmanTable) (state : Reservoir)
    (history : Window) (bytes : List UInt8) (reader : LSBReader) :
    denote (TokenMachine.start litLen dist state history bytes) reader =
      Manual.decodeStep litLen dist reader bytes := by
  simp only [denote, TokenMachine.start, ParserPhases.token_eval, Manual.decodeStep]
  rfl

theorem finish_denote (state : Reservoir) (pending : TokenOutput) (reader : LSBReader) :
    denote (TokenMachine.finish state pending) reader = outputDenote pending reader := by
  cases hp : pending.phase <;> simp only [TokenMachine.finish, hp, denote]

theorem finish_wellFormed (state : Reservoir) (pending : TokenOutput) (reader : LSBReader)
    (h : pending.Valid) : WellFormed (TokenMachine.finish state pending) reader := by
  cases hp : pending.phase with
  | complete flag =>
    simp only [TokenMachine.finish, hp, WellFormed]
    exact ⟨h, flag, rfl⟩
  | literal _ | matchBytes _ _ | endBlock =>
    simpa only [TokenMachine.finish, hp, WellFormed] using h

theorem emit_valid (state : Reservoir) (pending : TokenOutput) (reader : LSBReader)
    (capacity : Nat) (h : pending.Valid) :
    WellFormed (TokenMachine.emit state pending capacity) reader ∧
      denote (TokenMachine.emit state pending capacity) reader = outputDenote pending reader := by
  rw [TokenMachine.emit_eq state pending capacity h]
  exact ⟨finish_wellFormed _ _ _ (pending.advance_valid capacity h),
    (finish_denote _ _ _).trans (outputDenote_advance pending capacity reader h)⟩

/-- Parsed matches with insufficient history are deliberately allowed: both
the checked machine and the mathematical token application reject them. -/
theorem emit_start (state : Reservoir) (history : Window) (bytes : List UInt8)
    (token : Manual.Token) (reader : LSBReader) (capacity : Nat)
    (hrep : history.Represents bytes) (htoken : TokenAdmissible token) :
    WellFormed (TokenMachine.emit state (TokenOutput.start history bytes token) capacity) reader ∧
      denote (TokenMachine.emit state (TokenOutput.start history bytes token) capacity) reader =
        Manual.applyToken bytes token reader := by
  by_cases hfits : TokenFitsHistory bytes token
  · have hvalid := TokenOutput.start_valid history bytes token hrep hfits
    exact ⟨(emit_valid state _ reader capacity hvalid).1,
      (emit_valid state _ reader capacity hvalid).2.trans
        (outputDenote_start history bytes token reader hrep hfits)⟩
  · cases token with
    | literal byte | endBlock => exact False.elim (hfits trivial)
    | matchBytes count distance =>
      have hbound : 0 < distance ∧ distance ≤ windowLimit := ⟨htoken.2.2.1, htoken.2.2.2⟩
      have hunavailable : bytes.length < distance := by
        change ¬ (0 < distance ∧ distance ≤ windowLimit ∧ distance ≤ bytes.length) at hfits
        omega
      rw [TokenMachine.emit, TokenOutput.reject_unavailable_match history bytes count distance capacity hrep hunavailable]
      exact ⟨hrep, by simp only [denote, Manual.applyToken, hunavailable, ite_true]⟩

theorem feed_denote (machine : TokenMachine) (reader : LSBReader) (added : List UInt8) :
    denote (machine.feed added) reader = denote machine reader := by
  cases machine <;> rfl

theorem feed_wellFormed (machine : TokenMachine) (reader : LSBReader) (added : List UInt8)
    (h : WellFormed machine reader) :
    WellFormed (machine.feed added) (Reservoir.readerFeed reader added) := by
  cases machine with
  | parsing parser state history bytes => exact ⟨h.1, h.2.feed added⟩
  | emitting state pending | done state completed | error err state history bytes => exact h

/-- Every physical scheduler/output step preserves the full logical result,
even on errors and suspensions. The witness normalizes the physical reservoir;
the equality remains valid under every additional input suffix. -/
theorem step_correct_feed (machine : TokenMachine) (reader : LSBReader)
    (fuel capacity : Nat) (hnorm : Reservoir.Normalizes machine.reservoir reader)
    (hwf : WellFormed machine reader) :
    ∃ nextReader, Reservoir.Normalizes (machine.step fuel capacity).reservoir nextReader ∧
      WellFormed (machine.step fuel capacity) nextReader ∧ ∀ future,
        denote machine (Reservoir.readerFeed reader future) =
          denote (machine.step fuel capacity) (Reservoir.readerFeed nextReader future) := by
  cases machine with
  | parsing parser state history bytes =>
    change Reservoir.Normalizes state reader at hnorm
    obtain ⟨hrep, hadmissible⟩ := hwf
    obtain ⟨nextReader, hnext, observations⟩ := Parser.run_correct_feed fuel parser hnorm
    cases run : Parser.run fuel parser state with
    | done token rest =>
      rw [run] at hnext observations
      have htoken : TokenAdmissible token := hadmissible [] token nextReader (by
        simpa only [Reservoir.readerFeed_nil, RunResult.observe] using observations [])
      refine ⟨nextReader, ?_, ?_, ?_⟩
      · simpa only [TokenMachine.step, run, TokenMachine.emit_reservoir, RunResult.state] using hnext
      · simpa only [TokenMachine.step, run] using
          (emit_start rest history bytes token nextReader capacity hrep htoken).1
      · intro future
        simp only [denote, TokenMachine.step, run]
        rw [observations future]
        exact (emit_start rest history bytes token
          (Reservoir.readerFeed nextReader future) capacity hrep htoken).2.symm
    | error err rest =>
      rw [run] at hnext observations
      refine ⟨nextReader, ?_, ?_, ?_⟩
      · simpa only [TokenMachine.step, run, TokenMachine.reservoir, RunResult.state] using hnext
      · simpa only [TokenMachine.step, run, WellFormed] using hrep
      · intro future
        simp only [denote, TokenMachine.step, run]
        rw [observations future]
        rfl
    | needInput continuation rest =>
      rw [run] at hnext observations
      refine ⟨nextReader, ?_, ?_, ?_⟩
      · simpa only [TokenMachine.step, run, TokenMachine.reservoir, RunResult.state] using hnext
      · simp only [TokenMachine.step, run, WellFormed]
        refine ⟨hrep, ?_⟩
        intro future token finalReader parsed
        exact hadmissible future token finalReader ((observations future).trans parsed)
      · intro future
        simp only [denote, TokenMachine.step, run]
        rw [observations future]
        rfl
    | yield continuation rest =>
      rw [run] at hnext observations
      refine ⟨nextReader, ?_, ?_, ?_⟩
      · simpa only [TokenMachine.step, run, TokenMachine.reservoir, RunResult.state] using hnext
      · simp only [TokenMachine.step, run, WellFormed]
        refine ⟨hrep, ?_⟩
        intro future token finalReader parsed
        exact hadmissible future token finalReader ((observations future).trans parsed)
      · intro future
        simp only [denote, TokenMachine.step, run]
        rw [observations future]
        rfl
  | emitting state pending =>
    refine ⟨reader, ?_, ?_, ?_⟩
    · change Reservoir.Normalizes (TokenMachine.emit state pending capacity).reservoir reader
      rw [TokenMachine.emit_reservoir]
      exact hnorm
    · exact (emit_valid state pending reader capacity hwf).1
    · intro future
      exact (emit_valid state pending (Reservoir.readerFeed reader future) capacity hwf).2.symm
  | done state completed => exact ⟨reader, hnorm, hwf, fun _ => rfl⟩
  | error err state history bytes => exact ⟨reader, hnorm, hwf, fun _ => rfl⟩

theorem step_correct (machine : TokenMachine) (reader : LSBReader)
    (fuel capacity : Nat) (hnorm : Reservoir.Normalizes machine.reservoir reader)
    (hwf : WellFormed machine reader) :
    ∃ nextReader, Reservoir.Normalizes (machine.step fuel capacity).reservoir nextReader ∧
      WellFormed (machine.step fuel capacity) nextReader ∧
        denote machine reader = denote (machine.step fuel capacity) nextReader := by
  obtain ⟨nextReader, hnext, hwfnext, observations⟩ := step_correct_feed machine reader fuel capacity hnorm hwf
  exact ⟨nextReader, hnext, hwfnext,
    by simpa only [Reservoir.readerFeed_nil] using observations []⟩

/-- Completed states expose the same exact flag, output and reader as their
finite observation; the continuation denotation has no remaining work. -/
theorem done_denote (state : Reservoir) (completed : TokenOutput) (reader : LSBReader)
    (flag : Bool) (hphase : completed.phase = .complete flag) :
    denote (.done state completed) reader =
      .ok (if flag then .done completed.output reader else .more completed.output reader) := by
  cases flag <;> simp only [denote, outputDenote, TokenOutput.step,
    TokenOutput.DistanceAvailable, TokenOutput.advance, TokenOutput.observe, hphase,
    ite_true, Bool.false_eq_true, ite_false]

/-! ## Nonvacuity and error witnesses -/

/-- Arbitrary continuations really need the invariant: this total parser
returns an illegal distance, so it is not silently treated as an RFC parser. -/
theorem zero_distance_parser_not_admissible (reader : LSBReader) :
    ¬ ParserAdmissible (.pure (.matchBytes 3 0)) reader := by
  intro h
  have bad := h [] (.matchBytes 3 0) reader (by simp only [Parser.eval, Reservoir.readerFeed_nil])
  exact Nat.lt_irrefl 0 bad.2.2.1

/-- A valid distance code may still exceed history. Both logical evaluation
and a zero-capacity physical step reject this input. -/
theorem unavailable_history_zero_capacity :
    let machine := TokenMachine.parsing (.pure (.matchBytes 3 2)) (Reservoir.ofBytes [])
      (Window.ofOutput [65]) [65]
    denote machine ⟨0, 0, [], 0⟩ = .error .decodeOverrun ∧
      machine.step 1 0 = .error .decodeOverrun (Reservoir.ofBytes []) (Window.ofOutput [65]) [65] := by
  exact ⟨rfl, rfl⟩

/-- The pending overlapping match already denotes all its eventual output;
neither the current scheduler budget nor the next output buffer is needed to
state this completed logical result. -/
theorem overlapping_match_continuation :
    denote TokenMachine.matchPending ⟨0, 6, [], 10⟩ =
      .ok (.more [65, 65, 65, 65] ⟨0, 6, [], 10⟩) := rfl

end Silmaril.Formats.Compression.Inflate.Stream.TokenContinuation
