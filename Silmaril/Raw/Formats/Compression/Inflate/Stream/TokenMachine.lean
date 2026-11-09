module

public import Silmaril.Formats.Compression.Inflate.Stream.TokenMachine
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.ParserBridge
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.TokenOutput
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.TokenBounds

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.TokenMachine`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

namespace TokenMachine

theorem finish_reservoir (state : Reservoir) (pending : TokenOutput) :
    (finish state pending).reservoir = state := by
  cases hp : pending.phase <;> simp only [finish, hp, reservoir]

theorem finish_observe (state : Reservoir) (pending : TokenOutput) (reader : LSBReader) :
    (finish state pending).observe reader = .ok (pending.observe reader) := by
  cases hp : pending.phase <;> simp only [finish, hp, observe]

theorem emit_reservoir (state : Reservoir) (pending : TokenOutput) (capacity : Nat) :
    (emit state pending capacity).reservoir = state := by
  unfold emit
  cases pending.step capacity with
  | error err => rfl
  | ok next => exact finish_reservoir state next

theorem feed_reservoir (machine : TokenMachine) (added : List UInt8) :
    (machine.feed added).reservoir = machine.reservoir.feed added := by
  cases machine <;> rfl

theorem feed_output (machine : TokenMachine) (added : List UInt8) :
    (machine.feed added).output = machine.output := by
  cases machine <;> rfl

theorem feed_window (machine : TokenMachine) (added : List UInt8) :
    (machine.feed added).window = machine.window := by
  cases machine <;> rfl

theorem finish_feed (state : Reservoir) (pending : TokenOutput) (added : List UInt8) :
    (finish state pending).feed added = finish (state.feed added) pending := by
  cases hp : pending.phase <;> simp only [finish, hp, feed]

theorem emit_eq (state : Reservoir) (pending : TokenOutput) (capacity : Nat)
    (h : pending.Valid) :
    emit state pending capacity = finish state (pending.advance capacity) := by
  simp only [emit, pending.step_ok capacity h]

/-- Once parsing is finished, scheduler budgets no longer matter and no input
can be consumed. Every further step only advances the retained output phase. -/
theorem finish_step (state : Reservoir) (pending : TokenOutput)
    (fuel capacity : Nat) (h : pending.Valid) :
    (finish state pending).step fuel capacity = finish state (pending.advance capacity) := by
  cases hp : pending.phase with
  | complete isEnd => simp only [finish, hp, step, TokenOutput.advance]
  | literal byte | matchBytes _ _ | endBlock =>
    simpa only [finish, hp, step] using emit_eq state pending capacity h

theorem step_parsed (parser : Parser Manual.Token) (state rest : Reservoir)
    (history : Window) (bytes : List UInt8) (token : Manual.Token)
    (fuel capacity : Nat) (parsed : Parser.run fuel parser state = .done token rest)
    (hrep : history.Represents bytes) (hfits : TokenFitsHistory bytes token) :
    (TokenMachine.parsing parser state history bytes).step fuel capacity =
      finish rest ((TokenOutput.start history bytes token).advance capacity) := by
  simp only [step, parsed]
  exact emit_eq rest _ capacity (TokenOutput.start_valid history bytes token hrep hfits)

/-- Input and scheduler suspension keep the exact continuation rather than
restarting `ParserPhases.token` with the already consumed prefix. -/
theorem step_needInput (parser next : Parser Manual.Token) (state rest : Reservoir)
    (history : Window) (bytes : List UInt8) (fuel capacity : Nat)
    (paused : Parser.run fuel parser state = .needInput next rest) :
    (TokenMachine.parsing parser state history bytes).step fuel capacity =
      .parsing next rest history bytes := by simp only [step, paused]

theorem step_yield (parser next : Parser Manual.Token) (state rest : Reservoir)
    (history : Window) (bytes : List UInt8) (fuel capacity : Nat)
    (paused : Parser.run fuel parser state = .yield next rest) :
    (TokenMachine.parsing parser state history bytes).step fuel capacity =
      .parsing next rest history bytes := by simp only [step, paused]

theorem finish_fold (state : Reservoir) (pending : TokenOutput) (capacities : List Nat)
    (spent : Nat) (h : pending.Valid) :
    capacities.foldl (fun current capacity => current.step 0 capacity)
        (finish state (pending.advance spent)) =
      finish state (pending.advance (spent + capacities.sum)) := by
  induction capacities generalizing spent with
  | nil => simp only [List.foldl_nil, List.sum_nil, Nat.add_zero]
  | cons capacity rest ih =>
    simp only [List.foldl_cons, List.sum_cons]
    rw [finish_step state _ 0 capacity (pending.advance_valid spent h),
      TokenOutput.advance_add, ih, Nat.add_assoc]

theorem finish_runBuffers (state : Reservoir) (pending : TokenOutput) (capacities : List Nat)
    (h : pending.Valid) :
    (finish state pending).runBuffers capacities =
      finish state (pending.advance capacities.sum) := by
  unfold runBuffers
  rw [finish_step state pending 0 0 h, finish_fold state pending capacities 0 h, Nat.zero_add]

/-- A completed real parser run followed by enough total output space agrees
with token application; arbitrary output-buffer boundaries preserve all fields. -/
theorem parsed_buffers_complete (parser : Parser Manual.Token) (state rest : Reservoir)
    (history : Window) (bytes : List UInt8) (token : Manual.Token)
    (reader : LSBReader) (fuel : Nat) (capacities : List Nat)
    (parsed : Parser.run fuel parser state = .done token rest)
    (hrep : history.Represents bytes) (hfits : TokenFitsHistory bytes token)
    (hcapacity : tokenLength token ≤ capacities.sum) :
    (((TokenMachine.parsing parser state history bytes).step fuel 0).runBuffers capacities).observe reader =
      (Manual.applyToken bytes token reader).map some := by
  rw [step_parsed parser state rest history bytes token fuel 0 parsed hrep hfits,
    finish_runBuffers rest _ capacities
      ((TokenOutput.start history bytes token).advance_valid 0
        (TokenOutput.start_valid history bytes token hrep hfits)),
    TokenOutput.advance_add, Nat.zero_add, finish_observe]
  exact TokenOutput.complete_eq_applyToken history bytes token reader _ hrep hfits hcapacity

/-- The actual one-token reservoir machine refines `Manual.decodeStep`, with
the logical reader related to the final physical reservoir. The explicit
history premise is necessary: arbitrary parsed matches need not fit history. -/
theorem decodeStep_complete (litLen dist : HuffmanTable) (state rest : Reservoir)
    (history : Window) (bytes : List UInt8) (token : Manual.Token)
    (reader : LSBReader) (fuel : Nat) (capacities : List Nat)
    (hnorm : Reservoir.Normalizes state reader)
    (parsed : Parser.run fuel (ParserPhases.token litLen dist) state = .done token rest)
    (hrep : history.Represents bytes) (hfits : TokenFitsHistory bytes token)
    (hcapacity : tokenLength token ≤ capacities.sum) :
    ∃ nextReader, Reservoir.Normalizes rest nextReader ∧
      (((start litLen dist state history bytes).step fuel 0).runBuffers capacities).observe nextReader =
        (Manual.decodeStep litLen dist reader bytes).map some := by
  obtain ⟨nextReader, hnext, observations⟩ := ParserBridge.token_run litLen dist fuel hnorm
  rw [parsed] at hnext observations
  refine ⟨nextReader, hnext, ?_⟩
  have hparse : Manual.parseToken litLen dist reader = .ok (token, nextReader) := by
    simpa only [Reservoir.readerFeed_nil, RunResult.observe] using observations []
  simpa only [start, Manual.decodeStep, hparse] using
    parsed_buffers_complete (ParserPhases.token litLen dist) state rest history bytes token
      nextReader fuel capacities parsed hrep hfits hcapacity

theorem spec_decodeStep_complete (litLen dist : HuffmanTable) (state rest : Reservoir)
    (history : Window) (bytes : List UInt8) (token : Manual.Token)
    (reader : LSBReader) (fuel : Nat) (capacities : List Nat)
    (hnorm : Reservoir.Normalizes state reader)
    (parsed : Parser.run fuel (ParserPhases.token litLen dist) state = .done token rest)
    (hrep : history.Represents bytes) (hfits : TokenFitsHistory bytes token)
    (hcapacity : tokenLength token ≤ capacities.sum) :
    ∃ nextReader, Reservoir.Normalizes rest nextReader ∧
      (((start litLen dist state history bytes).step fuel 0).runBuffers capacities).observe nextReader =
        (Deflate.decodeStep litLen dist reader bytes).map some := by
  simpa only [Manual.decodeStep_eq_spec] using
    decodeStep_complete litLen dist state rest history bytes token reader fuel capacities
      hnorm parsed hrep hfits hcapacity

/-- Successful format decoding supplies all the match-history premises; the
caller need not separately assume positive/bounded distances. -/
theorem decodeStep_success_complete (litLen dist : HuffmanTable) (state rest : Reservoir)
    (history : Window) (bytes : List UInt8) (token : Manual.Token)
    (reader : LSBReader) (result : Deflate.SymbolStep) (fuel : Nat) (capacities : List Nat)
    (hnorm : Reservoir.Normalizes state reader)
    (parsed : Parser.run fuel (ParserPhases.token litLen dist) state = .done token rest)
    (hrep : history.Represents bytes)
    (hdecode : Manual.decodeStep litLen dist reader bytes = .ok result)
    (hcapacity : tokenLength token ≤ capacities.sum) :
    ∃ nextReader, Reservoir.Normalizes rest nextReader ∧
      (((start litLen dist state history bytes).step fuel 0).runBuffers capacities).observe nextReader =
        .ok (some result) := by
  obtain ⟨nextReader, hnext, observations⟩ := ParserBridge.token_run litLen dist fuel hnorm
  rw [parsed] at hnext observations
  have hparse : Manual.parseToken litLen dist reader = .ok (token, nextReader) := by
    simpa only [Reservoir.readerFeed_nil, RunResult.observe] using observations []
  have happly : Manual.applyToken bytes token nextReader = .ok result := by
    simpa only [Manual.decodeStep, hparse] using hdecode
  have hfits := TokenBounds.parseToken_fitsHistory hparse happly
  refine ⟨nextReader, hnext, ?_⟩
  simpa only [start, happly, Except.map] using
    parsed_buffers_complete (ParserPhases.token litLen dist) state rest history bytes token
      nextReader fuel capacities parsed hrep hfits hcapacity

/-- A parsed token remains valid after any later input arrives. Emission uses
the saved token and leaves that additional input in the reservoir. -/
theorem decodeStep_complete_future (litLen dist : HuffmanTable) (state rest : Reservoir)
    (history : Window) (bytes : List UInt8) (token : Manual.Token)
    (reader : LSBReader) (fuel : Nat) (capacities : List Nat)
    (hnorm : Reservoir.Normalizes state reader)
    (parsed : Parser.run fuel (ParserPhases.token litLen dist) state = .done token rest)
    (hrep : history.Represents bytes) (hfits : TokenFitsHistory bytes token)
    (hcapacity : tokenLength token ≤ capacities.sum) :
    ∃ nextReader, Reservoir.Normalizes rest nextReader ∧ ∀ future,
      ((((start litLen dist state history bytes).step fuel 0).feed future).runBuffers capacities).observe
          (Reservoir.readerFeed nextReader future) =
        (Manual.decodeStep litLen dist (Reservoir.readerFeed reader future) bytes).map some := by
  obtain ⟨nextReader, hnext, observations⟩ := ParserBridge.token_run litLen dist fuel hnorm
  rw [parsed] at hnext observations
  refine ⟨nextReader, hnext, ?_⟩
  intro future
  have hparse : Manual.parseToken litLen dist (Reservoir.readerFeed reader future) =
      .ok (token, Reservoir.readerFeed nextReader future) := observations future
  rw [start, step_parsed _ state rest history bytes token fuel 0 parsed hrep hfits,
    finish_feed, finish_runBuffers _ _ capacities
      ((TokenOutput.start history bytes token).advance_valid 0
        (TokenOutput.start_valid history bytes token hrep hfits)),
    TokenOutput.advance_add, Nat.zero_add, finish_observe, Manual.decodeStep, hparse]
  exact TokenOutput.complete_eq_applyToken history bytes token _ _ hrep hfits hcapacity

/-! ## Kernel-checked split-input and split-output executions -/

theorem literal_input_suspends :
    match literalPrefix with
    | .parsing _ state history bytes => state = ⟨0, 0, [], 8⟩ ∧ history.bytes = [] ∧ bytes = []
    | _ => False := by exact ⟨rfl, rfl, rfl⟩

theorem literal_retains_parsed_token :
    literalPending = .emitting ⟨0, 7, [], 9⟩
      ⟨Window.ofOutput [], [], .literal 144⟩ := rfl

theorem literal_split_output :
    (literalPending.runBuffers [0, 1]).observe ⟨0, 7, [], 9⟩ =
      .ok (some (.more [144] ⟨0, 7, [], 9⟩)) := rfl

theorem match_retains_overlap_and_remainder :
    match matchPending with
    | .emitting state pending =>
      state = ⟨0, 6, [], 10⟩ ∧ pending.window.bytes = [65, 65] ∧
        pending.output = [65, 65] ∧ pending.phase = .matchBytes 2 1
    | _ => False := by exact ⟨rfl, rfl, rfl, rfl⟩

/-- The second and third match bytes read the newly written window, across
separate output buffers. The nine-bit length was itself split across inputs. -/
theorem match_split_input_output :
    (matchPending.runBuffers [0, 1, 1]).observe ⟨0, 6, [], 10⟩ =
      .ok (some (.more [65, 65, 65, 65] ⟨0, 6, [], 10⟩)) := rfl

theorem output_does_not_consume_future_input :
    ((matchPending.feed [0xab, 0xcd]).runBuffers [1, 1]).reservoir =
      ⟨0, 6, [0xab, 0xcd], 10⟩ := rfl

end TokenMachine
end Silmaril.Formats.Compression.Inflate.Stream
