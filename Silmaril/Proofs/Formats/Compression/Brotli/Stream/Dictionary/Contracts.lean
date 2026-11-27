module

public import Silmaril.Formats.Compression.Brotli.Stream.Dictionary.Defs
import Silmaril.Formats.Compression.Brotli.Stream.Thms
import Silmaril.Formats.Compression.Brotli.Thms
import Silmaril.Formats.Compression.Brotli.CompressedHeader.Thms
import Silmaril.Formats.Compression.Brotli.Literal.Switch.Thms
import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Block.Thms
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Stream.Dictionary

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Internal (Cursor start readWindow readWindow_sound)
open Silmaril.Formats.Compression.Brotli.Literal.Switch (Source)
open Silmaril.Formats.Compression.Brotli.Stream (Header Cause)
open Silmaril.Formats.Compression.Brotli.Stream.Internal
open Silmaril.Formats.Compression.Brotli.Stream.Dictionary
open Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary
  (readBlockCounted readBlockCounted_sound readBlockCounted_error)

private def BodyResult (limits : Stream.Limits) (window index : Nat) (frame : Header)
    (initial : State) (before : LSBReader) (input : List Bool) :
    Except Stream.DistanceSwitch.Error (State × LSBReader) → Prop
  | .error reason => BodyFailure limits window index frame initial before input reason
  | .ok (next, after) =>
    next.execution.output.size ≤ limits.output ∧
    ∃ used tail chunk charge, BodyWire limits window before.totalRead frame initial used chunk charge next ∧
      Source before after input used tail ∧ Cursor after tail

private theorem readBody_observe {limits : Stream.Limits} {window index : Nat}
    {frame : Header} {initial : State} {before : LSBReader} {input : List Bool}
    (cursor : Cursor before input) (fits : initial.execution.output.size ≤ limits.output) :
    BodyResult limits window index frame initial before input
      (Stream.Dictionary.Internal.body limits window index frame initial before) := by
  unfold Stream.Dictionary.Internal.body
  cases frame with
  | terminal =>
    exact ⟨fits, [], input, [], 0, .terminal initial, ⟨by simp, cursor.1, cursor.2.1, by simp⟩, cursor⟩
  | metadata last length =>
    unfold readBodyWithResult
    cases aligned : alignedBody limits length.size before with
    | error reason =>
      simp only [aligned, Except.mapError, bind, Except.bind, BodyResult]
      exact .envelope (.byteBody aligned)
    | ok pair =>
      obtain ⟨bytes, after⟩ := pair
      simp only [aligned, Except.mapError, bind, Except.bind, pure, Except.pure, BodyResult]
      obtain ⟨tail, extent, split, next, position, _⟩ := alignedBody_sound cursor aligned
      exact ⟨fits, _, tail, [], 0, .metadata initial extent, ⟨split, next.1, next.2.1, position⟩, next⟩
  | raw length =>
    unfold readBodyWithResult
    dsimp only
    split
    · rename_i exceeded
      exact .envelope (.outputLimit before exceeded)
    · rename_i room
      cases aligned : alignedBody limits length.size before with
      | error reason =>
        simp only [Except.mapError, bind, Except.bind, BodyResult]
        exact .envelope (.byteBody aligned)
      | ok pair =>
        obtain ⟨bytes, after⟩ := pair
        simp only [Except.mapError, bind, Except.bind, pure, Except.pure, BodyResult]
        obtain ⟨tail, extent, split, next, position, _⟩ := alignedBody_sound cursor aligned
        exact ⟨by simpa [extent] using Nat.le_of_not_gt room, _, tail, bytes, 0, .raw extent,
          ⟨split, next.1, next.2.1, position⟩, next⟩
  | compressed last length =>
    unfold readBodyWithResult
    dsimp only
    split
    · rename_i exceeded
      exact .envelope (.outputLimit before exceeded)
    · cases parsed : CompressedHeader.read ⟨limits.mapEntries, limits.trees, limits.bits - before.totalRead⟩ before with
      | error reason =>
        simp only [Except.mapError, bind, Except.bind, BodyResult]
        exact .envelope (.header parsed)
      | ok pair =>
        obtain ⟨header, payload⟩ := pair
        simp only [Except.mapError, bind, Except.bind]
        obtain ⟨_, _, work, tableBits, tail, _, tables, split, rep, count, pos, _⟩ :=
          CompressedHeader.read_sound cursor.1 cursor.2.1 parsed
        have first : Source before payload input tableBits tail := ⟨split, rep, count, pos⟩
        cases decoder : readBlockCounted header window length.size initial.remainingCommands
            (Stream.DistanceSwitch.payloadLimits limits payload) initial.execution payload with
        | error reason =>
          simp only [ BodyResult]
          have failure := readBlockCounted_error rep count decoder
          obtain ⟨⟨used, unread, tailSplit, bit⟩, path⟩ := failure
          cases reason with
          | initialOutput _ => exact False.elim (Nat.not_lt_of_ge fits path.1)
          | fuel | command => exact .payload rfl parsed first path tailSplit bit
        | ok result =>
          simp only [ pure, Except.pure, BodyResult]
          obtain ⟨_, outFit, used, suffix, chunks, chain, _, slots, source, _⟩ :=
            readBlockCounted_sound rep count decoder
          have payloadCursor := cursor_advance cursor split rep count pos
          have next := cursor_advance payloadCursor source.split source.rep source.count source.position
          exact ⟨outFit, tableBits ++ used, suffix, chunks.flatten, chunks.length,
            .compressed tables pos chain source slots, first.trans source, next⟩

private theorem walk_observe {limits : Stream.Limits} {window fuel index : Nat}
    {state : State} {before : LSBReader} {input : List Bool}
    (cursor : Cursor before input) (fits : state.execution.output.size ≤ limits.output) :
    Walk limits window fuel index state before input
      (readBlocksWithState Stream.DistanceSwitch.Error.envelope Stream.Dictionary.Internal.body
        limits window fuel index state before) := by
  induction fuel generalizing index state before input with
  | zero => exact .fuel
  | succ fuel ih =>
    unfold readBlocksWithState
    cases framed : readHeader before with
    | error reason =>
      simp only [Except.mapError, bind, Except.bind, Function.comp_apply]
      exact .header framed
    | ok pair =>
      obtain ⟨frame, body⟩ := pair
      simp only [Except.mapError, bind, Except.bind]
      obtain ⟨tail, valid, split, bodyCursor, position⟩ := readHeader_sound cursor framed
      have first : Source before body input frame.bits tail := ⟨split, bodyCursor.1, bodyCursor.2.1, position⟩
      cases within : withinBits limits body with
      | error cause =>
        exact .headerBits framed within
      | ok accepted =>
        cases accepted
        have observed := readBody_observe (limits := limits) (window := window) (index := index)
          (frame := frame) bodyCursor fits
        cases stepped : Stream.Dictionary.Internal.body limits window index frame state body with
        | error reason =>
          rw [stepped] at observed
          exact .body framed within first stepped observed
        | ok pair =>
          obtain ⟨next, after⟩ := pair
          rw [stepped] at observed
          obtain ⟨nextFit, used, suffix, chunk, charge, wire, second, nextCursor⟩ := observed
          have source := first.trans second
          rw [position] at wire
          have passed : Passed limits window index frame state next before after input suffix chunk charge :=
            ⟨body, used, framed, within, valid, source.split, source.position, wire, stepped⟩
          by_cases last : frame.last = true
          · cases finished : finish limits after with
            | error cause =>
              simpa [last, finished, Except.mapError, bind, Except.bind] using
                (Walk.finishError (fuel := fuel) passed last finished)
            | ok aligned =>
              obtain ⟨fill, consumed, cap⟩ := finish_sound nextCursor finished
              have extent := source.position
              have original := congrArg List.length source.split
              simp only [List.length_append] at original extent
              have bitFit : before.totalRead + input.length ≤ limits.bits := by omega
              simpa [last, finished, Except.mapError, bind, Except.bind, pure, Except.pure] using
                (Walk.last (fuel := fuel) passed last finished fill bitFit nextFit)
          · have notLast : frame.last = false := by cases flag : frame.last <;> simp_all
            simpa [notLast] using Walk.more passed notLast (ih nextCursor nextFit)

theorem decode_wire (limits : Stream.Dictionary.Limits) (input : List UInt8) :
    Wire limits input (Stream.Dictionary.decode limits input) := by
  unfold Stream.Dictionary.decode decodeWithState
  dsimp only
  split
  · rename_i exceeds
    exact .inputLimit exceeds
  · rename_i fits
    cases windowRead : readWindow (start input) with
    | error reason =>
      simp only [Except.mapError, bind, Except.bind, Function.comp_apply]
      exact .window (Nat.le_of_not_gt fits) windowRead
    | ok pair =>
      obtain ⟨window, reader⟩ := pair
      simp only [Except.mapError, bind, Except.bind]
      cases checked : withinBits limits.framing reader with
      | error cause =>
        exact .windowBits (Nat.le_of_not_gt fits) windowRead checked
      | ok accepted =>
        cases accepted
        by_cases tooWide : limits.framing.window < windowSize window
        · simpa [tooWide, Except.mapError, bind, Except.bind] using
            Wire.windowLimit (Nat.le_of_not_gt fits) windowRead checked tooWide
        · have cursor : Cursor (start input) (bytesBits input) := by simp [Cursor, start, LSBReader.Rep, natBits]
          obtain ⟨code, tail, wire, split, next, position⟩ := readWindow_sound cursor windowRead
          simpa [tooWide, Except.mapError, bind, Except.bind] using
            Wire.blocks (Nat.le_of_not_gt fits) wire (Nat.le_of_not_gt tooWide)
              ⟨split, next.1, next.2.1, position⟩ (walk_observe next (Nat.zero_le _))

theorem BodyWire.output {limits : Stream.Limits} {window position : Nat} {frame : Header}
    {initial final : State} {bits : List Bool} {chunk : List UInt8} {charge : Nat}
    (wire : BodyWire limits window position frame initial bits chunk charge final) :
    final.execution.output.toList = initial.execution.output.toList ++ chunk ∧
    chunk.length = frame.outputSize ∧ charge + final.remainingCommands = initial.remainingCommands := by
  cases wire with
  | terminal | metadata => simp [Header.outputSize]
  | raw length => exact ⟨by simp, length, by simp⟩
  | compressed _ _ chain _ count =>
    obtain ⟨size, written⟩ := Execute.DistanceSwitch.Dictionary.CommandsWire.output chain
    have extent := congrArg List.length written
    simp only [Array.length_toList, List.length_append] at extent
    refine ⟨written, ?_, count⟩
    dsimp [Header.outputSize, Execute.Block.endOutput, Execute.InsertCopy.State.start] at size extent ⊢
    omega

private def AtBit (origin : Nat) (input : List Bool) (bit : Nat) : Prop :=
  ∃ used suffix, input = used ++ suffix ∧ bit = origin + used.length

private theorem atStart (origin : Nat) (input : List Bool) : AtBit origin input origin :=
  ⟨[], input, rfl, by simp⟩

private theorem AtBit.prepend {before after bit : Nat} {input used tail : List Bool}
    (split : input = used ++ tail) (position : after = before + used.length) (atTail : AtBit after tail bit) :
    AtBit before input bit := by
  obtain ⟨read, suffix, remaining, location⟩ := atTail
  exact ⟨used ++ read, suffix, by rw [split, remaining, List.append_assoc],
    by rw [location, position, List.length_append, Nat.add_assoc]⟩

private theorem BodyFailure.atBit {limits : Stream.Limits} {window index : Nat} {frame : Header}
    {initial : State} {before : LSBReader} {input : List Bool} {error : Stream.DistanceSwitch.Error}
    (failed : BodyFailure limits window index frame initial before input error) :
    AtBit before.totalRead input error.bit := by
  cases failed with
  | envelope _ => exact atStart _ _
  | payload _ _ source _ split pos => exact AtBit.prepend source.split source.position ⟨_, _, split, pos⟩

private theorem Walk.report {limits : Stream.Limits} {window fuel index : Nat} {initial : State}
    {before : LSBReader} {input : List Bool} {outcome : Except Stream.DistanceSwitch.Error State}
    (wire : Walk limits window fuel index initial before input outcome) :
    match outcome with
    | .error error => AtBit before.totalRead input error.bit
    | .ok final =>
      before.totalRead + input.length ≤ limits.bits ∧ final.execution.output.size ≤ limits.output ∧
      ∃ (chunks : List (List UInt8)) (charges : List Nat),
        0 < chunks.length ∧ chunks.length ≤ fuel ∧ charges.length = chunks.length ∧
        final.execution.output.toList = initial.execution.output.toList ++ chunks.flatten ∧
        charges.sum + final.remainingCommands = initial.remainingCommands := by
  induction wire with
  | fuel | header | headerBits => exact atStart _ _
  | body _ _ first _ reason =>
    exact AtBit.prepend first.split first.position (BodyFailure.atBit reason)
  | finishError passed _ _ =>
    obtain ⟨_, _, _, _, _, split, pos, _, _⟩ := passed.parts
    exact AtBit.prepend split pos (atStart _ _)
  | @last fuel index charge initial final before after endCursor input tail chunk frame passed _ _ _ fits output =>
    obtain ⟨_, _, _, _, _, _, _, body, _⟩ := passed.parts
    obtain ⟨written, _, slots⟩ := BodyWire.output body
    refine ⟨fits, output, [chunk], [charge], by simp, by simp, rfl, ?_, ?_⟩
    · simpa using written
    · simpa using slots
  | @more fuel index charge initial next before after input tail chunk frame outcome passed more rest ih =>
    obtain ⟨_, _, _, _, _, split, pos, body, _⟩ := passed.parts
    cases outcome with
    | error reason => exact AtBit.prepend split pos ih
    | ok final =>
      obtain ⟨bitFit, outFit, chunks, charges, positive, budget, same, emitted, slotCount⟩ := ih
      obtain ⟨written, _, slots⟩ := BodyWire.output body
      have extent := congrArg List.length split
      rw [List.length_append] at extent
      refine ⟨by omega, outFit, chunk :: chunks, charge :: charges, by simp, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons, same]
      · simp [emitted, written, List.append_assoc]
      · simp only [List.sum_cons]; omega

private theorem bytes_length (input : List UInt8) : (bytesBits input).length = 8 * input.length := by
  induction input with
  | nil => rfl
  | cons byte rest ih =>
    simp only [bytesBits, List.flatMap_cons, List.length_append, natBits_length, List.length_cons] at *
    omega

theorem decode_sound {limits : Stream.Dictionary.Limits} {input : List UInt8} {final : State}
    (decoded : Stream.Dictionary.decode limits input = .ok final) :
    Wire limits input (.ok final) ∧ input.length ≤ limits.framing.input ∧
    8 * input.length ≤ limits.framing.bits ∧ final.execution.output.size ≤ limits.framing.output ∧
    ∃ (window : Nat) (chunks : List (List UInt8)) (charges : List Nat),
      10 ≤ window ∧ window ≤ 24 ∧ windowSize window ≤ limits.framing.window ∧
      0 < chunks.length ∧ chunks.length ≤ limits.framing.blocks ∧ charges.length = chunks.length ∧
      final.execution.output.toList = chunks.flatten ∧ charges.sum + final.remainingCommands = limits.commands := by
  have evidence := decode_wire limits input
  rw [decoded] at evidence
  refine ⟨evidence, ?_⟩
  cases evidence with
  | blocks fits window cap source walk =>
    obtain ⟨bitFit, outFit, chunks, charges, positive, budget, same, written, charged⟩ := Walk.report walk
    have size := congrArg List.length source.split
    simp only [bytes_length, List.length_append] at size
    have cursor := source.position
    change _ = 0 + _ at cursor
    obtain ⟨low, high⟩ := WindowWire.range window
    exact ⟨fits, by omega, outFit, _, chunks, charges, low, high, cap, positive, budget, same,
      by simpa [Execute.State.start] using written, charged⟩

theorem decode_error {limits : Stream.Dictionary.Limits} {input : List UInt8} {error : Stream.DistanceSwitch.Error}
    (decoded : Stream.Dictionary.decode limits input = .error error) :
    Wire limits input (.error error) ∧ ∃ used suffix, bytesBits input = used ++ suffix ∧ error.bit = used.length := by
  have evidence := decode_wire limits input
  rw [decoded] at evidence
  refine ⟨evidence, ?_⟩
  have bit : AtBit 0 (bytesBits input) error.bit := by
    cases evidence with
    | inputLimit | window | windowBits | windowLimit => exact atStart _ _
    | blocks _ _ _ source walk =>
      exact AtBit.prepend source.split source.position (Walk.report walk)
  simpa [AtBit] using bit

end Silmaril.Proofs.Formats.Compression.Brotli.Stream.Dictionary
