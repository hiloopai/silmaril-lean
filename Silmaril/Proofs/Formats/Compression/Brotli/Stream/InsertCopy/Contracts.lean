module

public import Silmaril.Formats.Compression.Brotli.Stream.InsertCopy.Defs
import Silmaril.Formats.Compression.Brotli.Stream.Thms
import Silmaril.Formats.Compression.Brotli.Thms
import Silmaril.Formats.Compression.Brotli.CompressedHeader.Thms
import Silmaril.Formats.Compression.Brotli.Execute.InsertCopy.Thms
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Stream.InsertCopy

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Internal (Cursor start readWindow_sound)
open Silmaril.Formats.Compression.Brotli.Stream (Header)
open Silmaril.Formats.Compression.Brotli.Stream.Internal
open Silmaril.Formats.Compression.Brotli.Stream.InsertCopy
open Silmaril.Formats.Compression.Brotli.Execute.InsertCopy (State)

private theorem bind_ok {ε α β : Type} {action : Except ε α} {next : α → Except ε β} {out : β}
    (read : (action >>= next) = .ok out) : ∃ value, action = .ok value ∧ next value = .ok out := by
  cases action with
  | error _ => cases read
  | ok value => exact ⟨value, rfl, read⟩

private theorem bind_mapped_ok {ε δ α β : Type} {action : Except ε α} {next : α → Except δ β}
    {error : ε → δ} {out : β} (read : (action.mapError error >>= next) = .ok out) :
    ∃ value, action = .ok value ∧ next value = .ok out := by
  cases action with
  | error _ => cases read
  | ok value => exact ⟨value, rfl, read⟩

theorem CommandsWire.output {header : CompressedHeader.Header} {block : Execute.Block}
    {initial final : State} {bits : List Bool} {chunks : List (List UInt8)}
    (wire : CommandsWire header block initial bits chunks final) :
    final.execution.output.size = block.endOutput ∧
    final.execution.output.toList = initial.execution.output.toList ++ chunks.flatten ∧
    chunks.length ≤ chunks.flatten.length := by
  induction wire with
  | done exactLength => exact ⟨exactLength, by simp, by simp⟩
  | step _ appended grows _ ih =>
    have remaining := ih.2.2
    refine ⟨ih.1, ?_, ?_⟩
    · simp [ih.2.1, Execute.InsertCopy.Result.state, appended, List.append_assoc]
    · simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega

theorem Payload.output {header : CompressedHeader.Header} {block : Execute.Block} {initial final : Execute.State}
    {bits : List Bool} {chunk : List UInt8} (start : block.start = initial.output.size)
    (wire : Payload header block initial bits chunk final) :
    final.output.toList = initial.output.toList ++ chunk ∧ chunk.length = block.length := by
  obtain ⟨chunks, runs, wire, rfl⟩ := wire
  obtain ⟨last, output, _⟩ := CommandsWire.output wire
  change final.output.toList = initial.output.toList ++ chunks.flatten at output
  change final.output.size = block.endOutput at last
  have len := congrArg List.length output
  simp only [Array.length_toList, List.length_append] at len
  simp only [Execute.Block.endOutput] at last
  exact ⟨output, by omega⟩

private theorem runCommands_sound {limits : Stream.Limits} {header : CompressedHeader.Header} {block : Execute.Block}
    {index fuel command : Nat} {initial final : State} {before after : LSBReader} {input : List Bool}
    (cursor : Cursor before input) (outFits : initial.execution.output.size ≤ limits.output)
    (bitFits : before.totalRead ≤ limits.bits)
    (read : Stream.InsertCopy.Internal.runCommands limits header block index fuel command initial before = .ok (final, after)) :
    final.execution.output.size ≤ limits.output ∧ after.totalRead ≤ limits.bits ∧
    ∃ used suffix chunks, CommandsWire header block initial used chunks final ∧ chunks.length ≤ fuel ∧
      input = used ++ suffix ∧ Cursor after suffix ∧ after.totalRead = before.totalRead + used.length := by
  induction fuel generalizing command initial final before after input with
  | zero =>
    unfold Stream.InsertCopy.Internal.runCommands at read
    split at read
    · rename_i done
      cases read
      exact ⟨outFits, bitFits, [], input, [], .done done, by simp, rfl, cursor, by simp⟩
    · cases read
  | succ fuel ih =>
    unfold Stream.InsertCopy.Internal.runCommands at read
    split at read
    · rename_i done
      cases read
      exact ⟨outFits, bitFits, [], input, [], .done done, by simp, rfl, cursor, by simp⟩
    · obtain ⟨⟨result, next⟩, commandRead, run⟩ := bind_mapped_ok read
      obtain ⟨_, _, _, grows, _, nextOut, used, tail, wire, split, rep, count, position, nextBits⟩ :=
        Execute.InsertCopy.read_sound cursor.1 cursor.2.1 commandRead
      change used.length ≤ limits.bits - before.totalRead at nextBits
      have nextCursor := cursor_advance cursor split rep count position
      have nextFit : next.totalRead ≤ limits.bits := by omega
      obtain ⟨outFit, finalFit, rest, suffix, chunks, chain, steps, restBits, finalCursor, finalPosition⟩ :=
        ih nextCursor nextOut nextFit run
      obtain ⟨_, _, _, _, _, _, commandWire⟩ := wire.parts
      obtain ⟨_, _, _, _, _, literals, _, matched, _, _, _, _, _, _, _, append⟩ := commandWire.parts
      have appended : result.execution.state.output.toList = initial.execution.output.toList ++ (literals ++ matched) := by
        simpa only [List.append_assoc] using append
      have len := congrArg List.length appended
      simp only [Array.length_toList, List.length_append] at len
      refine ⟨outFit, finalFit, used ++ rest, suffix, (literals ++ matched) :: chunks,
        .step wire appended (by simp only [List.length_append]; omega) chain, ?_, ?_, finalCursor, ?_⟩
      · simp only [List.length_cons]; omega
      · rw [split, restBits, List.append_assoc]
      · rw [finalPosition, position, List.length_append, Nat.add_assoc]

private theorem readPayload_sound : PayloadSound Stream.InsertCopy.Internal.readPayload Payload := by
  intro limits index headerBit header block initial final before after input cursor outFits bitFits read
  unfold Stream.InsertCopy.Internal.readPayload at read
  obtain ⟨⟨out, stop⟩, commandsRead, done⟩ := bind_ok read
  cases done
  obtain ⟨outFit, bitFit, used, suffix, chunks, chain, _, split, next, pos⟩ :=
    runCommands_sound cursor outFits bitFits commandsRead
  exact ⟨outFit, bitFit, used, suffix, chunks.flatten, ⟨chunks, out.runs, chain, rfl⟩, split, next, pos⟩

private theorem readBody_sound : BodySound Stream.InsertCopy.Internal.readBody Payload :=
  readBodyWith_sound (onError := Stream.InsertCopy.Error.envelope) (compressed := Stream.InsertCopy.Internal.readPayload)
    (wire := Payload) readPayload_sound

theorem decode_sound {limits : Stream.Limits} {input : List UInt8} {final : Execute.State}
    (read : Stream.InsertCopy.decode limits input = .ok final) :
    input.length ≤ limits.input ∧ 8 * input.length ≤ limits.bits ∧ final.output.size ≤ limits.output ∧
    ∃ window chunks, Wire input window chunks final ∧ 10 ≤ window ∧ window ≤ 24 ∧
      windowSize window ≤ limits.window ∧ chunks.length ≤ limits.blocks ∧
      0 < chunks.length ∧ chunks.length ≤ 8 * input.length ∧ final.output.toList = chunks.flatten := by
  obtain ⟨inputFit, bitFit, outFit, window, chunks, accepted, lower, upper, winFit, steps⟩ :=
    decodeWith_sound (onError := Stream.InsertCopy.Error.envelope) (body := Stream.InsertCopy.Internal.readBody) (wire := Payload)
      readBody_sound read
  obtain ⟨code, body, windowWire, split, chain⟩ := accepted
  obtain ⟨positive, progress⟩ := Stream.EnvelopeWire.progress chain
  have sourceSize := congrArg List.length split
  rw [List.length_append] at sourceSize
  have byteSize (bytes : List UInt8) : (bytesBits bytes).length = 8 * bytes.length := by
    induction bytes with
    | nil => rfl
    | cons byte rest ih =>
      simp only [bytesBits, List.flatMap_cons, List.length_append, natBits_length, List.length_cons] at *
      omega
  rw [byteSize] at sourceSize
  refine ⟨inputFit, bitFit, outFit, window, chunks, ⟨code, body, windowWire, split, chain⟩,
    lower, upper, winFit, steps, positive, by omega, ?_⟩
  simpa [Execute.State.start] using Stream.EnvelopeWire.output Payload.output chain

theorem Source.prepend {input used middle tail : List Bool} {before after : LSBReader}
    (split : input = used ++ middle) (position : after.totalRead = before.totalRead + used.length)
    {reader : LSBReader} (source : Source after.totalRead middle reader tail) :
    Source before.totalRead input reader tail := by
  obtain ⟨prefixBits, bits, sitePos, cursor⟩ := source
  refine ⟨used ++ prefixBits, ?_, ?_, cursor⟩
  · rw [split, bits, List.append_assoc]
  · rw [sitePos, position, List.length_append, Nat.add_assoc]

private theorem runCommands_error {limits : Stream.Limits} {header : CompressedHeader.Header} {block : Execute.Block}
    {index fuel command failedBlock failedCommand : Nat} {initial : State} {before : LSBReader} {input : List Bool}
    {reason : Execute.InsertCopy.Error} (cursor : Cursor before input)
    (read : Stream.InsertCopy.Internal.runCommands limits header block index fuel command initial before =
      .error (.command failedBlock failedCommand reason)) :
    failedBlock = index ∧
    ∃ passed state reader tail, passed < fuel ∧ failedCommand = command + passed ∧
      PassedCommands limits header block initial before passed state reader ∧
      Source before.totalRead input reader tail ∧
      Execute.InsertCopy.Failure header block (commandLimits limits reader) state reader tail reason := by
  induction fuel generalizing command initial before input with
  | zero => unfold Stream.InsertCopy.Internal.runCommands at read; split at read <;> cases read
  | succ fuel ih =>
    unfold Stream.InsertCopy.Internal.runCommands at read
    split at read
    · cases read
    cases step : Execute.InsertCopy.read header block (commandLimits limits before) initial before with
    | error first =>
      simp only [step, Except.mapError, bind, Except.bind] at read
      cases read
      exact ⟨rfl, 0, initial, before, input, by omega, by simp, .none .., ⟨[], rfl, by simp, cursor⟩,
        Execute.InsertCopy.read_error cursor.1 cursor.2.1 step⟩
    | ok pair =>
      obtain ⟨result, after⟩ := pair
      simp only [step, Except.mapError, bind, Except.bind] at read
      obtain ⟨_, _, _, _, _, _, used, tail, _, split, rep, count, position, _⟩ :=
        Execute.InsertCopy.read_sound cursor.1 cursor.2.1 step
      have next := cursor_advance cursor split rep count position
      obtain ⟨block, passed, state, reader, suffix, cap, command, path, source, failure⟩ := ih next read
      exact ⟨block, passed + 1, state, reader, suffix, by omega, by omega, .next step path,
        Source.prepend split position source, failure⟩

private theorem readBody_error {limits : Stream.Limits} {window index failedBlock command : Nat}
    {header : Header} {initial : Execute.State} {before : LSBReader} {input : List Bool}
    {reason : Execute.InsertCopy.Error} (cursor : Cursor before input)
    (read : Stream.InsertCopy.Internal.readBody limits window index header initial before =
      .error (.command failedBlock command reason)) :
    failedBlock = index ∧ BodyFailure limits window header initial before input command reason := by
  cases header with
  | terminal => cases read
  | metadata last length =>
    unfold Stream.InsertCopy.Internal.readBody readBodyWith at read
    cases bytes : alignedBody limits length.size before with
    | error reason => simp only [bytes, Except.mapError, bind, Except.bind] at read; cases read
    | ok pair =>
      obtain ⟨_, _⟩ := pair
      simp only [bytes, Except.mapError, bind, Except.bind] at read
      cases read
  | raw length =>
    unfold Stream.InsertCopy.Internal.readBody readBodyWith at read
    dsimp only at read
    split at read
    · cases read
    cases bytes : alignedBody limits length.size before with
    | error reason => simp only [bytes, Except.mapError, bind, Except.bind] at read; cases read
    | ok pair =>
      obtain ⟨_, _⟩ := pair
      simp only [bytes, Except.mapError, bind, Except.bind] at read
      cases read
  | compressed last length =>
    unfold Stream.InsertCopy.Internal.readBody readBodyWith at read
    dsimp only at read
    split at read
    · cases read
    cases headerRead : CompressedHeader.read
        ⟨limits.mapEntries, limits.trees, limits.bits - before.totalRead⟩ before with
    | error _ => simp only [headerRead, Except.mapError, bind, Except.bind] at read; cases read
    | ok pair =>
      obtain ⟨header, payload⟩ := pair
      simp only [headerRead, Except.mapError, bind, Except.bind] at read
      obtain ⟨_, _, _, used, tail, _, _, split, rep, count, pos, _⟩ :=
        CompressedHeader.read_sound cursor.1 cursor.2.1 headerRead
      have next := cursor_advance cursor split rep count pos
      unfold Stream.InsertCopy.Internal.readPayload at read
      cases commands : Stream.InsertCopy.Internal.runCommands limits header ⟨window, initial.output.size, length.size⟩
          index length.size 0 (State.start header initial) payload with
      | error error =>
        simp only [commands, bind, Except.bind] at read
        cases read
        obtain ⟨block, passed, state, reader, suffix, cap, count, path, source, failure⟩ :=
          runCommands_error next commands
        have indexEq : command = passed := by simpa using count
        refine ⟨block, ?_⟩
        rw [indexEq]
        exact ⟨last, length, header, payload, state, reader, suffix, rfl, headerRead, path, cap,
          Source.prepend split pos source, failure⟩
      | ok pair =>
        obtain ⟨_, _⟩ := pair
        simp only [commands, bind, Except.bind] at read
        cases read

private theorem readBlocks_error {limits : Stream.Limits} {window fuel index block command : Nat}
    {initial : Execute.State} {before : LSBReader} {input : List Bool} {reason : Execute.InsertCopy.Error}
    (cursor : Cursor before input) (outFits : initial.output.size ≤ limits.output)
    (read : readBlocksWith Stream.InsertCopy.Error.envelope Stream.InsertCopy.Internal.readBody limits window fuel index initial before =
      .error (.command block command reason)) :
    CommandFailure limits window block command reason index initial before input := by
  induction fuel generalizing index initial before input with
  | zero => cases read
  | succ fuel ih =>
    unfold readBlocksWith at read
    cases head : readHeader before with
    | error _ => simp only [head, Except.mapError, bind, Except.bind, Function.comp_apply] at read; cases read
    | ok pair =>
      obtain ⟨header, payload⟩ := pair
      simp only [head, Except.mapError, bind, Except.bind] at read
      cases cap : withinBits limits payload with
      | error _ => simp only [cap] at read; cases read
      | ok admitted =>
        cases admitted
        simp only [cap] at read
        obtain ⟨tail, _, split, next, pos⟩ := readHeader_sound cursor head
        cases body : Stream.InsertCopy.Internal.readBody limits window index header initial payload with
        | error _ =>
          simp only [body] at read
          cases read
          obtain ⟨atBlock, witness⟩ := readBody_error next body
          subst index
          exact .here head cap ⟨header.bits, split, pos, next⟩ witness
        | ok pair =>
          obtain ⟨state, after⟩ := pair
          simp only [body] at read
          split at read
          · cases endRead : finish limits after <;> simp only [endRead] at read <;> cases read
          · rename_i more
            obtain ⟨fits, _, used, rest, _, _, restBits, afterCursor, afterPos⟩ :=
              readBody_sound next outFits (withinBits_ok cap) body
            have source : Source payload.totalRead tail after rest := ⟨used, restBits, afterPos, afterCursor⟩
            exact .more head cap body (by simpa using more) (Source.prepend split pos source)
              (ih afterCursor fits read)

theorem decode_command_error {limits : Stream.Limits} {input : List UInt8} {block command : Nat}
    {reason : Execute.InsertCopy.Error}
    (read : Stream.InsertCopy.decode limits input = .error (.command block command reason)) :
    FailureWire limits input block command reason := by
  unfold Stream.InsertCopy.decode decodeWith at read
  dsimp only at read
  split at read
  · cases read
  cases windowRead : Brotli.Internal.readWindow (start input) with
  | error _ => simp only [windowRead, Except.mapError, bind, Except.bind, Function.comp_apply] at read; cases read
  | ok pair =>
    obtain ⟨window, reader⟩ := pair
    simp only [windowRead, Except.mapError, bind, Except.bind] at read
    cases cap : withinBits limits reader with
    | error _ => simp only [cap] at read; cases read
    | ok admitted =>
      cases admitted
      simp only [cap] at read
      split at read
      · cases read
      have cursor : Cursor (start input) (bytesBits input) := by simp [Cursor, start, LSBReader.Rep, natBits]
      obtain ⟨code, tail, wire, split, next, pos⟩ := readWindow_sound cursor windowRead
      exact ⟨window, reader, code, tail, windowRead, wire, split, by simpa [start] using pos,
        readBlocks_error next (Nat.zero_le _) read⟩

private def Offset (origin : Nat) (input : List Bool) (bit : Nat) : Prop :=
  ∃ used suffix, input = used ++ suffix ∧ bit = origin + used.length

private theorem Offset.here (before : LSBReader) (input : List Bool) :
    Offset before.totalRead input before.totalRead :=
  ⟨[], input, rfl, by simp⟩

private theorem Offset.prepend {origin bit : Nat} {input tail : List Bool} {reader : LSBReader}
    (source : Source origin input reader tail) (offset : Offset reader.totalRead tail bit) :
    Offset origin input bit := by
  obtain ⟨first, splitFirst, position, _⟩ := source
  obtain ⟨second, suffix, splitSecond, reached⟩ := offset
  exact ⟨first ++ second, suffix, by rw [splitFirst, splitSecond, List.append_assoc],
    by rw [reached, position, List.length_append, Nat.add_assoc]⟩

private theorem lowerOffset {header : CompressedHeader.Header} {block : Execute.Block} {limits : Execute.Limits}
    {initial : State} {before : LSBReader} {input : List Bool} {reason : Execute.InsertCopy.Error}
    (failure : Execute.InsertCopy.Failure header block limits initial before input reason) :
    Offset before.totalRead input (commandBit reason) := by
  cases failure with
  | literalBlockTypes _ | distanceBlockTypes _ => exact Offset.here before input
  | commandTree site _ | execute site _ _ =>
    obtain ⟨used, suffix, _, split, _, position, _⟩ := site.extent
    exact ⟨used, suffix, split, position⟩
  | switch failure =>
    cases failure with
    | invalidState | singleExhausted | typeSymbol | typeRange => exact Offset.here before input
    | length _ _ _ _ _ _ split _ position _ _ =>
      exact ⟨_, _, split, by simpa only [commandBit, msbBits_length] using position⟩

private theorem CommandFailure.offset {limits : Stream.Limits} {window index block command : Nat}
    {initial : Execute.State} {before : LSBReader} {input : List Bool} {reason : Execute.InsertCopy.Error}
    (failure : CommandFailure limits window block command reason index initial before input) :
    Offset before.totalRead input (commandBit reason) := by
  induction failure with
  | here _ _ source body =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, afterFraming, lower⟩ := body
    exact Offset.prepend source (Offset.prepend afterFraming (lowerOffset lower))
  | more _ _ _ _ source _ ih => exact Offset.prepend source ih

theorem decode_command_offset {limits : Stream.Limits} {input : List UInt8} {block command : Nat}
    {reason : Execute.InsertCopy.Error} (read : Stream.InsertCopy.decode limits input = .error (.command block command reason)) :
    ∃ used suffix, bytesBits input = used ++ suffix ∧ (Error.command block command reason).bit = used.length := by
  obtain ⟨_, reader, code, tail, _, _, split, position, failure⟩ := decode_command_error read
  obtain ⟨used, suffix, consumed, bit⟩ := CommandFailure.offset failure
  exact ⟨code ++ used, suffix, by rw [split, consumed, List.append_assoc],
    by simpa only [Error.bit, List.length_append, position] using bit⟩

end Silmaril.Proofs.Formats.Compression.Brotli.Stream.InsertCopy
