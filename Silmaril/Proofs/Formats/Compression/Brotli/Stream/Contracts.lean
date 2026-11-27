module

public import Silmaril.Formats.Compression.Brotli.Stream.Defs
import Silmaril.Formats.Compression.Brotli.Thms
import Silmaril.Formats.Compression.Bits.Thms
import Silmaril.Formats.Compression.Brotli.CompressedHeader.Thms
import Silmaril.Formats.Compression.Brotli.Execute.Thms
import Silmaril.Proofs.Formats.Compression.Brotli.Stream.Framing
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Stream

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Internal (Cursor start readWindow_sound)
open Silmaril.Formats.Compression.Brotli.Stream
open Silmaril.Formats.Compression.Brotli.Stream.Internal

theorem CommandsWire.output {header : CompressedHeader.Header} {block : Execute.Block}
    {initial final : Execute.State} {bits : List Bool} {chunks : List (List UInt8)}
    (wire : CommandsWire header block initial bits chunks final) :
    final.output.size = block.endOutput ∧ final.output.toList = initial.output.toList ++ chunks.flatten ∧
      chunks.length ≤ chunks.flatten.length := by
  induction wire with
  | done exactLength => exact ⟨exactLength, by simp, by simp⟩
  | step _ appended grows _ ih =>
    refine ⟨ih.1, ?_, ?_⟩
    · simp [ih.2.1, appended, List.append_assoc]
    · simp only [List.length_cons, List.flatten_cons, List.length_append]
      have remaining := ih.2.2
      omega

theorem BodyWire.output {window position : Nat} {header : Header} {initial final : Execute.State}
    {bits : List Bool} {chunk : List UInt8} (wire : BodyWire window position header initial bits chunk final) :
    final.output.toList = initial.output.toList ++ chunk ∧
      chunk.length = header.outputSize := by
  cases wire with
  | raw length => exact ⟨by simp, length⟩
  | terminal | metadata => simp [Header.outputSize]
  | compressed _ _ commands =>
    obtain ⟨size, append, _⟩ := CommandsWire.output commands
    have len := congrArg List.length append
    simp only [Array.length_toList, List.length_append] at len
    exact ⟨append, by simp only [Execute.Block.endOutput] at size; simp only [Header.outputSize]; omega⟩

theorem BlocksWire.output {window position : Nat} {initial final : Execute.State}
    {bits : List Bool} {chunks : List (List UInt8)} (wire : BlocksWire window position initial bits chunks final) :
    final.output.toList = initial.output.toList ++ chunks.flatten := by
  induction wire with
  | last _ _ body => simp [ (BodyWire.output body).1 ]
  | more _ _ body _ ih => simp [ih, (BodyWire.output body).1, List.append_assoc]

private theorem header_progress (header : Header) : 0 < header.bits.length := by
  cases header with
  | raw | terminal => simp [Header.bits, MetaHeader.bits]
  | compressed last | metadata last => cases last <;> simp [Header.bits, lastBits, natBits_length]

theorem BlocksWire.progress {window position : Nat} {initial final : Execute.State}
    {bits : List Bool} {chunks : List (List UInt8)} (wire : BlocksWire window position initial bits chunks final) :
    0 < chunks.length ∧ chunks.length ≤ bits.length := by
  induction wire with
  | @last _ _ _ header _ _ _ _ _ =>
    have consumed := header_progress header
    simp only [List.length_cons, List.length_nil, List.length_append]
    omega
  | @more _ _ _ _ header _ _ _ _ _ _ _ _ ih =>
    have consumed := header_progress header
    obtain ⟨nonempty, count⟩ := ih
    simp only [List.length_cons, List.length_append]
    omega

private theorem runCommands_sound {limits : Stream.Limits} {header : CompressedHeader.Header} {block : Execute.Block}
    {index fuel command : Nat} {initial final : Execute.State} {before after : LSBReader} {input : List Bool}
    (cursor : Cursor before input) (outFits : initial.output.size ≤ limits.output)
    (bitFits : before.totalRead ≤ limits.bits)
    (read : runCommands limits header block index fuel command initial before = .ok (final, after)) :
    final.output.size ≤ limits.output ∧ after.totalRead ≤ limits.bits ∧
    ∃ used suffix chunks, CommandsWire header block initial used chunks final ∧ chunks.length ≤ fuel ∧
      input = used ++ suffix ∧ Cursor after suffix ∧ after.totalRead = before.totalRead + used.length := by
  induction fuel generalizing command initial final before after input with
  | zero =>
    unfold runCommands at read
    split at read
    · rename_i done
      cases read
      exact ⟨outFits, bitFits, [], input, [], .done done, by simp, rfl, cursor, by simp⟩
    · contradiction
  | succ fuel ih =>
    unfold runCommands at read
    split at read
    · rename_i done
      cases read
      exact ⟨outFits, bitFits, [], input, [], .done done, by simp, rfl, cursor, by simp⟩
    · obtain ⟨⟨result, next⟩, commandRead, run⟩ := bind_mapped_ok read
      obtain ⟨_, _, _, _, grows, _, nextOut, used, tail, wire, split, rep, count, position, nextBits⟩ :=
        Execute.read_sound cursor.1 cursor.2.1 commandRead
      change used.length ≤ limits.bits - before.totalRead at nextBits
      have nextCursor := cursor_advance cursor split rep count position
      have nextFit : next.totalRead ≤ limits.bits := by omega
      obtain ⟨outFit, finalFit, rest, suffix, chunks, chain, steps, restBits, finalCursor, finalPosition⟩ :=
        ih nextCursor nextOut nextFit run
      obtain ⟨_, _, _, _, _, literals, _, matched, _, _, _, _, _, _, _, append⟩ := wire.parts
      have appended : result.state.output.toList = initial.output.toList ++ (literals ++ matched) := by
        simpa only [List.append_assoc] using append
      have len := congrArg List.length appended
      simp only [Array.length_toList, List.length_append] at len
      change initial.output.size < result.state.output.size at grows
      refine ⟨outFit, finalFit, used ++ rest, suffix, (literals ++ matched) :: chunks,
        .step wire appended (by simp only [List.length_append]; omega) chain, ?_, ?_, finalCursor, ?_⟩
      · simp only [List.length_cons]; omega
      · rw [split, restBits, List.append_assoc]
      · rw [finalPosition, position, List.length_append, Nat.add_assoc]

theorem readBodyWith_sound {ε : Type} {onError : Stream.Error → ε} {compressed : ReadPayload ε}
    {wire : PayloadWire} (payloadSound : PayloadSound compressed wire) :
    BodySound (readBodyWith onError compressed) wire := by
  intro limits window index header initial final before after input cursor outFits bitFits parsed
  cases header with
  | terminal =>
    cases parsed
    exact ⟨outFits, bitFits, [], input, [], .terminal initial, rfl, cursor, by simp⟩
  | metadata last length =>
    unfold readBodyWith readBodyWithResult at parsed
    obtain ⟨⟨bytes, stop⟩, bodyRead, done⟩ := bind_mapped_ok parsed
    cases done
    obtain ⟨suffix, extent, bits, next, position, fits⟩ := alignedBody_sound cursor bodyRead
    exact ⟨outFits, fits, _, suffix, [], .metadata initial extent, bits, next, position⟩
  | raw length =>
    unfold readBodyWith readBodyWithResult at parsed
    dsimp only at parsed
    split at parsed
    · contradiction
    rename_i fits
    obtain ⟨⟨bytes, stop⟩, bodyRead, done⟩ := bind_mapped_ok parsed
    cases done
    obtain ⟨suffix, extent, bits, next, position, bitCap⟩ := alignedBody_sound cursor bodyRead
    refine ⟨?_, bitCap, _, suffix, bytes, .raw extent, bits, next, position⟩
    simpa [extent] using Nat.le_of_not_gt fits
  | compressed last length =>
    unfold readBodyWith readBodyWithResult at parsed
    dsimp only at parsed
    split at parsed
    · contradiction
    obtain ⟨⟨header, payload⟩, headerRead, read⟩ := bind_mapped_ok parsed
    obtain ⟨_, _, work, used, tail, _, tables, split, rep, count, position, bits⟩ :=
      CompressedHeader.read_sound cursor.1 cursor.2.1 headerRead
    change used.length ≤ limits.bits - before.totalRead at bits
    have payloadCursor := cursor_advance cursor split rep count position
    have payloadFits : payload.totalRead ≤ limits.bits := by omega
    obtain ⟨outFit, finalFit, commands, suffix, chunk, chain, tailSplit, finalCursor, afterPos⟩ :=
      payloadSound payloadCursor outFits payloadFits read
    refine ⟨outFit, finalFit, used ++ commands, suffix, chunk, .compressed tables chain,
      ?_, finalCursor, ?_⟩
    · rw [split, tailSplit, List.append_assoc]
    · rw [afterPos, position, List.length_append, Nat.add_assoc]

private def SingleWire : PayloadWire :=
  fun header block initial bits chunk final => Execute.oneType header = true ∧
    ∃ chunks, CommandsWire header block initial bits chunks final ∧ chunk = chunks.flatten

private theorem readSinglePayload_sound : PayloadSound readSinglePayload SingleWire := by
  intro limits index headerBit header block initial final before after input cursor outFits bitFits read
  unfold readSinglePayload at read
  split at read
  · contradiction
  · rename_i profile
    obtain ⟨outFit, finalFit, commands, suffix, chunks, chain, _, tailSplit, finalCursor, afterPos⟩ :=
      runCommands_sound cursor outFits bitFits read
    exact ⟨outFit, finalFit, commands, suffix, chunks.flatten, ⟨by simpa using profile, chunks, chain, rfl⟩,
      tailSplit, finalCursor, afterPos⟩

private theorem BodyWireWith.toLegacy {window position : Nat} {header : Header} {initial final : Execute.State}
    {bits : List Bool} {chunk : List UInt8} (h : BodyWireWith SingleWire window position header initial bits chunk final) :
    BodyWire window position header initial bits chunk final := by
  cases h with
  | terminal => exact .terminal initial
  | raw size => exact .raw size
  | metadata => exact .metadata initial (by assumption)
  | compressed tables step =>
    obtain ⟨profile, _, chain, rfl⟩ := step
    exact .compressed tables profile chain

private theorem EnvelopeWire.toLegacy {window position : Nat} {initial final : Execute.State}
    {bits : List Bool} {chunks : List (List UInt8)}
    (wire : EnvelopeWire SingleWire window position initial bits chunks final) :
    BlocksWire window position initial bits chunks final := by
  induction wire with
  | last valid last body => exact .last valid last (BodyWireWith.toLegacy body)
  | more valid more body _ ih => exact .more valid more (BodyWireWith.toLegacy body) ih

theorem readBody_sound {limits : Stream.Limits} {window index : Nat} {header : Header}
    {initial final : Execute.State} {before after : LSBReader} {input : List Bool}
    (cursor : Cursor before input) (outFits : initial.output.size ≤ limits.output)
    (bitFits : before.totalRead ≤ limits.bits)
    (read : readBody limits window index header initial before = .ok (final, after)) :
    final.output.size ≤ limits.output ∧ after.totalRead ≤ limits.bits ∧
    ∃ used suffix chunk, BodyWire window before.totalRead header initial used chunk final ∧
      input = used ++ suffix ∧ Cursor after suffix ∧ after.totalRead = before.totalRead + used.length := by
  obtain ⟨out, bits, used, suffix, chunk, body, split, next, pos⟩ :=
    readBodyWith_sound (onError := id) (compressed := readSinglePayload) (wire := SingleWire)
      readSinglePayload_sound cursor outFits bitFits read
  exact ⟨out, bits, used, suffix, chunk, BodyWireWith.toLegacy body, split, next, pos⟩

theorem BodyWireWith.output {payload : PayloadWire} {window position : Nat} {header : Header}
    {initial final : Execute.State} {bits : List Bool} {chunk : List UInt8}
    (output : ∀ {header block initial bits chunk final}, block.start = initial.output.size →
      payload header block initial bits chunk final →
      final.output.toList = initial.output.toList ++ chunk ∧ chunk.length = block.length)
    (wire : BodyWireWith payload window position header initial bits chunk final) :
    final.output.toList = initial.output.toList ++ chunk ∧ chunk.length = header.outputSize := by
  cases wire with
  | raw length => exact ⟨by simp, length⟩
  | terminal | metadata => simp [Header.outputSize]
  | compressed _ step => exact output rfl step

theorem EnvelopeWire.output {payload : PayloadWire} {window position : Nat} {initial final : Execute.State}
    {bits : List Bool} {chunks : List (List UInt8)}
    (output : ∀ {header block initial bits chunk final}, block.start = initial.output.size →
      payload header block initial bits chunk final →
      final.output.toList = initial.output.toList ++ chunk ∧ chunk.length = block.length)
    (wire : EnvelopeWire payload window position initial bits chunks final) :
    final.output.toList = initial.output.toList ++ chunks.flatten := by
  induction wire with
  | last _ _ body => simp [(BodyWireWith.output output body).1]
  | more _ _ body _ ih => simp [ih, (BodyWireWith.output output body).1, List.append_assoc]

theorem EnvelopeWire.progress {payload : PayloadWire} {window position : Nat} {initial final : Execute.State}
    {bits : List Bool} {chunks : List (List UInt8)} (wire : EnvelopeWire payload window position initial bits chunks final) :
    0 < chunks.length ∧ chunks.length ≤ bits.length := by
  induction wire with
  | @last _ _ _ header _ _ _ _ _ =>
    have consumed := header_progress header
    simp only [List.length_cons, List.length_nil, List.length_append]
    omega
  | @more _ _ _ _ header _ _ _ _ _ _ _ _ ih =>
    have consumed := header_progress header
    obtain ⟨nonempty, count⟩ := ih
    simp only [List.length_cons, List.length_append]
    omega

private theorem readBlocksWith_sound {ε : Type} {onError : Stream.Error → ε} {body : ReadBody ε}
    {wire : PayloadWire} (bodySound : BodySound body wire)
    {limits : Stream.Limits} {window fuel index : Nat}
    {initial final : Execute.State} {before : LSBReader} {input : List Bool}
    (cursor : Cursor before input) (outFits : initial.output.size ≤ limits.output)
    (read : readBlocksWith onError body limits window fuel index initial before = .ok final) :
    final.output.size ≤ limits.output ∧ before.totalRead + input.length ≤ limits.bits ∧
    ∃ chunks, EnvelopeWire wire window before.totalRead initial input chunks final ∧ chunks.length ≤ fuel := by
  induction fuel generalizing index initial before input with
  | zero => contradiction
  | succ fuel ih =>
    unfold readBlocksWith readBlocksWithState at read
    obtain ⟨⟨header, payload⟩, headRead, read⟩ := bind_mapped_ok read
    obtain ⟨tail, valid, headBits, next, position⟩ := readHeader_sound cursor headRead
    obtain ⟨⟨⟩, within, read⟩ := bind_mapped_ok read
    obtain ⟨⟨stepped, after⟩, bodyRead, read⟩ := bind_ok read
    obtain ⟨fits, _, used, suffix, chunk, bodyWire, bodyBits, nextCursor, bodyPos⟩ :=
      bodySound next outFits (withinBits_ok within) bodyRead
    dsimp only at read
    have stop : after.totalRead = before.totalRead + header.bits.length + used.length := by
      rw [bodyPos, position]
    split at read
    · rename_i last
      obtain ⟨aligned, finishRead, read⟩ := bind_mapped_ok read
      obtain ⟨finalBits, alignedPos, finalCap⟩ := finish_sound nextCursor finishRead
      cases read
      refine ⟨fits, ?_, [chunk], ?_, by simp⟩
      · simp only [headBits, bodyBits, List.length_append]
        omega
      · rw [headBits, bodyBits, finalBits, stop]
        rw [position] at bodyWire
        simpa only [List.append_assoc] using EnvelopeWire.last valid last bodyWire
    · rename_i more
      have notLast : header.last = false := by simpa using more
      obtain ⟨finalFits, finalBits, chunks, chain, steps⟩ := ih nextCursor fits read
      rw [position] at bodyWire
      rw [stop] at chain
      refine ⟨finalFits, ?_, chunk :: chunks, ?_, by simpa using steps⟩
      · simp only [headBits, bodyBits, List.length_append]
        omega
      · rw [headBits, bodyBits]
        simpa only [List.append_assoc] using EnvelopeWire.more valid notLast bodyWire chain

theorem decodeWith_sound {ε : Type} {onError : Stream.Error → ε} {body : ReadBody ε}
    {wire : PayloadWire} (bodySound : BodySound body wire)
    {limits : Stream.Limits} {input : List UInt8} {final : Execute.State}
    (read : decodeWith onError body limits input = .ok final) :
    input.length ≤ limits.input ∧ 8 * input.length ≤ limits.bits ∧ final.output.size ≤ limits.output ∧
    ∃ window chunks, WireWith wire input window chunks final ∧ 10 ≤ window ∧ window ≤ 24 ∧
      windowSize window ≤ limits.window ∧ chunks.length ≤ limits.blocks := by
  unfold decodeWith decodeWithState at read
  dsimp only at read
  split at read
  · contradiction
  rename_i inputFits
  obtain ⟨⟨window, reader⟩, windowRead, read⟩ := bind_mapped_ok read
  have cursor : Cursor (start input) (bytesBits input) := by
    simp [Cursor, start, LSBReader.Rep, natBits]
  obtain ⟨code, tail, windowWire, split, next, position⟩ := readWindow_sound cursor windowRead
  obtain ⟨⟨⟩, _, read⟩ := bind_mapped_ok read
  dsimp only at read
  split at read
  · contradiction
  rename_i windowFits
  obtain ⟨outFit, bitFit, chunks, chain, steps⟩ :=
    readBlocksWith_sound bodySound next (Nat.zero_le _) read
  have pos : reader.totalRead = code.length := by simpa [start] using position
  have length := congrArg List.length split
  simp only [bytes_length, List.length_append] at length
  obtain ⟨lower, upper⟩ := WindowWire.range windowWire
  rw [pos] at chain
  exact ⟨Nat.le_of_not_gt inputFits, by omega, outFit, window, chunks,
    ⟨code, tail, windowWire, split, chain⟩, lower, upper, Nat.le_of_not_gt windowFits, steps⟩

theorem decode_sound {limits : Stream.Limits} {input : List UInt8} {final : Execute.State}
    (read : Stream.decode limits input = .ok final) :
    input.length ≤ limits.input ∧ 8 * input.length ≤ limits.bits ∧ final.output.size ≤ limits.output ∧
    ∃ window chunks, Wire input window chunks final ∧ 10 ≤ window ∧ window ≤ 24 ∧
      windowSize window ≤ limits.window ∧ chunks.length ≤ limits.blocks ∧ final.output.toList = chunks.flatten := by
  obtain ⟨inputFit, bitFit, outputFit, window, chunks, ⟨code, tail, windowWire, split, chain⟩, lower, upper, winFit, steps⟩ :=
    decodeWith_sound (onError := id) (body := readBody) (wire := SingleWire)
      (readBodyWith_sound (onError := id) (compressed := readSinglePayload) (wire := SingleWire)
        readSinglePayload_sound) read
  have legacy := EnvelopeWire.toLegacy chain
  refine ⟨inputFit, bitFit, outputFit, window, chunks, ⟨code, tail, windowWire, split, legacy⟩,
    lower, upper, winFit, steps, ?_⟩
  simpa [Execute.State.start] using BlocksWire.output legacy

end Silmaril.Proofs.Formats.Compression.Brotli.Stream
