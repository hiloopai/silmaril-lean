module

public import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
import Silmaril.Formats.Compression.Brotli.Stream.Thms
import Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch.Thms
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Stream.LiteralSwitch

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch
open Silmaril.Formats.Compression.Brotli.Stream.Internal

theorem Payload.output {header : CompressedHeader.Header} {block : Execute.Block} {initial final : Execute.State}
    {bits : List Bool} {chunk : List UInt8}
    (wire : Payload header block initial bits chunk final) :
    final.output.toList = initial.output.toList ++ chunk ∧ chunk.length = block.length := by
  obtain ⟨chunks, runs, wire, rfl⟩ := wire
  obtain ⟨last, output, _⟩ := Execute.LiteralSwitch.CommandsWire.output wire
  change final.output.toList = initial.output.toList ++ chunks.flatten at output
  change final.output.size = initial.output.size + block.length at last
  have len := congrArg List.length output
  simp only [Array.length_toList, List.length_append] at len
  exact ⟨output, by omega⟩

private theorem readPayload_sound : PayloadSound Stream.LiteralSwitch.Internal.readPayload Payload := by
  intro limits index headerBit header block initial final before after input cursor _ bitFits read
  unfold Stream.LiteralSwitch.Internal.readPayload at read
  cases payload : Execute.LiteralSwitch.readBlock header block.windowBits block.length
      (payloadLimits limits before) initial before with
  | error reason => simp [payload, Except.mapError, bind, Except.bind] at read
  | ok pair =>
    obtain ⟨out, stop⟩ := pair
    simp only [payload, Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    obtain ⟨_, fits, used, suffix, chunks, chain, _, _, source, usedFits⟩ :=
      Execute.LiteralSwitch.readBlock_sound cursor.1 cursor.2.1 payload
    have next := cursor_advance cursor source.split source.rep source.count source.position
    change out.execution.output.size ≤ limits.output at fits
    change used.length ≤ limits.bits - before.totalRead at usedFits
    have finalFits := source.position
    exact ⟨fits, by omega, used, suffix, chunks.flatten, ⟨chunks, out.runs, chain, rfl⟩,
      source.split, next, source.position⟩

theorem readBody_sound : BodySound Stream.LiteralSwitch.Internal.readBody Payload :=
  readBodyWith_sound (onError := Error.envelope) (compressed := Stream.LiteralSwitch.Internal.readPayload)
    readPayload_sound

theorem decode_sound {limits : Stream.Limits} {input : List UInt8} {final : Execute.State}
    (read : Stream.LiteralSwitch.decode limits input = .ok final) :
    input.length ≤ limits.input ∧ 8 * input.length ≤ limits.bits ∧ final.output.size ≤ limits.output ∧
    ∃ window chunks, Wire input window chunks final ∧ 10 ≤ window ∧ window ≤ 24 ∧
      windowSize window ≤ limits.window ∧ chunks.length ≤ limits.blocks ∧
      0 < chunks.length ∧ chunks.length ≤ 8 * input.length ∧ final.output.toList = chunks.flatten := by
  obtain ⟨inputFit, bitFit, outFit, window, chunks, accepted, lower, upper, winFit, steps⟩ :=
    decodeWith_sound (onError := Error.envelope) (body := Stream.LiteralSwitch.Internal.readBody)
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
  simpa [Execute.State.start] using Stream.EnvelopeWire.output (fun _ => Payload.output) chain

end Silmaril.Proofs.Formats.Compression.Brotli.Stream.LiteralSwitch
