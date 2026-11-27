module

public import Silmaril.Formats.Compression.Brotli.Stream.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Stream.Contracts
import Silmaril.Proofs.Formats.Compression.Brotli.Stream.Failure
import Silmaril.Proofs.Formats.Compression.Brotli.Stream.Framing

public section

namespace Silmaril.Formats.Compression.Brotli.Stream

theorem CommandsWire.output {header : CompressedHeader.Header} {block : Execute.Block}
    {initial final : Execute.State} {bits : List Bool} {chunks : List (List UInt8)}
    (wire : CommandsWire header block initial bits chunks final) :
    final.output.size = block.endOutput ∧ final.output.toList = initial.output.toList ++ chunks.flatten ∧
      chunks.length ≤ chunks.flatten.length :=
  Proofs.Formats.Compression.Brotli.Stream.CommandsWire.output wire

theorem BodyWire.output {window position : Nat} {header : Header} {initial final : Execute.State}
    {bits : List Bool} {chunk : List UInt8} (wire : BodyWire window position header initial bits chunk final) :
    final.output.toList = initial.output.toList ++ chunk ∧ chunk.length = header.outputSize :=
  Proofs.Formats.Compression.Brotli.Stream.BodyWire.output wire

theorem BlocksWire.progress {window position : Nat} {initial final : Execute.State}
    {bits : List Bool} {chunks : List (List UInt8)} (wire : BlocksWire window position initial bits chunks final) :
    0 < chunks.length ∧ chunks.length ≤ bits.length :=
  Proofs.Formats.Compression.Brotli.Stream.BlocksWire.progress wire

theorem BlocksWire.output {window position : Nat} {initial final : Execute.State}
    {bits : List Bool} {chunks : List (List UInt8)} (wire : BlocksWire window position initial bits chunks final) :
    final.output.toList = initial.output.toList ++ chunks.flatten :=
  Proofs.Formats.Compression.Brotli.Stream.BlocksWire.output wire

/-- Each stream byte is accounted for, including final zero fill, and the
    returned bytes and ring follow the ordered block witnesses. -/
theorem decode_sound {limits : Limits} {input : List UInt8} {final : Execute.State}
    (read : decode limits input = .ok final) :
    input.length ≤ limits.input ∧ 8 * input.length ≤ limits.bits ∧ final.output.size ≤ limits.output ∧
    ∃ window chunks, Wire input window chunks final ∧ 10 ≤ window ∧ window ≤ 24 ∧
      windowSize window ≤ limits.window ∧ chunks.length ≤ limits.blocks ∧ final.output.toList = chunks.flatten :=
  Proofs.Formats.Compression.Brotli.Stream.decode_sound read

/-- The typed cause is witnessed at a cursor into the original input at
    the reported absolute bit position. Exhausted block fuel can fail at
    index `limits.blocks`; each failing command keeps its lower error. -/
theorem decode_error {limits : Limits} {bytes : List UInt8} {error : Error}
    (read : decode limits bytes = .error error) :
    FailureWire limits 0 (bytesBits bytes) error ∧
      (error.block = none ∧ error.command = none ∨
        (∃ index ≤ limits.blocks, error.block = some index) ∧ ∃ window reader,
          Brotli.Internal.readWindow (Brotli.Internal.start bytes) = .ok (window, reader) ∧
          IndexedFailure limits window 0 Execute.State.start reader error) ∧
      error.cause ≠ .commandFuel :=
  Proofs.Formats.Compression.Brotli.Stream.decode_error read

theorem BodyWireWith.output {payload : PayloadWire} {window position : Nat} {header : Header}
    {initial final : Execute.State} {bits : List Bool} {chunk : List UInt8}
    (output : ∀ {header block initial bits chunk final}, block.start = initial.output.size →
      payload header block initial bits chunk final →
      final.output.toList = initial.output.toList ++ chunk ∧ chunk.length = block.length)
    (wire : BodyWireWith payload window position header initial bits chunk final) :
    final.output.toList = initial.output.toList ++ chunk ∧ chunk.length = header.outputSize :=
  Proofs.Formats.Compression.Brotli.Stream.BodyWireWith.output output wire

theorem EnvelopeWire.output {payload : PayloadWire} {window position : Nat} {initial final : Execute.State}
    {bits : List Bool} {chunks : List (List UInt8)}
    (output : ∀ {header block initial bits chunk final}, block.start = initial.output.size →
      payload header block initial bits chunk final →
      final.output.toList = initial.output.toList ++ chunk ∧ chunk.length = block.length)
    (wire : EnvelopeWire payload window position initial bits chunks final) :
    final.output.toList = initial.output.toList ++ chunks.flatten :=
  Proofs.Formats.Compression.Brotli.Stream.EnvelopeWire.output output wire

theorem EnvelopeWire.progress {payload : PayloadWire} {window position : Nat} {initial final : Execute.State}
    {bits : List Bool} {chunks : List (List UInt8)} (wire : EnvelopeWire payload window position initial bits chunks final) :
    0 < chunks.length ∧ chunks.length ≤ bits.length :=
  Proofs.Formats.Compression.Brotli.Stream.EnvelopeWire.progress wire

namespace Internal

theorem readHeader_sound {before after : LSBReader} {bits : List Bool} {header : Header}
    (cursor : Brotli.Internal.Cursor before bits) (read : readHeader before = .ok (header, after)) :
    ∃ tail, header.Valid ∧ bits = header.bits ++ tail ∧ Brotli.Internal.Cursor after tail ∧
      after.totalRead = before.totalRead + header.bits.length :=
  Proofs.Formats.Compression.Brotli.Stream.readHeader_sound cursor read

theorem withinBits_ok {limits : Limits} {after : LSBReader}
    (read : withinBits limits after = .ok ()) : after.totalRead ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.Stream.withinBits_ok read

theorem cursor_advance {before after : LSBReader} {input used suffix : List Bool}
    (cursor : Brotli.Internal.Cursor before input) (split : input = used ++ suffix)
    (rep : after.Rep suffix) (count : after.count < 8)
    (position : after.totalRead = before.totalRead + used.length) : Brotli.Internal.Cursor after suffix :=
  Proofs.Formats.Compression.Brotli.Stream.cursor_advance cursor split rep count position

theorem readBodyWith_sound {ε : Type} {onError : Error → ε} {compressed : ReadPayload ε}
    {wire : PayloadWire} (payloadSound : PayloadSound compressed wire) :
    BodySound (readBodyWith onError compressed) wire :=
  Proofs.Formats.Compression.Brotli.Stream.readBodyWith_sound (onError := onError)
    (compressed := compressed) (wire := wire) payloadSound

theorem decodeWith_sound {ε : Type} {onError : Error → ε} {body : ReadBody ε}
    {wire : PayloadWire} (bodySound : BodySound body wire)
    {limits : Limits} {input : List UInt8} {final : Execute.State}
    (read : decodeWith onError body limits input = .ok final) :
    input.length ≤ limits.input ∧ 8 * input.length ≤ limits.bits ∧ final.output.size ≤ limits.output ∧
    ∃ window chunks, WireWith wire input window chunks final ∧ 10 ≤ window ∧ window ≤ 24 ∧
      windowSize window ≤ limits.window ∧ chunks.length ≤ limits.blocks :=
  Proofs.Formats.Compression.Brotli.Stream.decodeWith_sound bodySound read

end Internal

end Silmaril.Formats.Compression.Brotli.Stream
