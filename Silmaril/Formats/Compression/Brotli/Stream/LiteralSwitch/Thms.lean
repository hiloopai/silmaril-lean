module

public import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Stream.LiteralSwitch.Contracts
import Silmaril.Proofs.Formats.Compression.Brotli.Stream.LiteralSwitch.Failure

public section

namespace Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch

theorem Payload.output {header : CompressedHeader.Header} {block : Execute.Block} {initial final : Execute.State}
    {bits : List Bool} {chunk : List UInt8} (wire : Payload header block initial bits chunk final) :
    final.output.toList = initial.output.toList ++ chunk ∧ chunk.length = block.length :=
  Proofs.Formats.Compression.Brotli.Stream.LiteralSwitch.Payload.output wire

/-- Every compressed meta-block has fresh runs and inherits the exact
    predecessor execution state. The envelope accounts for all original
    bits including the first last flag and final zero fill. -/
theorem decode_sound {limits : Limits} {input : List UInt8} {final : Execute.State}
    (read : decode limits input = .ok final) :
    input.length ≤ limits.input ∧ 8 * input.length ≤ limits.bits ∧ final.output.size ≤ limits.output ∧
    ∃ window chunks, Wire input window chunks final ∧ 10 ≤ window ∧ window ≤ 24 ∧
      windowSize window ≤ limits.window ∧ chunks.length ≤ limits.blocks ∧
      0 < chunks.length ∧ chunks.length ≤ 8 * input.length ∧ final.output.toList = chunks.flatten :=
  Proofs.Formats.Compression.Brotli.Stream.LiteralSwitch.decode_sound read

/-- The offset is in the original stream. For command errors the witness
    follows successful earlier blocks and commands to the first failure. -/
theorem decode_error {limits : Limits} {input : List UInt8} {error : Error}
    (read : decode limits input = .error error) :
    (∃ used suffix, bytesBits input = used ++ suffix ∧ error.bit = used.length) ∧
      ∀ {block command reason}, error = .block block (.command command reason) →
        CommandFailureWire limits input block command reason :=
  Proofs.Formats.Compression.Brotli.Stream.LiteralSwitch.decode_error read

end Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch
