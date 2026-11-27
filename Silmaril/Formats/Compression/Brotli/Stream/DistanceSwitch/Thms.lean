module

public import Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Stream.DistanceSwitch.Contracts
import Silmaril.Proofs.Formats.Compression.Brotli.Stream.DistanceSwitch.Failure

public section

namespace Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch

theorem Payload.output {header : CompressedHeader.Header} {block : Execute.Block} {initial final : Execute.State}
    {bits : List Bool} {chunk : List UInt8} (wire : Payload header block initial bits chunk final) :
    final.output.toList = initial.output.toList ++ chunk ∧ chunk.length = block.length :=
  Proofs.Formats.Compression.Brotli.Stream.DistanceSwitch.Payload.output wire

/-- The original input includes exactly the admitted blocks and their
    terminal zero fill. Each block receives the prior execution state. -/
theorem decode_sound {limits : Limits} {input : List UInt8} {final : Execute.State}
    (read : decode limits input = .ok final) :
    input.length ≤ limits.input ∧ 8 * input.length ≤ limits.bits ∧ final.output.size ≤ limits.output ∧
    ∃ window chunks, Wire input window chunks final ∧ 10 ≤ window ∧ window ≤ 24 ∧
      windowSize window ≤ limits.window ∧ chunks.length ≤ limits.blocks ∧
      0 < chunks.length ∧ chunks.length ≤ 8 * input.length ∧ final.output.toList = chunks.flatten :=
  Proofs.Formats.Compression.Brotli.Stream.DistanceSwitch.decode_sound read

/-- All earlier blocks in the witness succeeded. A failed command keeps
    its checked table header, successful command prefix and typed cause. -/
theorem decode_error {limits : Limits} {input : List UInt8} {error : Error}
    (read : decode limits input = .error error) : FailureWire limits input error :=
  Proofs.Formats.Compression.Brotli.Stream.DistanceSwitch.decode_failure read

theorem FailureWire.offset {limits : Limits} {input : List UInt8} {error : Error}
    (failed : FailureWire limits input error) :
    ∃ used suffix, bytesBits input = used ++ suffix ∧ error.bit = used.length :=
  Proofs.Formats.Compression.Brotli.Stream.DistanceSwitch.FailureWire.offset failed

end Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch
