module

public import Silmaril.Formats.Compression.Brotli.Stream.InsertCopy.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Stream.InsertCopy.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Stream.InsertCopy

/-- Accepted commands append exactly the modeled bytes, with one unit
    of command fuel justified by each nonempty output chunk. -/
theorem CommandsWire.output {header : CompressedHeader.Header} {block : Execute.Block}
    {initial final : Execute.InsertCopy.State} {bits : List Bool} {chunks : List (List UInt8)}
    (wire : CommandsWire header block initial bits chunks final) :
    final.execution.output.size = block.endOutput ∧
    final.execution.output.toList = initial.execution.output.toList ++ chunks.flatten ∧
    chunks.length ≤ chunks.flatten.length :=
  Proofs.Formats.Compression.Brotli.Stream.InsertCopy.CommandsWire.output wire

theorem Payload.output {header : CompressedHeader.Header} {block : Execute.Block} {initial final : Execute.State}
    {bits : List Bool} {chunk : List UInt8} (start : block.start = initial.output.size)
    (wire : Payload header block initial bits chunk final) :
    final.output.toList = initial.output.toList ++ chunk ∧ chunk.length = block.length :=
  Proofs.Formats.Compression.Brotli.Stream.InsertCopy.Payload.output start wire

/-- The exact original stream is accounted for through final zero fill,
    with ordered output and cumulative limits. The payload witness
    initializes fresh run state for each compressed meta-block. -/
theorem decode_sound {limits : Limits} {input : List UInt8} {final : Execute.State}
    (read : decode limits input = .ok final) :
    input.length ≤ limits.input ∧ 8 * input.length ≤ limits.bits ∧ final.output.size ≤ limits.output ∧
    ∃ window chunks, Wire input window chunks final ∧ 10 ≤ window ∧ window ≤ 24 ∧
      windowSize window ≤ limits.window ∧ chunks.length ≤ limits.blocks ∧
      0 < chunks.length ∧ chunks.length ≤ 8 * input.length ∧ final.output.toList = chunks.flatten :=
  Proofs.Formats.Compression.Brotli.Stream.InsertCopy.decode_sound read

/-- Every earlier block and command succeeded. The first lower error
    is witnessed at its original cursor and exact block and command indices. -/
theorem decode_command_error {limits : Limits} {input : List UInt8} {block command : Nat}
    {reason : Execute.InsertCopy.Error}
    (read : decode limits input = .error (.command block command reason)) :
    FailureWire limits input block command reason :=
  Proofs.Formats.Compression.Brotli.Stream.InsertCopy.decode_command_error read

theorem decode_command_offset {limits : Limits} {input : List UInt8} {block command : Nat}
    {reason : Execute.InsertCopy.Error} (read : decode limits input = .error (.command block command reason)) :
    ∃ used suffix, bytesBits input = used ++ suffix ∧ (Error.command block command reason).bit = used.length :=
  Proofs.Formats.Compression.Brotli.Stream.InsertCopy.decode_command_offset read

end Silmaril.Formats.Compression.Brotli.Stream.InsertCopy
