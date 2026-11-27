module

public import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Block.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Block.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch

theorem CommandsWire.output {header : CompressedHeader.Header} {block : Block}
    {initial final : InsertCopy.State} {bits : List Bool} {chunks : List (List UInt8)}
    (wire : CommandsWire header block initial bits chunks final) :
    final.execution.output.size = block.endOutput ∧
    final.execution.output.toList = initial.execution.output.toList ++ chunks.flatten ∧
    chunks.length ≤ chunks.flatten.length :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Block.CommandsWire.output wire

/-- The fresh runs come from this block's header. The command chain
    threads the actual execution state and accounts for every consumed bit. -/
theorem readBlock_sound {header : CompressedHeader.Header} {window length : Nat} {limits : Limits}
    {initial : Execute.State} {final : InsertCopy.State} {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : readBlock header window length limits initial before = .ok (final, after)) :
    final.execution.output.size = initial.output.size + length ∧ final.execution.output.size ≤ limits.output ∧
    ∃ used suffix chunks,
      CommandsWire header ⟨window, initial.output.size, length⟩
        (InsertCopy.State.start header initial) used chunks final ∧
      final.execution.output.toList = initial.output.toList ++ chunks.flatten ∧
      chunks.length ≤ length ∧ Literal.Switch.Source before after input used suffix ∧ used.length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Block.readBlock_sound rep count parsed

/-- The error follows exactly the successful earlier commands. The
    MLEN fuel cannot exhaust before the block ends or a command fails. -/
theorem readBlock_error {header : CompressedHeader.Header} {window length : Nat}
    {limits : Limits} {initial : Execute.State} {before : LSBReader} {input : List Bool}
    {error : BlockError} (rep : before.Rep input) (count : before.count < 8)
    (parsed : readBlock header window length limits initial before = .error error) :
    (∃ used suffix, input = used ++ suffix ∧ error.bit = before.totalRead + used.length) ∧
      match error with
      | .initialOutput _ => limits.output < initial.output.size
      | .fuel .. => False
      | .command command reason =>
        BlockFailure header ⟨window, initial.output.size, length⟩ limits before command reason length 0
          (InsertCopy.State.start header initial) before input :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Block.readBlock_error rep count parsed

theorem BlockFailure.offset {header : CompressedHeader.Header} {block : Block} {limits : Limits}
    {origin before : LSBReader} {fuel index command : Nat} {state : InsertCopy.State} {input : List Bool}
    {reason : Error} (rep : before.Rep input) (count : before.count < 8)
    (failure : BlockFailure header block limits origin command reason fuel index state before input) :
    command < index + fuel ∧
    ∃ used suffix, input = used ++ suffix ∧ reason.bit = before.totalRead + used.length :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Block.BlockFailure.offset rep count failure

end Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch
