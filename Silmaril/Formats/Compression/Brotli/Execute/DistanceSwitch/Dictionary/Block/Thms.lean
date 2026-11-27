module

public import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Block.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Block.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary

open Literal.Switch (Source)

/-- The output is the ordered concatenation of the original command effects. -/
theorem CommandsWire.output {header : CompressedHeader.Header} {block : Block} {limits : Limits}
    {origin before after : LSBReader} {initial final : Execute.InsertCopy.State} {input suffix : List Bool}
    {chunks : List (List UInt8)} (wire : CommandsWire header block limits origin initial before input suffix chunks final after) :
    final.execution.output.size = block.endOutput ∧
    final.execution.output.toList = initial.execution.output.toList ++ chunks.flatten :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Block.CommandsWire.output wire

/-- Success accounts for every bit and command slot, returns exactly MLEN new bytes,
    and carries the final runs and ring from the witnessed command chain. -/
theorem readBlock_sound {header : CompressedHeader.Header} {window length commandCap : Nat} {limits : Limits}
    {initial : Execute.State} {final : Execute.InsertCopy.State} {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : readBlock header window length commandCap limits initial before = .ok (final, after)) :
    final.execution.output.size = initial.output.size + length ∧ final.execution.output.size ≤ limits.output ∧
    ∃ used suffix chunks,
      CommandsWire header ⟨window, initial.output.size, length⟩ limits before
        (Execute.InsertCopy.State.start header initial) before input suffix chunks final after ∧
      final.execution.output.toList = initial.output.toList ++ chunks.flatten ∧
      chunks.length ≤ commandCap ∧ Source before after input used suffix ∧ used.length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Block.readBlock_sound rep count parsed

/-- A command cause uses an available slot. Fuel exhaustion identifies the
    first pending command after the last available slot. -/
theorem FailurePath.locate {header : CompressedHeader.Header} {block : Block} {limits : Limits}
    {origin before : LSBReader} {fuel index : Nat} {state : Execute.InsertCopy.State} {input : List Bool}
    {error : BlockError} (rep : before.Rep input) (count : before.count < 8)
    (failed : FailurePath header block limits origin fuel index state before input error) :
    (∃ used suffix, input = used ++ suffix ∧ error.bit = before.totalRead + used.length) ∧
    match error with
    | .initialOutput _ => False
    | .fuel exhausted _ => exhausted = index + fuel
    | .command failedIndex _ => index ≤ failedIndex ∧ failedIndex < index + fuel :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Block.FailurePath.locate rep count failed

/-- The first error retains its original bit offset and earlier command path. -/
theorem readBlock_error {header : CompressedHeader.Header} {window length commandCap : Nat}
    {limits : Limits} {initial : Execute.State} {before : LSBReader} {input : List Bool}
    {error : BlockError} (rep : before.Rep input) (count : before.count < 8)
    (parsed : readBlock header window length commandCap limits initial before = .error error) :
    (∃ used suffix, input = used ++ suffix ∧ error.bit = before.totalRead + used.length) ∧
      match error with
      | .initialOutput bit => limits.output < initial.output.size ∧ bit = before.totalRead
      | .fuel .. | .command .. =>
        FailurePath header ⟨window, initial.output.size, length⟩ limits before commandCap 0
          (Execute.InsertCopy.State.start header initial) before input error :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Block.readBlock_error rep count parsed

end Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary
