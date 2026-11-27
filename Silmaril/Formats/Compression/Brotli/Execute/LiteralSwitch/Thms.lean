module

public import Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Execute.LiteralSwitch.Contracts
import Silmaril.Proofs.Formats.Compression.Brotli.Execute.LiteralSwitch.Block

public section

namespace Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch

/-- Exact command bits in the order insert-and-copy switch, command,
    switched literal sequence, and any distance/copy tail. -/
theorem read_sound {header : CompressedHeader.Header} {block : Block} {limits : Limits}
    {initial : InsertCopy.State} {before after : LSBReader} {input : List Bool}
    {result : InsertCopy.Result} (rep : before.Rep input) (count : before.count < 8)
    (parsed : read header block limits initial before = .ok (result, after)) :
    initial.execution.output.size < result.execution.state.output.size ∧
    result.execution.state.output.size ≤ block.endOutput ∧ result.execution.state.output.size ≤ limits.output ∧
    ∃ used suffix, Wire header block initial used result ∧
      Literal.Switch.Source before after input used suffix ∧ used.length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.Execute.LiteralSwitch.read_sound rep count parsed

theorem Wire.distance_preserved {header : CompressedHeader.Header} {block : Block} {initial : InsertCopy.State}
    {bits : List Bool} {result : InsertCopy.Result} (wire : Wire header block initial bits result) :
    result.runs.distance = initial.runs.distance :=
  Proofs.Formats.Compression.Brotli.Execute.LiteralSwitch.Wire.distance_preserved wire

theorem read_error {header : CompressedHeader.Header} {block : Block} {limits : Limits}
    {initial : InsertCopy.State} {before : LSBReader} {input : List Bool} {error : Error}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : read header block limits initial before = .error error) :
    Failure header block limits initial before input error :=
  Proofs.Formats.Compression.Brotli.Execute.LiteralSwitch.read_error rep count parsed

theorem Failure.offset {header : CompressedHeader.Header} {block : Block} {limits : Limits}
    {initial : InsertCopy.State} {before : LSBReader} {input : List Bool} {error : Error}
    (rep : before.Rep input) (count : before.count < 8)
    (failure : Failure header block limits initial before input error) :
    ∃ used suffix, input = used ++ suffix ∧ error.bit = before.totalRead + used.length :=
  Proofs.Formats.Compression.Brotli.Execute.LiteralSwitch.Failure.offset rep count failure

theorem CommandsWire.output {header : CompressedHeader.Header} {block : Block}
    {initial final : InsertCopy.State} {bits : List Bool} {chunks : List (List UInt8)}
    (wire : CommandsWire header block initial bits chunks final) :
    final.execution.output.size = block.endOutput ∧
    final.execution.output.toList = initial.execution.output.toList ++ chunks.flatten ∧
    chunks.length ≤ chunks.flatten.length :=
  Proofs.Formats.Compression.Brotli.Execute.LiteralSwitch.CommandsWire.output wire

/-- The payload starts with fresh category runs and threads each
    command's actual successor into the next one. -/
theorem readBlock_sound {header : CompressedHeader.Header} {window length : Nat} {limits : Limits}
    {initial : Execute.State} {final : InsertCopy.State} {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : readBlock header window length limits initial before = .ok (final, after)) :
    final.execution.output.size = initial.output.size + length ∧ final.execution.output.size ≤ limits.output ∧
    ∃ used suffix chunks,
      CommandsWire header ⟨window, initial.output.size, length⟩
        (InsertCopy.State.start header initial) used chunks final ∧
      final.execution.output.toList = initial.output.toList ++ chunks.flatten ∧ chunks.length ≤ length ∧
      Literal.Switch.Source before after input used suffix ∧ used.length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.Execute.LiteralSwitch.readBlock_sound rep count parsed

/-- A command error follows only successful earlier commands. Within
    the failing command the witness identifies the first failed stage. -/
theorem readBlock_command_error {header : CompressedHeader.Header} {window length command : Nat}
    {limits : Limits} {initial : Execute.State} {before : LSBReader} {input : List Bool}
    {reason : Error} (rep : before.Rep input) (count : before.count < 8)
    (parsed : readBlock header window length limits initial before = .error (.command command reason)) :
    BlockFailure header ⟨window, initial.output.size, length⟩ limits before command reason length 0
      (InsertCopy.State.start header initial) before input :=
  Proofs.Formats.Compression.Brotli.Execute.LiteralSwitch.readBlock_command_error rep count parsed

theorem BlockFailure.offset {header : CompressedHeader.Header} {block : Block} {limits : Limits}
    {origin before : LSBReader} {fuel index command : Nat} {state : InsertCopy.State} {input : List Bool}
    {reason : Error} (rep : before.Rep input) (count : before.count < 8)
    (failure : BlockFailure header block limits origin command reason fuel index state before input) :
    command < index + fuel ∧
    ∃ used suffix, input = used ++ suffix ∧ reason.bit = before.totalRead + used.length :=
  Proofs.Formats.Compression.Brotli.Execute.LiteralSwitch.BlockFailure.offset rep count failure

end Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch
