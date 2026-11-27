module

public import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch

/-- The shared parser commits exactly the original command, literal,
    distance switch and distance-code bits with a single command cap. -/
theorem readWith_sound {finishCopy : Internal.FinishCopy} {header : CompressedHeader.Header}
    {block : Block} {limits : Limits} {initial : InsertCopy.State}
    {before after : LSBReader} {input : List Bool} {result : InsertCopy.Result}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : Internal.readWith finishCopy header block limits initial before = .ok (result, after)) :
    ∃ used suffix, ReadWire finishCopy header block limits initial used result ∧
      Literal.Switch.Source before after input used suffix ∧ used.length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.readWith_sound rep count parsed

/-- On a pending explicit copy the source contains the distance switch
    before the selected context row's code and extra bits. -/
theorem read_sound {header : CompressedHeader.Header} {block : Block} {limits : Limits}
    {initial : InsertCopy.State} {before after : LSBReader} {input : List Bool}
    {result : InsertCopy.Result} (rep : before.Rep input) (count : before.count < 8)
    (parsed : read header block limits initial before = .ok (result, after)) :
    initial.execution.output.size < result.execution.state.output.size ∧
    result.execution.state.output.size ≤ block.endOutput ∧ result.execution.state.output.size ≤ limits.output ∧
    ∃ used suffix, Wire header block initial used result ∧
      Literal.Switch.Source before after input used suffix ∧ used.length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.read_sound rep count parsed

theorem Wire.output_count {header : CompressedHeader.Header} {block : Block} {initial : InsertCopy.State}
    {bits : List Bool} {result : InsertCopy.Result} (wire : Wire header block initial bits result) :
    result.execution.state.output.size = initial.execution.output.size + result.execution.command.insertLength +
      (if result.execution.distance.isSome then result.execution.command.copyLength else 0) :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Wire.output_count wire

theorem SelectionWire.other_runs {control : BlockTypes.Control} {command : Command.Value}
    {initial final : BlockTypes.Switch.State} {bits : List Bool}
    (wire : SelectionWire control command initial bits final) :
    final.literal = initial.literal ∧ final.insertCopy = initial.insertCopy :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.SelectionWire.other_runs wire

/-- An implicit distance and a literal-only ending preserve both the D
    run and the recent-distance ring. -/
theorem Wire.no_distance_symbol {header : CompressedHeader.Header} {block : Block}
    {initial : InsertCopy.State} {bits : List Bool} {result : InsertCopy.Result}
    (wire : Wire header block initial bits result)
    (absent : result.execution.distance = none ∨ result.execution.command.distance = .implicitZero) :
    result.runs.distance = initial.runs.distance ∧ result.execution.state.ring = initial.execution.ring :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Wire.no_distance_symbol wire absent

theorem readWith_error {finishCopy : Internal.FinishCopy} {header : CompressedHeader.Header} {block : Block} {limits : Limits}
    {initial : InsertCopy.State} {before : LSBReader} {input : List Bool} {error : Error}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : Internal.readWith finishCopy header block limits initial before = .error error) :
    Failure header block limits initial before input error finishCopy :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.readWith_error rep count parsed

theorem read_error {header : CompressedHeader.Header} {block : Block} {limits : Limits}
    {initial : InsertCopy.State} {before : LSBReader} {input : List Bool} {error : Error}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : read header block limits initial before = .error error) :
    Failure header block limits initial before input error :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.read_error rep count parsed

theorem Failure.offset {finishCopy : Internal.FinishCopy} {header : CompressedHeader.Header} {block : Block} {limits : Limits}
    {initial : InsertCopy.State} {before : LSBReader} {input : List Bool} {error : Error}
    (rep : before.Rep input) (count : before.count < 8)
    (failed : Failure header block limits initial before input error finishCopy) :
    ∃ used suffix, input = used ++ suffix ∧ error.bit = before.totalRead + used.length :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Failure.offset rep count failed

end Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch
