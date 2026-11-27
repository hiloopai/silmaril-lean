module

public import Silmaril.Formats.Compression.Brotli.Execute.InsertCopy.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Execute.InsertCopy.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Execute.InsertCopy

/-- A checked header contains the original 704-symbol command tree for
    every in-range insert-and-copy type. -/
theorem selected_tree_exists {header : CompressedHeader.Header} {work : Nat} {bits : List Bool}
    {run : BlockTypes.Switch.Run} (wire : CompressedHeader.Wire work bits header)
    (valid : run.Valid header.initial.controls.insertCopy) :
    ∃ table, header.insertCopyTrees[run.current]? = some table ∧ table.alphabetSize = 704 :=
  Proofs.Formats.Compression.Brotli.Execute.InsertCopy.selected_tree_exists wire valid

/-- The selected ordinal indexes the original command tree group, and
    the existing executor uses the residual bits and output budget. -/
theorem read_sound {header : CompressedHeader.Header} {block : Block} {limits : Limits}
    {initial : State} {before after : LSBReader} {input : List Bool} {result : Result}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read header block limits initial before = .ok (result, after)) :
    result.runs.insertCopy.Valid header.initial.controls.insertCopy ∧
    result.runs.literal = initial.runs.literal ∧ result.runs.distance = initial.runs.distance ∧
    initial.execution.output.size < result.execution.state.output.size ∧
    result.execution.state.output.size ≤ block.endOutput ∧ result.execution.state.output.size ≤ limits.output ∧
    ∃ used suffix, Wire header block initial used result ∧ input = used ++ suffix ∧ after.Rep suffix ∧
      after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧ used.length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.Execute.InsertCopy.read_sound rep count read

theorem read_error {header : CompressedHeader.Header} {block : Block} {limits : Limits}
    {initial : State} {before : LSBReader} {input : List Bool} {error : Error}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read header block limits initial before = .error error) :
    Failure header block limits initial before input error :=
  Proofs.Formats.Compression.Brotli.Execute.InsertCopy.read_error rep count read

end Silmaril.Formats.Compression.Brotli.Execute.InsertCopy
