module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Defs

namespace Silmaril.Formats.Parquet.ListFile.Multi.ToIpc

private def groups : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-list-file/nullable-int32-v1.parquet"⟩

private def continued : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-list-continuation/authored-continuation-v1.parquet"⟩

private def noGroups : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-list-to-ipc/no-groups.parquet"⟩

private def emptyGroup : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-list-to-ipc/empty-framed-group.parquet"⟩

private def first : List ListPage.Row :=
  [none, some [], some [none], some [some (-7), none, some 0], some [some 9, none]]

private def second : List ListPage.Row :=
  [some [some 10, none], none, some [], some [none, some (-2147483648)], some [some 2147483647, none]]

private def observe (source : Bytes) : Option (Arrow.ListInt32.Field × List (List ListPage.Row)) := do
  let bytes ← (convert {} source).wire.toOption
  let native ← (Arrow.ListInt32.Stream.read {} bytes).toOption
  pure (native.field, native.batches.map (·.rows))

set_option synthInstance.maxSize 1024

#guard observe groups = some (⟨"samples", "element"⟩, [first, second])
#guard observe continued = some (⟨"items", "element"⟩, [[none, some [], some [some 11, none, some 22, none]]])
#guard observe noGroups = some (⟨"samples", "element"⟩, [])
#guard observe emptyGroup = some (⟨"samples", "element"⟩, [first, [], second])

-- The second footer group fails before the writer's zero-row budget is checked.
#guard Id.run do
  let damaged := Bytes.ofList (groups.toList.set 72 0xa3)
  let converted := convert { ipc.totalRows := 0 } damaged
  let failure : Multi.Error := .groupFailure 1 (.frame 0 48 (.page .continuationWithoutList))
  let .ok ⟨schema, trace⟩ := converted.trace | return false
  let some column := (List.finRange schema.width).head? | return false
  return decide (trace.batches.map (·.values column) = [first] ∧
    trace.termination = .readError failure ∧ converted.wire.map (fun _ => ()) = .error (.source failure))

-- A writer refusal leaves the complete source trace available.
#guard Id.run do
  let converted := convert { ipc.totalChildren := 0 } groups
  let .ok ⟨_, trace⟩ := converted.trace | return false
  return decide (trace.batches.length = 2 ∧ trace.termination = .eos ∧
    converted.wire.map (fun _ => ()) = .error (.writer .childLimit))

#guard (convert { parquet.file.maxFileBytes := 0 } groups).wire.map (fun _ => ()) =
  .error (.source (.openFailure .fileLimit))

end Silmaril.Formats.Parquet.ListFile.Multi.ToIpc
