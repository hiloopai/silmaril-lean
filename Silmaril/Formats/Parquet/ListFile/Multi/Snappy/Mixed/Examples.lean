module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed.Defs

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed

private def mixed : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-snappy-mixed/assembled-mixed.parquet"⟩

private def continued : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-snappy-mixed/assembled-v1-continuation.parquet"⟩

private def first : List ListPage.Row :=
  [none, some [], some (List.replicate 7 (some (-2147483648)) ++ [none]),
    some [some (-2147483648), some 2147483647]]

private def last : ListPage.Row :=
  some (List.replicate 32 (some 0) ++ [none] ++ List.replicate 7 (some 0))

private def second : List ListPage.Row :=
  [none, some [], some [some (-7), none], last]

private def continuedRows : List ListPage.Row :=
  [none, some [], some [some (-7), none, some 0, none], last]

private def observed (source : Bytes) (limits : Limits := {}) :
    Option (Arrow.ListInt32.Field × List (List ListPage.Row)) := do
  let ipc ← (convert limits source).wire.toOption
  let decoded ← (Arrow.ListInt32.Stream.read limits.ipc ipc).toOption
  pure (decoded.field, decoded.batches.map (·.rows))

set_option synthInstance.maxSize 1024

#guard observed mixed = some (⟨"items", "element"⟩, [first, second])
#guard observed continued = some (⟨"items", "element"⟩, [first, continuedRows])
#guard observed mixed { maxExpandedBytes := 267 } = some (⟨"items", "element"⟩, [first, second])
#guard (convert { maxExpandedBytes := 266, ipc.totalRows := 0 } mixed).wire.map (fun _ => ()) =
  .error (.source (.groupFailure 1 (.frame 3 267 (.expandedBudget 164 165))))

-- Explicit version and codec-zero entry points still have their original admission.
#guard (Snappy.convert {} mixed).wire.map (fun _ => ()) =
  .error (.source (.groupFailure 0 (.frame 1 40 (.page .pageKind))))
#guard (Snappy.convertV2 {} mixed).wire.map (fun _ => ()) =
  .error (.source (.groupFailure 0 (.frame 0 4 (.page .pageKind))))
#guard (ListFile.openFile {} mixed).toOption.map (·.readGroup 0) = some (.error (.codec 1))

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed
