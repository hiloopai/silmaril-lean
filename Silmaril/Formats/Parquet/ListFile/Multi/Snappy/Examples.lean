module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Defs

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy

private def native : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-list-snappy-v1/native-crc-v1.parquet"⟩

private def optional : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-list-snappy-v1/native-no-crc-v1.parquet"⟩

private def continued : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-list-snappy-v1/assembled-continuation-v1.parquet"⟩

private def first : List ListPage.Row :=
  [none, some [], some (List.replicate 7 (some (-2147483648)) ++ [none]), some [some 2147483647, none]]

private def second : List ListPage.Row :=
  [none, some [], some [some (-7), none], some [some 0, none]]

private def continuedRows : List ListPage.Row :=
  [none, some [], some [some (-7), none, some 0, none]]

private def observed (source : Bytes) (limits : Limits := {}) :
    Option (Arrow.ListInt32.Field × List (List ListPage.Row)) := do
  let ipc ← (convert limits source).wire.toOption
  let decoded ← (Arrow.ListInt32.Stream.read limits.ipc ipc).toOption
  pure (decoded.field, decoded.batches.map (·.rows))

private def outcome (source : Bytes) (limits : Limits := {}) : Except Error Unit :=
  (convert limits source).wire.map (fun _ => ())

set_option synthInstance.maxSize 1024

#guard observed native = some (⟨"items", "element"⟩, [first, second])
#guard observed optional = some (⟨"items", "element"⟩, [first, second])
#guard observed continued = some (⟨"items", "element"⟩, [first, continuedRows])

-- Exactly 140 expanded bytes cover the original eight pages, including the levels.
#guard observed native { maxExpandedBytes := 140 } = some (⟨"items", "element"⟩, [first, second])
#guard outcome native { maxExpandedBytes := 139, ipc.totalRows := 0 } =
  .error (.source (.groupFailure 1 (.frame 3 292 (.expandedBudget 16 17))))

#guard outcome native { ipc.totalRows := 0 } = .error (.writer .rowLimit)
#guard outcome native { maxStoredPageBytes := 13 } =
  .error (.source (.groupFailure 0 (.frame 0 4 (.checksum .byteLimit))))
#guard outcome native { parquet.file.page.maxBodyBytes := 40 } =
  .error (.source (.groupFailure 0 (.frame 2 81 (.payload .outputLimit))))
#guard outcome native { parquet.maxGroupSlots := 11 } =
  .error (.source (.groupFailure 0 .slotLimit))
#guard outcome native { parquet.file.framing.maxPages := 3 } =
  .error (.source (.groupFailure 0 (.framing (.framing .pageLimit))))

-- Existing readers still require codec 0, and the opt-in reader requires 1.
#guard (ListFile.openFile {} native).toOption.map (·.readGroup 0) =
  some (.error (.codec 1))
#guard (ListFile.openFile {} native).toOption.map (fun checked => Multi.readGroup 100 checked 0) =
  some (.error (.framing (.codec 1)))
#guard outcome ⟨include_bytes "../../../../../../data/parquet-list-continuation/native-v1.parquet"⟩ =
  .error (.source (.groupFailure 0 (.framing (.codec 0))))

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy
