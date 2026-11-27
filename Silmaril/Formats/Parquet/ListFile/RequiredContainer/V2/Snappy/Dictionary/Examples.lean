module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.Defs

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary

private def native : Bytes :=
  ⟨include_bytes "../../../../../../../../data/parquet-list-required-container-v2-dictionary/native-required-v2-dictionary.parquet"⟩

private def noCrc : Bytes :=
  ⟨include_bytes "../../../../../../../../data/parquet-list-required-container-v2-dictionary/native-required-v2-dictionary-no-crc.parquet"⟩

private def plain : Bytes :=
  ⟨include_bytes "../../../../../../../../data/parquet-list-required-container-v2-snappy-multi/native-required-v2-snappy-multi-crc.parquet"⟩

private def first : List ListPage.Row :=
  [some [], some [none], some [some (-2147483648), none, some 2147483647], some [some 7, some 7]]

private def second : List ListPage.Row :=
  [some [none, none], some [], some [some 2147483647],
    some ((List.replicate 52 [some (7 : Int32), some (-2147483648)]).flatten ++ [none])]

private def observed (limits : Limits) (source : Bytes) : Option (Arrow.ListInt32.Field × List (List ListPage.Row)) := do
  let ipc ← (convert limits source).wire.toOption
  let value ← (Arrow.ListInt32.Stream.readFor false limits.snappy.ipc ipc).toOption
  pure (value.field, value.batches.map (·.rows))

private def outcome (limits : Limits) (source : Bytes) : Except (RequiredContainer.Error GroupError) Unit :=
  (convert limits source).wire.map (fun _ => ())

set_option synthInstance.maxSize 1024

#guard observed {} native = some (⟨"items", "element"⟩, [first, second])
#guard observed {} noCrc = observed {} native
#guard observed { snappy.maxExpandedBytes := 106 } native = observed {} native
#guard outcome { snappy.maxExpandedBytes := 105 } native =
  .error (.source (.groupFailure 1 (.frame 5 385 (.expandedBudget 37 38))))
#guard outcome { maxEntries := 2 } native =
  .error (.source (.groupFailure 0 (.frame 0 4 .entryLimit)))
#guard outcome { snappy.ipc.totalRows := 7 } native = .error (.writer .rowLimit)
#guard outcome {} plain = .error (.source (.groupFailure 0 (.dictionaryOffset none 4)))
#guard (Snappy.convert {} native).wire.map (fun _ => ()) =
  .error (.source (.groupFailure 0 (.framing .unsupportedOffsets)))
#guard (ListFile.openFile {} native).map (fun _ => ()) = .error .shape

end Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary
