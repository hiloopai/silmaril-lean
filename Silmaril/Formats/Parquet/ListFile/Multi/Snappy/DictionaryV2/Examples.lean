module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.Defs

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2

private def native : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-snappy-dictionary-v2/native-crc-v2.parquet"⟩

private def emptyDictionary : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-snappy-dictionary-v2/native-no-crc-empty-dictionary-v2.parquet"⟩

private def defaultFlag : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-snappy-dictionary-v2/assembled-default-v2.parquet"⟩

private def first : List ListPage.Row :=
  [none, some [], some [some (-7), none, some (-7), some 2147483647],
    some [some (-2147483648), some 2147483647, some (-2147483648)]]

private def second : List ListPage.Row :=
  [some [], none, some [none, some 8, some 8],
    some ((List.replicate 256 [some (-11), some 8]).flatten ++ [none, some 8])]

private def onlyNulls : List ListPage.Row := [none, some [], some [none], some [none, none]]

private def observed (source : Bytes) (limits : DictionaryV1.Limits := {}) :
    Option (Arrow.ListInt32.Field × List (List ListPage.Row)) := do
  let ipc ← (convert limits source).wire.toOption
  let decoded ← (Arrow.ListInt32.Stream.read limits.snappy.ipc ipc).toOption
  pure (decoded.field, decoded.batches.map (·.rows))

private def outcome (source : Bytes) (limits : DictionaryV1.Limits := {}) : Except DictionaryV1.Error Unit :=
  (convert limits source).wire.map (fun _ => ())

set_option synthInstance.maxSize 1024

#guard observed native = some (⟨"items", "element"⟩, [first, second])
#guard observed emptyDictionary = some (⟨"items", "element"⟩, [first, second, onlyNulls])
#guard observed defaultFlag = some (⟨"items", "element"⟩, [first, second])
#guard observed native { snappy.maxExpandedBytes := 145 } = some (⟨"items", "element"⟩, [first, second])
#guard outcome native { snappy.maxExpandedBytes := 144, snappy.ipc.totalRows := 0 } =
  .error (.source (.groupFailure 1 (.frame 5 384 (.expandedBudget 78 79))))
#guard outcome native { snappy.maxStoredPageBytes := 22 } =
  .error (.source (.groupFailure 1 (.frame 5 384 (.checksum .byteLimit))))
#guard outcome native { snappy.parquet.file.page.maxBodyBytes := 78 } =
  .error (.source (.groupFailure 1 (.frame 5 384 (.v2 (.payload .outputLimit)))))
#guard outcome native { snappy.parquet.file.page.levels := ⟨1024 * 1024, 5⟩ } =
  .error (.source (.groupFailure 1 (.frame 5 384 (.v2 .v2LevelLimit))))
#guard outcome native { snappy.ipc.totalRows := 0 } = .error (.writer .rowLimit)

#guard (DictionaryV1.convert {} native).wire.map (fun _ => ()) =
  .error (.source (.groupFailure 0 (.frame 1 38 .expectedDataV1)))
#guard outcome ⟨include_bytes "../../../../../../../data/parquet-list-snappy-dictionary-v1/native-crc-v1.parquet"⟩ =
  .error (.source (.groupFailure 0 (.frame 1 38 (.v2 (.page .pageKind)))))
#guard (Snappy.convertV2 {} native).wire.map (fun _ => ()) =
  .error (.source (.groupFailure 0 (.framing .unsupportedOffsets)))

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2
