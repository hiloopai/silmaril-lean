module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.Defs

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1

private def native : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-snappy-dictionary-v1/native-crc-v1.parquet"⟩

private def emptyDictionary : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-snappy-dictionary-v1/native-no-crc-empty-dictionary-v1.parquet"⟩

private def first : List ListPage.Row :=
  [none, some [], some [some (-7), none, some (-7), some 2147483647],
    some [some (-2147483648), some 2147483647, some (-2147483648)]]

private def second : List ListPage.Row := [some [], none, some [none, some 8, some 8],
  some [some (-11), some (-11), some 8, none]]

private def onlyNulls : List ListPage.Row := [none, some [], some [none], some [none, none]]

private def observed (source : Bytes) (limits : Limits := {}) :
    Option (Arrow.ListInt32.Field × List (List ListPage.Row)) := do
  let ipc ← (convert limits source).wire.toOption
  let decoded ← (Arrow.ListInt32.Stream.read limits.snappy.ipc ipc).toOption
  pure (decoded.field, decoded.batches.map (·.rows))

private def outcome (source : Bytes) (limits : Limits := {}) : Except Error Unit :=
  (convert limits source).wire.map (fun _ => ())

set_option synthInstance.maxSize 1024

#guard observed native = some (⟨"items", "element"⟩, [first, second])
#guard observed emptyDictionary = some (⟨"items", "element"⟩, [first, second, onlyNulls])
#guard observed native { snappy.maxExpandedBytes := 154 } = some (⟨"items", "element"⟩, [first, second])
#guard outcome native { snappy.maxExpandedBytes := 153, snappy.ipc.totalRows := 0 } =
  .error (.source (.groupFailure 1 (.frame 5 428 (.expandedBudget 15 16))))
#guard outcome native { snappy.ipc.totalRows := 0 } = .error (.writer .rowLimit)
#guard outcome native { maxEntries := 2 } = .error (.source (.groupFailure 0 (.frame 0 4 .entryLimit)))
#guard outcome native { maxDictionaryBytes := 13 } =
  .error (.source (.groupFailure 0 (.frame 0 4 (.checksum .byteLimit))))
#guard outcome native { indices := ⟨10, 2⟩ } =
  .error (.source (.groupFailure 0 (.frame 3 118 (.indices .indexByteLimit))))

#guard (Snappy.convert {} native).wire.map (fun _ => ()) =
  .error (.source (.groupFailure 0 (.framing .unsupportedOffsets)))

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1
