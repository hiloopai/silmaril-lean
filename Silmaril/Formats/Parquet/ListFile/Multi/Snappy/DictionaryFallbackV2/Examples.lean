module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.Defs

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2

private def native : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-snappy-dictionary-fallback-v2/native-fallback-v2.parquet"⟩

private def dictionaryOnly : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-snappy-dictionary-v2/native-crc-v2.parquet"⟩

private def plainOnly : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-snappy-v2/native-crc-v2.parquet"⟩

private def first : List ListPage.Row :=
  [none, some [], some [none, some (-2147483648), some (-2147483648)], some [some (-2147483648)],
    some [some 0, some 1, some 2, some 3, some 4, some 5], some [some 2147483647, none],
    some (List.replicate 20 (some 6)), some ((List.replicate 16 [some 7, none]).flatten)]

private def second : List ListPage.Row :=
  [some [], none, some [none, some (-7), some (-7)], some [some (-7)],
    some [some (-1), some 0, some 1, some 2, some 3, some 4], some [some (-2147483648), none],
    some (List.replicate 20 (some 2147483647)), some ((List.replicate 16 [some (-8), none]).flatten)]

private def observed (source : Bytes) (limits : DictionaryV1.Limits := {}) :
    Option (Arrow.ListInt32.Field × List (List ListPage.Row)) := do
  let ipc ← (convert limits source).wire.toOption
  let decoded ← (Arrow.ListInt32.Stream.read limits.snappy.ipc ipc).toOption
  pure (decoded.field, decoded.batches.map (·.rows))

private def outcome (source : Bytes) (limits : DictionaryV1.Limits := {}) : Except DictionaryV1.Error Unit :=
  (convert limits source).wire.map (fun _ => ())

set_option synthInstance.maxSize 1024

#guard observed native = some (⟨"items", "element"⟩, [first, second])
#guard observed native { snappy.maxExpandedBytes := 468 } = some (⟨"items", "element"⟩, [first, second])
#guard outcome native { snappy.maxExpandedBytes := 467, snappy.ipc.totalRows := 0 } =
  .error (.source (.groupFailure 1 (.frame 8 698 (.v2 (.expandedBudget 76 77)))))
#guard outcome native { snappy.ipc.totalRows := 0 } = .error (.writer .rowLimit)
#guard outcome dictionaryOnly = .error (.source (.groupFailure 0 .missingPlainSuffix))
#guard outcome plainOnly = .error (.source (.groupFailure 0 (.dictionaryOffset none 4)))

#guard (DictionaryV2.convert {} native).wire.map (fun _ => ()) =
  .error (.source (.groupFailure 0 (.frame 6 238 (.dataEncoding 0))))
#guard (Snappy.convertV2 {} native).wire.map (fun _ => ()) =
  .error (.source (.groupFailure 0 (.framing .unsupportedOffsets)))

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2
