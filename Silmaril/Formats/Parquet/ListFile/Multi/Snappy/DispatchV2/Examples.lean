module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2.Defs

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2

private def plain : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-snappy-v2-dispatch/native-plain-v2.parquet"⟩

private def native : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-snappy-v2-dispatch/native-dictionary-and-fallback-v2.parquet"⟩

private def mixed : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-snappy-v2-dispatch/assembled-three-profiles-v2.parquet"⟩

private def v1 : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-snappy-v1/native-crc-v1.parquet"⟩

private def expectedPlain : List ListPage.Row :=
  [none, some [], some [none, some (-2147483648), some 2147483647], some (List.replicate 32 (some 4))]

private def expectedDictionary : List ListPage.Row :=
  [none, some [], some [none, some (-7), some (-7)], some [some (-7)], some [none], some [some 0, some (-7)],
    some (List.replicate 16 (some 0)), some [none, some (-7)]]

private def expectedFallback : List ListPage.Row :=
  [none, some [], some [none, some (-2147483648), some (-2147483648)], some [some (-2147483648)],
    some [some 0, some 1, some 2, some 3, some 4, some 5], some [some 2147483647, none],
    some (List.replicate 20 (some 6)), some ((List.replicate 16 [some 7, none]).flatten)]

private def profiles (source : Bytes) : Option (List Profile) := do
  let checked ← (ListFile.openFile {} source).toOption
  (List.range checked.snapshot.groupCount).mapM fun ordinal => do
    let framed ← (checked.frameGroupWith 1 true ordinal).toOption
    pure (classify framed.frames)

private def observed (source : Bytes) (limits : DictionaryV1.Limits := {}) :
    Option (Arrow.ListInt32.Field × List (List ListPage.Row)) := do
  let ipc ← (convert limits source).wire.toOption
  let decoded ← (Arrow.ListInt32.Stream.read limits.snappy.ipc ipc).toOption
  pure (decoded.field, decoded.batches.map (·.rows))

private def outcome (source : Bytes) (limits : DictionaryV1.Limits := {}) : Except Error Unit :=
  (convert limits source).wire.map (fun _ => ())

set_option synthInstance.maxSize 1024

#guard profiles plain = some [.plain]
#guard profiles native = some [.dictionary, .fallback]
#guard profiles mixed = some [.plain, .dictionary, .fallback]

#guard observed plain = some (⟨"items", "element"⟩, [expectedPlain])
#guard observed native = some (⟨"items", "element"⟩, [expectedDictionary, expectedFallback])
#guard observed mixed { snappy.maxExpandedBytes := 449 } =
  some (⟨"items", "element"⟩, [expectedPlain, expectedDictionary, expectedFallback])
#guard outcome mixed { snappy.maxExpandedBytes := 448, snappy.ipc.totalRows := 0 } =
  .error (.source (.groupFailure 2 (.fallback (.frame 8 807 (.v2 (.expandedBudget 76 77))))))
#guard outcome mixed { snappy.ipc.totalRows := 0 } = .error (.writer .rowLimit)
#guard outcome v1 = .error (.source (.groupFailure 0 (.plain (.frame 0 4 (.page .pageKind)))))

#guard (Snappy.convertV2 {} mixed).wire.map (fun _ => ()) =
  .error (.source (.groupFailure 1 (.framing .unsupportedOffsets)))
#guard (DictionaryV2.convert {} native).wire.map (fun _ => ()) =
  .error (.source (.groupFailure 1 (.frame 6 592 (.dataEncoding 0))))
#guard (DictionaryFallbackV2.convert {} native).wire.map (fun _ => ()) =
  .error (.source (.groupFailure 0 .missingPlainSuffix))

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2
