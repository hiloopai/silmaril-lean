module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Defs

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy

private def native : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-list-snappy-v2/native-crc-v2.parquet"⟩

private def withoutCrc : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-list-snappy-v2/native-no-crc-v2.parquet"⟩

private def defaultFlag : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-list-snappy-v2/assembled-default-v2.parquet"⟩

private def first : List ListPage.Row :=
  [none, some [], some [some (-7), none], some [some (-2147483648), some 2147483647]]

private def second : List ListPage.Row :=
  [none, some [], some [none], some (List.replicate 32 (some 0) ++ [none] ++ List.replicate 7 (some 0))]

private def observed (source : Bytes) (limits : Limits := {}) :
    Option (Arrow.ListInt32.Field × List (List ListPage.Row)) := do
  let ipc ← (convertV2 limits source).wire.toOption
  let decoded ← (Arrow.ListInt32.Stream.read limits.ipc ipc).toOption
  pure (decoded.field, decoded.batches.map (·.rows))

private def outcome (source : Bytes) (limits : Limits := {}) : Except Error Unit :=
  (convertV2 limits source).wire.map (fun _ => ())

set_option synthInstance.maxSize 1024

#guard observed native = some (⟨"items", "element"⟩, [first, second])
#guard observed withoutCrc = some (⟨"items", "element"⟩, [first, second])
#guard observed defaultFlag = some (⟨"items", "element"⟩, [first, second])
#guard observed native { maxExpandedBytes := 206 } = some (⟨"items", "element"⟩, [first, second])
#guard outcome native { maxExpandedBytes := 205, ipc.totalRows := 0 } =
  .error (.source (.groupFailure 1 (.frame 3 255 (.expandedBudget 164 165))))
#guard outcome native { parquet.file.page.maxBodyBytes := 164 } =
  .error (.source (.groupFailure 1 (.frame 3 255 (.payload .outputLimit))))
#guard outcome native { parquet.file.page.levels := ⟨1024 * 1024, 4⟩ } =
  .error (.source (.groupFailure 1 (.frame 3 255 .v2LevelLimit)))
#guard outcome native { maxStoredPageBytes := 21 } =
  .error (.source (.groupFailure 1 (.frame 3 255 (.checksum .byteLimit))))
#guard outcome native { ipc.totalRows := 0 } = .error (.writer .rowLimit)

-- Version selection is explicit and the uncompressed framing API is independent.
#guard (convert {} native).wire.map (fun _ => ()) =
  .error (.source (.groupFailure 0 (.frame 0 4 (.page .pageKind))))
#guard outcome ⟨include_bytes "../../../../../../data/parquet-list-snappy-v1/native-crc-v1.parquet"⟩ =
  .error (.source (.groupFailure 0 (.frame 0 4 (.page .pageKind))))
#guard (ListFile.openFile {} native).toOption.map (·.readGroup 0) = some (.error (.codec 1))

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy
