module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Defs
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Defs
meta import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Defs

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy

private def native : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-required-container-v2-snappy/native-required-v2-snappy-crc.parquet"⟩

private def absent : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-required-container-v2-snappy/native-required-v2-snappy-no-crc.parquet"⟩

private def raw : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-required-container-v2/native-required-v2.parquet"⟩

private def first : List ListPage.Row :=
  [some [], some [none], some [some (-2147483648), none, some 2147483647], some [some 7, some 7]]

private def second : List ListPage.Row :=
  [some [none, none], some [],
    some (List.replicate 72 (some 7) ++ [none] ++ List.replicate 32 (some (-2147483648))),
    some [some 2147483647]]

private def observed (limits : Limits) (source : Bytes) : Option (Arrow.ListInt32.Field × List (List ListPage.Row)) := do
  let ipc ← (convert limits source).wire.toOption
  let value ← (Arrow.ListInt32.Stream.readFor false limits.ipc ipc).toOption
  pure (value.field, value.batches.map (·.rows))

private def outcome (limits : Limits) (source : Bytes) : Except Error Unit :=
  (convert limits source).wire.map (fun _ => ())

set_option synthInstance.maxSize 1024

#guard observed {} native = some (⟨"items", "element"⟩, [first, second])
#guard observed {} absent = some (⟨"items", "element"⟩, [first, second])
#guard observed { maxStoredPageBytes := 56, parquet.page.maxBodyBytes := 438 } native =
  some (⟨"items", "element"⟩, [first, second])
#guard outcome { maxStoredPageBytes := 55 } native =
  .error (.source (.groupFailure 1 (.frame 0 55 (.snappy (.checksum .byteLimit)))))
#guard outcome { parquet.page.maxBodyBytes := 437 } native =
  .error (.source (.groupFailure 1 (.frame 0 55 (.snappy (.payload .outputLimit)))))
#guard outcome { parquet.page.levels := ⟨109, 10⟩ } native =
  .error (.source (.groupFailure 1 (.frame 0 55 (.snappy .v2LevelLimit))))
#guard outcome { ipc.totalRows := 7 } native = .error (.writer .rowLimit)

#guard outcome {} raw = .error (.source (.groupFailure 0 (.framing (.codec 0))))
#guard (V2.convert {} native).wire.map (fun _ => ()) = .error (.source (.groupFailure 0 (.framing (.codec 1))))
#guard (RequiredContainer.convert {} native).wire.map (fun _ => ()) = .error (.source (.groupFailure 0 (.framing (.codec 1))))
#guard (ListFile.openFile {} native).map (fun _ => ()) = .error .shape

end Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy
