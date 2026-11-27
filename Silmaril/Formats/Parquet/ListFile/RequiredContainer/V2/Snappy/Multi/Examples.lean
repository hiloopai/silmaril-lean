module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi.Defs

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi

private def native : Bytes :=
  ⟨include_bytes "../../../../../../../../data/parquet-list-required-container-v2-snappy-multi/native-required-v2-snappy-multi-crc.parquet"⟩

private def noCrc : Bytes :=
  ⟨include_bytes "../../../../../../../../data/parquet-list-required-container-v2-snappy-multi/native-required-v2-snappy-multi-no-crc.parquet"⟩

private def uncompressed : Bytes :=
  ⟨include_bytes "../../../../../../../../data/parquet-list-required-container-v2-multi/native-required-v2-multi.parquet"⟩

private def first : List ListPage.Row :=
  [some [], some [none], some [some (-2147483648), none, some 2147483647], some [some 7, some 7]]

private def second : List ListPage.Row :=
  [some [none, none], some [], some [some 2147483647],
    some (List.replicate 72 (some 7) ++ [none] ++ List.replicate 32 (some (-2147483648)))]

private def observed (limits : Limits) (source : Bytes) : Option (Arrow.ListInt32.Field × List (List ListPage.Row)) := do
  let ipc ← (convert limits source).wire.toOption
  let value ← (Arrow.ListInt32.Stream.readFor false limits.ipc ipc).toOption
  pure (value.field, value.batches.map (·.rows))

private def outcome (limits : Limits) (source : Bytes) : Except (RequiredContainer.Error GroupError) Unit :=
  (convert limits source).wire.map (fun _ => ())

set_option synthInstance.maxSize 1024

#guard observed {} native = some (⟨"items", "element"⟩, [first, second])
#guard observed {} noCrc = observed {} native
#guard observed { maxGroupSlots := 109, maxStoredPageBytes := 46, parquet.page.maxBodyBytes := 429 } native =
  some (⟨"items", "element"⟩, [first, second])
#guard outcome { maxGroupSlots := 108 } native = .error (.source (.groupFailure 1 .slotLimit))
#guard outcome { maxStoredPageBytes := 45 } native =
  .error (.source (.groupFailure 1 (.frame 2 196 (.checksum .byteLimit))))
#guard outcome { parquet.page.maxBodyBytes := 428 } native =
  .error (.source (.groupFailure 1 (.frame 2 196 (.payload .outputLimit))))
#guard outcome { ipc.totalRows := 7 } native = .error (.writer .rowLimit)
#guard outcome {} uncompressed = .error (.source (.groupFailure 0 (.framing (.codec 0))))
#guard (Snappy.convert {} native).wire.map (fun _ => ()) = .error (.source (.groupFailure 0 (.framing .pageCount)))
#guard (V2.Multi.convert {} native).wire.map (fun _ => ()) = .error (.source (.groupFailure 0 (.framing (.codec 1))))

end Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi
