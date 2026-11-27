module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.Defs

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi

private def native : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-required-container-v2-multi/native-required-v2-multi.parquet"⟩

private def singleton : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-list-required-container-v2/native-required-v2.parquet"⟩

private def first : List ListPage.Row :=
  [some [], some [none], some [some (-2147483648), none, some 2147483647], some [some 7, some 7]]

private def second : List ListPage.Row :=
  [some [none, none], some [], some [some (-7), none, some 0], some [some 2147483647]]

private def observed (limits : Limits) (source : Bytes) : Option (Arrow.ListInt32.Field × List (List ListPage.Row)) := do
  let ipc ← (convert limits source).wire.toOption
  let value ← (Arrow.ListInt32.Stream.readFor false limits.ipc ipc).toOption
  pure (value.field, value.batches.map (·.rows))

private def outcome (limits : Limits) (source : Bytes) : Except (RequiredContainer.Error GroupError) Unit :=
  (convert limits source).wire.map (fun _ => ())

set_option synthInstance.maxSize 1024

#guard observed {} native = some (⟨"items", "element"⟩, [first, second])
#guard observed { maxGroupSlots := 7, parquet.page.maxRows := 4, parquet.page.maxBodyBytes := 13 } native =
  some (⟨"items", "element"⟩, [first, second])
#guard outcome { maxGroupSlots := 6 } native = .error (.source (.groupFailure 0 .slotLimit))
#guard outcome { parquet.page.maxRows := 3 } native = .error (.source (.groupFailure 0 .rowLimit))
#guard outcome { parquet.page.maxBodyBytes := 12 } native =
  .error (.source (.groupFailure 0 (.frame 1 33 (.data .bodyLimit))))
#guard outcome { ipc.totalRows := 7 } native = .error (.writer .rowLimit)
#guard observed {} singleton = some (⟨"items", "element"⟩, [first, second])
#guard (V2.convert {} native).wire.map (fun _ => ()) = .error (.source (.groupFailure 0 (.framing .pageCount)))

end Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi
