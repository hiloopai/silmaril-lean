module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Defs

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2

private def native : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-list-required-container-v2/native-required-v2.parquet"⟩

private def v1 : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-list-required-container/native-required.parquet"⟩

private def first : List ListPage.Row :=
  [some [], some [none], some [some (-2147483648), none, some 2147483647], some [some 7, some 7]]

private def second : List ListPage.Row :=
  [some [none, none], some [], some [some (-7), none, some 0], some [some 2147483647]]

private def observed (limits : Limits) (source : Bytes) : Option (Arrow.ListInt32.Field × List (List ListPage.Row)) := do
  let ipc ← (convert limits source).wire.toOption
  let value ← (Arrow.ListInt32.Stream.readFor false limits.ipc ipc).toOption
  pure (value.field, value.batches.map (·.rows))

private def outcome (limits : Limits) (source : Bytes) : Except Error Unit :=
  (convert limits source).wire.map (fun _ => ())

set_option synthInstance.maxSize 1024

#guard observed {} native = some (⟨"items", "element"⟩, [first, second])
#guard observed { parquet.page.maxBodyBytes := 21 } native = some (⟨"items", "element"⟩, [first, second])
#guard outcome { parquet.page.maxBodyBytes := 20 } native = .error (.source (.groupFailure 0 (.frame 0 4 .bodyLimit)))
#guard outcome { parquet.page.levels := ⟨16, 2⟩ } native = .error (.source (.groupFailure 0 (.frame 0 4 .levelLimit)))
#guard outcome { ipc.totalRows := 7 } native = .error (.writer .rowLimit)
#guard outcome {} v1 = .error (.source (.groupFailure 0 (.frame 0 4 (.page .pageKind))))
#guard (RequiredContainer.convert {} native).wire.map (fun _ => ()) =
  .error (.source (.groupFailure 0 (.frame 0 4 (.page .pageKind))))
#guard (ListFile.openFile {} native).map (fun _ => ()) = .error .shape

end Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2
