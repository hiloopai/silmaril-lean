module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Defs

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer

private def native : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-list-required-container/native-required.parquet"⟩

private def optional : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-list-required-container/native-optional.parquet"⟩

private def first : List ListPage.Row :=
  [some [], some [none], some [some (-2147483648), none, some 2147483647], some [some 7, some 7]]

private def second : List ListPage.Row :=
  [some [none, none], some [], some [some (-7), none, some 0], some [some 2147483647]]

private def expectedField : Arrow.ListInt32.Field := ⟨"items", "element"⟩

private def observed (source : Bytes) : Option (Arrow.ListInt32.Field × List (List ListPage.Row)) := do
  let ipc ← (convert {} source).wire.toOption
  let value ← (Arrow.ListInt32.Stream.readFor false {} ipc).toOption
  pure (value.field, value.batches.map (·.rows))

set_option synthInstance.maxSize 1024

#guard (openFile {} native).toOption.map (·.shape.outer.repetition) = some (some .required)
#guard (openFile {} native).toOption.map (·.shape.element.repetition) = some (some .optional)
#guard observed native = some (expectedField, [first, second])
#guard (convert {} optional).wire.map (fun _ => ()) = .error (.source (.openFailure .shape))
#guard (ListFile.openFile {} native).map (fun _ => ()) = .error .shape
#guard (ListFile.openFile {} optional).map (fun _ => ()) = .ok ()
#guard (convert { ipc.totalRows := 7 } native).wire.map (fun _ => ()) = .error (.writer .rowLimit)

#guard ((convert {} native).wire.toOption.map
  (fun wire => (Arrow.ListInt32.Stream.read {} wire).map (fun _ => ()))) =
  some (.error (.schemaMetadata (.unsupported .nested)))

#guard (Arrow.ListInt32.Stream.Writer.emitFor false {} expectedField [[none]]).map (fun _ => ()) =
  .error (.readback (.batch 0 .parentValidity))

end Silmaril.Formats.Parquet.ListFile.RequiredContainer
