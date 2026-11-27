module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.Writer.FromIpc.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.Writer.FromIpc.Defs
meta import Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Defs

namespace Silmaril.Formats.Parquet.ListFile.Writer.FromIpc

private def bytes (raw : ByteArray) : KBytes := .leaf raw.size (KBytes.leVal raw.data.toList)

private def native : KBytes :=
  bytes (include_bytes "../../../../../../data/arrow-list-int32-stream/nullable-list-int32.arrows")

private def schemaOnly : KBytes :=
  bytes (include_bytes "../../../../../../data/arrow-list-parquet-roundtrip/schema-only.arrows")

private def emptyBatch : KBytes :=
  bytes (include_bytes "../../../../../../data/arrow-list-parquet-roundtrip/empty-batch.arrows")

private def wrongChild : KBytes :=
  bytes (include_bytes "../../../../../../data/arrow-list-parquet-roundtrip/noncanonical-child.arrows")

private def returned (source : KBytes) :
    Option (Arrow.ListInt32.Field × List (List ListPage.Row) × List Nat) := do
  let parquet ← (convert {} source).toOption
  let output ← (Multi.ToIpc.convert {} parquet.bytes).wire.toOption
  let decoded ← (Arrow.ListInt32.Stream.read {} output).toOption
  pure (decoded.field, decoded.batches.map (·.rows), decoded.batches.map (·.childCount))

set_option synthInstance.maxSize 1024

-- The source's hidden physical child 99 is not an observed value.
#guard returned native = some (⟨"items", "element"⟩,
  [[none, some [], some [some (-7), none, some 0], some [none]], [],
    [some [], some [some (-2147483648), some 2147483647]]], [4, 0, 2])

#guard returned schemaOnly = some (⟨"résultats", "element"⟩, [], [])
#guard returned emptyBatch = some (⟨"résultats", "element"⟩, [[]], [0])
#guard (convert {} schemaOnly).toOption.map (·.footer.start) = some 4
#guard (convert {} emptyBatch).toOption.map (fun f => f.groups.map (·.page.body.length)) = some [8]

#guard (convert {} wrongChild).map (fun _ => ()) = .error (.childName "item")
#guard (convert { parquet.maxGroups := 0 } native).map (fun _ => ()) = .error (.writer .groupLimit)
#guard (convert { parquet.maxGroups := 0 } (native.slice 0 (native.len - 9))).map (fun _ => ()) =
  .error (.source (.batch 2 (.body (.malformed .truncated))))
#guard (convert { parquet.maxGroups := 0 } (wrongChild.slice 0 (wrongChild.len - 9))).map (fun _ => ()) =
  .error (.source (.batch 1 (.body (.malformed .truncated))))
#guard (convert {} (native.slice 0 (native.len - 8))).map (fun _ => ()) =
  .error (.source (.batch 3 (.envelope (.malformed .truncated))))

end Silmaril.Formats.Parquet.ListFile.Writer.FromIpc
