module

public import Silmaril.Formats.Hive.Date32.Utf8.Render.Defs
import Silmaril.Proofs.Formats.Hive.Date32.Utf8.Render

public section

namespace Silmaril.Formats.Hive.Date32.Utf8

open Silmaril.Relational
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.File (Value)

theorem encode_convert_leftInverse (keys : Keys) :
    WritePlan.CellLeftInverse keys.schema encode convert :=
  Proofs.Formats.Hive.Date32.Utf8.Render.encode_convert_leftInverse keys

/-- The rendered directory parses to the original ordered entries. -/
theorem renderDirectory_parse {keys : Keys} (options : PartitionPath.Options)
    (cells : Scan.Row keys.schema.toScan Value) {directory : String}
    (written : renderDirectory options cells = .ok directory) :
    ∃ entries, WritePlan.encodeEntries encode cells = .ok entries ∧
      PartitionPath.parse options directory = .ok entries ∧ entries.map Prod.fst = keys.schema.keys :=
  Proofs.Formats.Hive.Date32.Utf8.Render.renderDirectory_parse options cells written

/-- A checked declaration under the rendered directory retains its literal
path and binds the exact typed cells using the same URI options. -/
theorem prepareFile_renderDirectory {keys : Keys} (options : PartitionPath.Options)
    (cells : Scan.Row keys.schema.toScan Value) {directory path leaf : String}
    (written : renderDirectory options cells = .ok directory)
    (split : Manifest.splitFile path = .ok (directory, leaf)) :
    Manifest.prepareFile keys.schema options convert path = .ok ⟨⟨path, directory, leaf⟩, cells⟩ :=
  Proofs.Formats.Hive.Date32.Utf8.Render.prepareFile_renderDirectory options cells written split

/-- After encoding and key admission, refuse the first present value whose
decoded spelling equals the configured marker. -/
theorem renderDirectory_first_markerCollision {keys : Keys} (options : PartitionPath.Options)
    (cells : Scan.Row keys.schema.toScan Value) {entries : PartitionPath.Partition} {entry : PartitionPath.Entry}
    (encoded : WritePlan.encodeEntries encode cells = .ok entries)
    (marker : options.nullMarker.isEmpty = false)
    (valid : PartitionPath.validate options entries = .ok ())
    (found : entries.find? (fun part => part.2 == some options.nullMarker) = some entry) :
    renderDirectory options cells = .error (.render (.nullMarkerCollision entry.1)) :=
  Proofs.Formats.Hive.Date32.Utf8.Render.renderDirectory_first_markerCollision options cells encoded marker valid found

end Silmaril.Formats.Hive.Date32.Utf8
