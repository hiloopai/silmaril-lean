module

public import Silmaril.Formats.Hive.WritePlan.Restore.Defs
import Silmaril.Proofs.Formats.Hive.WritePlan.Restore

public section

namespace Silmaril.Formats.Hive.WritePlan

open Silmaril.Relational
open Silmaril.Formats.Hive.TypedPartitions (Convert PartitionSchema)

variable {Kind : Type*} {Value : Kind → Type*} {EncodeFailure DecodeFailure : Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

/-- Successful encoding emits the declared keys in their original order. -/
theorem encodeEntries_keys (encode : Encode Value EncodeFailure) (cells : Scan.Row schema.toScan Value)
    {entries : PartitionPath.Partition} (encoded : encodeEntries encode cells = .ok entries) :
    entries.map Prod.fst = schema.keys :=
  Proofs.Formats.Hive.WritePlan.encodeEntries_keys encode cells encoded

/-- Successful rendering provides the key admission needed to recover every
typed cell from the encoded entries, under the supplied codec inverse. -/
theorem decode_renderedEntries (options : PartitionPath.Options)
    (encode : Encode Value EncodeFailure) (decode : Convert Value DecodeFailure)
    (inverse : CellLeftInverse schema encode decode) (cells : Scan.Row schema.toScan Value)
    {entries : PartitionPath.Partition} {directory : String}
    (encoded : encodeEntries encode cells = .ok entries) (rendered : PartitionPath.render options entries = .ok directory) :
    TypedPartitions.decode schema decode entries = .ok cells :=
  Proofs.Formats.Hive.WritePlan.decode_renderedEntries options encode decode inverse cells encoded rendered

/-- Recover the full original rows in first-seen directory order and in
source-relative order within each directory. Both operations use the same
path options. Successful planning supplies directory representability,
and the left inverse recovers each successfully encoded present cell. -/
theorem restore_plan_eq_groupedRows (options : PartitionPath.Options)
    (encode : Encode Value EncodeFailure) (decode : Convert Value DecodeFailure)
    (inverse : CellLeftInverse schema encode decode)
    (rows : Scan.Table (schema.extend physical) Value) (buckets : List (Bucket physical Value))
    (planned : plan physical schema options encode rows = .ok buckets) :
    restore physical schema options decode buckets = .ok (groupOriginalRows options encode rows) :=
  Proofs.Formats.Hive.WritePlan.restore_plan_eq_groupedRows options encode decode inverse rows buckets planned

end Silmaril.Formats.Hive.WritePlan
