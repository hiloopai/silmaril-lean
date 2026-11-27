module

public import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.ToCsv.Defs
import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.Thms
import Silmaril.Formats.Csv.Typed.Utf8.Thms
import Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.ToCsv

public section

namespace Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.ToCsv

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Hive Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Name : Type*} {Admission Failure : Type}
variable {int32 byteArray : Field} {partitions : PartitionSchema Kind}

/-- The original label is recoverable from its UTF-8 CSV spelling. -/
theorem csvSchema_label (schema : Scan.Schema String Kind) (i : Fin schema.width) :
    Csv.Typed.Utf8.string.parse ((csvSchema schema).kind i).1 = some (schema.kind i).1 :=
  Csv.Typed.Utf8.string_parsePrint rfl

/-- The decimal and opaque-byte codecs both recover the exact printed value. -/
theorem codecs_parsePrint (kind : Kind) : (codecs kind).ParsePrint :=
  Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.ToCsv.codecs_parsePrint kind

/-- Every input error, including admission failure and budget cutoff, is
returned before encoding with no CSV carrier or updated database. -/
theorem exportImported_input_error {Source : Type} (name : Name) (maxCsvBytes : Nat)
    (reason : NamedTable.ImportError Source) :
    exportImported name maxCsvBytes (.error reason) = .error (.input reason) := rfl

/-- Successful conversion observes exact EOS, returns the bounded CSV
and the single-name update, and decodes to all original projected rows
in order. The typed zero-column marker preserves cardinality. -/
theorem convert_roundTrip [DecidableEq Name] (db : Database Name) (name : Name) (maxCsvBytes : Nat)
    (admission : Manifest.Inventory.Limits) (maxDirectoryBytes : Nat) (keys : List String)
    (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (codec : Convert Value Admission) (listing : List String) (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat)
    {result : Result Name}
    (converted : convert db name maxCsvBytes admission maxDirectoryBytes keys encoding options codec listing
      limits lookup projection keep budget = .ok result) :
    ∃ trace,
      Manifest.RenderedPositional.scan admission maxDirectoryBytes keys encoding options codec listing
        limits lookup projection keep budget = .ok trace ∧ trace.termination = .eos ∧
      result.schema = csvSchema projection.schema ∧
      Csv.Typed.Utf8.decode (csvSchema projection.schema) codecs result.wire = .ok trace.rows ∧
      result.db = Function.update db name (some ⟨projection.schema, trace.rows⟩) ∧
      result.wire.length ≤ maxCsvBytes :=
  Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.ToCsv.convert_roundTrip
    db name maxCsvBytes admission maxDirectoryBytes keys encoding options codec listing
    limits lookup projection keep budget converted

/-- The same atomic result is obtained from direct original-entry binding
and the stable, pruned render-reference scan. -/
theorem convert_eq_reference [DecidableEq Name] (db : Database Name) (name : Name) (maxCsvBytes : Nat)
    (admission : Manifest.Inventory.Limits) (renderLimits : PartitionPath.Positional.RenderLimits)
    (keys : List String) (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (codec : Convert Value Admission) (listing : List String) (original : String → PartitionPath.Partition)
    (witness : Manifest.RenderedPositional.MatchesRender admission renderLimits keys encoding options original listing)
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) :
    convert db name maxCsvBytes admission renderLimits.maxDirectoryBytes keys encoding options codec listing
      limits lookup projection keep budget =
      exportImported name maxCsvBytes
        (importResult db name
          ((Manifest.prepareInventoryReferenceWith (Int32ByteArrayGroup.File.schema int32 byteArray) partitions
            admission (Manifest.RenderedPositional.fromOriginal renderLimits.maxDirectoryBytes original)
            options codec listing).map (fun files =>
              Manifest.scanInt32ByteArraySnapshotsBounded limits lookup projection keep budget
                ((Manifest.Inventory.orderFiles files).filter fun file => (keep file.cells).getD false)))) := by
  unfold convert
  rw [importScan_eq_reference db name admission renderLimits keys encoding options codec listing
    original witness limits lookup projection keep budget]

end Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.ToCsv
