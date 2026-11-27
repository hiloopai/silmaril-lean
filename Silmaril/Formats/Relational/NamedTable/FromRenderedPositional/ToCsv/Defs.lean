module

public import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.Defs
public import Silmaril.Formats.Csv.NamedTable.Utf8.Defs
public import Silmaril.Formats.Csv.Typed.Codecs.Defs

/-! Atomic UTF-8 CSV export from a bounded rendered positional Parquet import. -/

@[expose] public section

namespace Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.ToCsv

open Silmaril.Relational Silmaril.Formats.Hive Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

inductive Error (Source : Type) where
  | input (reason : NamedTable.ImportError Source)
  | output (reason : Csv.NamedTable.ExportError)
  | byteLimit (maximum actual : Nat)

structure Result (Name : Type*) where
  db : Database Name
  schema : Csv.Typed.Schema Kind
  wire : Csv.Bytes

/-- Translate only the ordered labels to UTF-8. Positions and kinds remain
the same, including duplicate labels and width zero. -/
def csvSchema (schema : Scan.Schema String Kind) : Csv.Typed.Schema Kind :=
  ⟨schema.width, fun i => ((schema.kind i).1.toByteArray.data.toList, (schema.kind i).2)⟩

/-- The shared named CSV exporter observes this relabeled database view.
The returned database still carries the original String labels. -/
def csvView {Name : Type*} (db : Database Name) : NamedTable.Packed Name Csv.Field Value :=
  fun name => (db name).map fun ⟨schema, rows⟩ => ⟨csvSchema schema, rows⟩

/-- Escape arbitrary octets with the existing uppercase percent codec.
The typed CSV layer supplies the separate null/present tag. -/
def bytesCodec : Csv.Typed.CellCodec Bytes where
  print value := some (PartitionPath.Percent.escape value.toList)
  parse field := do
    let bytes ← (PartitionPath.Percent.unescape field).toOption
    if PartitionPath.Percent.escape bytes = field then some (Bytes.ofList bytes) else none

def codecs : (kind : Kind) → Csv.Typed.CellCodec (Value kind)
  | .int32 _ => Csv.Typed.Codecs.int32
  | .byteArray _ => bytesCodec

/-- Publish the imported database and CSV together after successful export
and an output byte count check. Input errors bypass export. -/
def exportImported {Name : Type*} {Source : Type} (name : Name) (maxCsvBytes : Nat)
    (imported : Except (NamedTable.ImportError Source) (Database Name)) :
    Except (Error Source) (Result Name) :=
  match imported with
  | .error reason => .error (.input reason)
  | .ok loaded =>
    match Csv.NamedTable.Utf8.exportCsv (csvView loaded) name codecs with
    | .error reason => .error (.output reason)
    | .ok (schema, wire) =>
      if wire.length > maxCsvBytes then .error (.byteLimit maxCsvBytes wire.length)
      else .ok ⟨loaded, schema, wire⟩

variable {Name : Type*} {Admission Failure : Type}
variable {int32 byteArray : Field} {partitions : PartitionSchema Kind}

/-- Run the bounded scan and exact-schema EOS import, then export the
installed name through the shared typed UTF-8 CSV exporter. -/
def convert [DecidableEq Name] (db : Database Name) (name : Name) (maxCsvBytes : Nat)
    (admission : Manifest.Inventory.Limits) (maxDirectoryBytes : Nat) (keys : List String)
    (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (codec : Convert Value Admission) (listing : List String) (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) :
    Except (Error (SourceError Admission Failure)) (Result Name) :=
  exportImported name maxCsvBytes
    (importScan db name admission maxDirectoryBytes keys encoding options codec listing
      limits lookup projection keep budget)

end Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.ToCsv
