module

public import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Defs
import Silmaril.Formats.Relational.NamedTable.Thms
import Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv

public section

namespace Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Hive Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Name : Type*}

/-- Success means exact typed decoding and both inclusive caps. -/
theorem readCsv_ok_iff (limits : Limits) (declared : Scan.Schema String Kind) (wire : Csv.Bytes)
    (rows : Scan.Table declared Value) :
    readCsv limits declared wire = .ok rows ↔
      wire.length ≤ limits.maxBytes ∧
      Csv.Typed.Utf8.decode (ToCsv.csvSchema declared) ToCsv.codecs wire = .ok rows ∧
      rows.length ≤ limits.maxRows :=
  Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.readCsv_ok_iff limits declared wire rows

/-- On success the name was vacant, the declared schema agrees exactly,
and the only update stores the complete ordered table. -/
theorem importCsv_ok_iff [DecidableEq Name] (db next : Database Name) (name : Name)
    (expected declared : Scan.Schema String Kind) (limits : Limits) (wire : Csv.Bytes) :
    importCsv db name expected declared limits wire = .ok next ↔
      db name = none ∧ expected = declared ∧ ∃ rows : Scan.Table declared Value,
        readCsv limits declared wire = .ok rows ∧
        next = Function.update db name (some ⟨declared, rows⟩) :=
  Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.importCsv_ok_iff db next name expected declared limits wire

/-- At a vacant name the exact read failure is returned without a database. -/
theorem importCsv_read_error [DecidableEq Name] (db : Database Name) (name : Name)
    (expected declared : Scan.Schema String Kind) (limits : Limits) (wire : Csv.Bytes)
    (vacant : db name = none) {error : ReadError} (failed : readCsv limits declared wire = .error error) :
    importCsv db name expected declared limits wire = .error (.openError error) := by
  simp [importCsv, NamedTable.importCollected, vacant, failed, Except.map]

variable {SourceName : Type*} {Admission Failure : Type}
variable {int32 byteArray : Field} {partitions : PartitionSchema Kind}

/-- A successful forward conversion reconstructs the original projected
String/Kind table in a vacant target exactly when the reverse caps admit
it. The update preserves all other names. -/
theorem import_convert [DecidableEq SourceName] [DecidableEq Name]
    (source : Database SourceName) (sourceName : SourceName) (maxCsvBytes : Nat)
    (admission : Manifest.Inventory.Limits) (maxDirectoryBytes : Nat) (keys : List String)
    (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (convertCell : Convert Value Admission) (listing : List String) (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat)
    {result : ToCsv.Result SourceName}
    (converted : ToCsv.convert source sourceName maxCsvBytes admission maxDirectoryBytes keys encoding options
      convertCell listing limits lookup projection keep budget = .ok result)
    (target : Database Name) (dest : Name) (csvLimits : Limits) :
    ∃ trace,
      Manifest.RenderedPositional.scan admission maxDirectoryBytes keys encoding options convertCell listing
        limits lookup projection keep budget = .ok trace ∧ trace.termination = .eos ∧
      result.schema = ToCsv.csvSchema projection.schema ∧
      ∀ next, importCsv target dest projection.schema projection.schema csvLimits result.wire = .ok next ↔
        target dest = none ∧ result.wire.length ≤ csvLimits.maxBytes ∧ trace.rows.length ≤ csvLimits.maxRows ∧
        next = Function.update target dest (some ⟨projection.schema, trace.rows⟩) :=
  Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.import_convert
    source sourceName maxCsvBytes admission maxDirectoryBytes keys encoding options convertCell listing limits
    lookup projection keep budget converted target dest csvLimits

end Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv
