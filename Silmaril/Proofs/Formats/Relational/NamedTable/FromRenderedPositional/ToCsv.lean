module

public import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.ToCsv.Defs
import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.Thms
import Silmaril.Formats.Csv.NamedTable.Utf8.Thms
import Silmaril.Formats.Csv.Typed.Codecs.Thms
import Silmaril.Formats.Hive.PartitionPath.Thms

public section

namespace Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.ToCsv

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Hive Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Name : Type*} {Admission Failure : Type}
variable {int32 byteArray : Field} {partitions : PartitionSchema Kind}

open Silmaril.Formats.Relational
open NamedTable.FromRenderedPositional
open NamedTable.FromRenderedPositional.ToCsv

theorem codecs_parsePrint (kind : Kind) : (codecs kind).ParsePrint := by
  cases kind with
  | int32 _ => exact Csv.Typed.Codecs.int32_parsePrint
  | byteArray _ =>
    intro value field printed
    have equal : PartitionPath.Percent.escape value.toList = field := Option.some.inj printed
    subst field
    simp [codecs, bytesCodec, PartitionPath.Percent.unescape_escape, Except.toOption, Option.bind]

private theorem exportImported_values {Source : Type} (name : Name) (maxCsvBytes : Nat)
    (imported : Except (NamedTable.ImportError Source) (Database Name)) {result : Result Name}
    (accepted : exportImported name maxCsvBytes imported = .ok result) :
    ∃ loaded schema wire,
      imported = .ok loaded ∧ Csv.NamedTable.Utf8.exportCsv (csvView loaded) name codecs = .ok (schema, wire) ∧
      wire.length ≤ maxCsvBytes ∧ result = ⟨loaded, schema, wire⟩ := by
  cases imported with
  | error reason => cases accepted
  | ok loaded =>
    cases written : Csv.NamedTable.Utf8.exportCsv (csvView loaded) name codecs with
    | error reason => simp [exportImported, written] at accepted
    | ok output =>
      obtain ⟨schema, wire⟩ := output
      by_cases oversized : wire.length > maxCsvBytes
      · simp [exportImported, written, oversized] at accepted
      · simp [exportImported, written, oversized] at accepted
        exact ⟨loaded, schema, wire, rfl, written, Nat.le_of_not_gt oversized, accepted.symm⟩

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
      result.wire.length ≤ maxCsvBytes := by
  obtain ⟨loaded, schema, wire, imported, exported, bounded, rfl⟩ :=
    exportImported_values name maxCsvBytes _ converted
  obtain ⟨_, trace, scanned, exhausted, rfl⟩ :=
    (importScan_ok_iff db loaded name admission maxDirectoryBytes keys encoding options codec listing
      limits lookup projection keep budget).mp imported
  have found : Scan.observePacked (csvView (Function.update db name (some ⟨projection.schema, trace.rows⟩))) name =
      some ⟨csvSchema projection.schema, trace.rows⟩ := by
    simp [csvView, Scan.observePacked, Silmaril.Relational.Database.Packed.erase,
      Silmaril.Relational.Database.Partial.map]
  obtain ⟨exactSchema, decoded⟩ := Csv.NamedTable.Utf8.decode_exportCsv _ _ found codecs_parsePrint exported
  exact ⟨trace, scanned, exhausted, exactSchema, decoded, rfl, bounded⟩

end Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.ToCsv
