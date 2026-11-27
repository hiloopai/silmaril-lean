module

public import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Defs
import Silmaril.Formats.Relational.NamedTable.Thms
import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.ToCsv.Thms

public section

namespace Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Hive Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Name : Type*}

open Silmaril.Formats.Relational
open NamedTable.FromRenderedPositional
open NamedTable.FromRenderedPositional.FromCsv

theorem readCsv_ok_iff (limits : Limits) (declared : Scan.Schema String Kind) (wire : Csv.Bytes)
    (rows : Scan.Table declared Value) :
    readCsv limits declared wire = .ok rows ↔
      wire.length ≤ limits.maxBytes ∧
      Csv.Typed.Utf8.decode (ToCsv.csvSchema declared) ToCsv.codecs wire = .ok rows ∧
      rows.length ≤ limits.maxRows := by
  by_cases large : wire.length > limits.maxBytes
  · simp [readCsv, large, Nat.not_le.mpr large]
  have fits := Nat.le_of_not_gt large
  cases decoded : Csv.Typed.Utf8.decode (ToCsv.csvSchema declared) ToCsv.codecs wire with
  | error reason => simp [readCsv, large, decoded]
  | ok actual =>
    constructor
    · intro read
      by_cases tooMany : actual.length > limits.maxRows
      · simp [readCsv, large, decoded, tooMany] at read
      · have same : (Except.ok actual : Except ReadError (Scan.Table declared Value)) = .ok rows := by
          simpa [readCsv, large, decoded, tooMany] using read
        cases same
        exact ⟨fits, rfl, Nat.le_of_not_gt tooMany⟩
    · rintro ⟨_, same, bounded⟩
      have equal := Except.ok.inj same
      subst rows
      simp only [readCsv, ite_eq_right large, decoded]
      split
      · rename_i tooMany
        exact (Nat.not_lt_of_ge bounded tooMany).elim
      · rfl

theorem importCsv_ok_iff [DecidableEq Name] (db next : Database Name) (name : Name)
    (expected declared : Scan.Schema String Kind) (limits : Limits) (wire : Csv.Bytes) :
    importCsv db name expected declared limits wire = .ok next ↔
      db name = none ∧ expected = declared ∧ ∃ rows : Scan.Table declared Value,
        readCsv limits declared wire = .ok rows ∧
        next = Function.update db name (some ⟨declared, rows⟩) := by
  cases existing : db name with
  | some entry => simp [importCsv, existing]
  | none =>
    simp only [importCsv, existing, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    rw [NamedTable.importCollected_ok_iff]
    by_cases same : expected = declared
    · subst expected
      cases readCsv limits declared wire <;> simp [Except.map, existing]
    · cases readCsv limits declared wire <;> simp [Except.map, same, Ne.symm same]

variable {SourceName : Type*} {Admission Failure : Type}
variable {int32 byteArray : Field} {partitions : PartitionSchema Kind}

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
        next = Function.update target dest (some ⟨projection.schema, trace.rows⟩) := by
  obtain ⟨trace, scanned, exhausted, schema, decoded, _, _⟩ :=
    ToCsv.convert_roundTrip source sourceName maxCsvBytes admission maxDirectoryBytes keys encoding options
      convertCell listing limits lookup projection keep budget converted
  refine ⟨trace, scanned, exhausted, schema, fun next => ?_⟩
  rw [importCsv_ok_iff]
  constructor
  · rintro ⟨vacant, _, rows, read, updated⟩
    obtain ⟨bytesFit, exactRows, rowsFit⟩ := (readCsv_ok_iff csvLimits _ _ _).mp read
    rw [decoded] at exactRows
    have equal := Except.ok.inj exactRows
    subst rows
    exact ⟨vacant, bytesFit, rowsFit, updated⟩
  · rintro ⟨vacant, bytesFit, rowsFit, updated⟩
    exact ⟨vacant, rfl, trace.rows, (readCsv_ok_iff csvLimits _ _ _).mpr ⟨bytesFit, decoded, rowsFit⟩, updated⟩

end Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv
