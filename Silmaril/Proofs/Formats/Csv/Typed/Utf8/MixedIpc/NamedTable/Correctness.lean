module

public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable.Defs
public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.Thms
import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.Thms
import Silmaril.Formats.Relational.NamedTable.Thms

public section

namespace Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable

open Silmaril.Relational Silmaril.Formats
open Silmaril.Formats.Csv.Typed.Utf8.MixedIpc
open Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc
open Silmaril.Formats.Relational.NamedTable (importCollected_ok_iff schemaMatches schemaMatches_eq_true_iff)

theorem importCsv_ok_iff {Name : Type*} [DecidableEq Name] {db next : Database Name}
    {name : Name} {expected declared : Rows.Schema} {limits : Limits} {input : Csv.Bytes} :
    importCsv db name expected declared limits input = .ok next ↔
      db name = none ∧ declared = expected ∧ ∃ rows : Scan.Table expected (fun _ => Cell),
        decode limits declared input = .ok ⟨expected, rows⟩ ∧
        next = Function.update db name (some ⟨expected, rows⟩) := by
  have gate : importCsv db name expected declared limits input = .ok next ↔
      db name = none ∧ ∃ rows : Scan.Table expected (fun _ => Cell),
        decode limits declared input = .ok ⟨expected, rows⟩ ∧
        next = Function.update db name (some ⟨expected, rows⟩) := by
    unfold importCsv
    rw [importCollected_ok_iff]
    cases decode limits declared input <;> simp [Except.map]
  rw [gate]
  constructor
  · rintro ⟨vacant, rows, decoded, update⟩
    exact ⟨vacant, (decode_schema decoded).symm, rows, decoded, update⟩
  · rintro ⟨vacant, _, rows, decoded, update⟩
    exact ⟨vacant, rows, decoded, update⟩

theorem exportCsv_ok_iff {Name : Type*} {db : Database Name} {name : Name}
    {expected : Rows.Schema} {limits : Limits} {output : Output} :
    exportCsv db name expected limits = .ok output ↔
      ∃ rows : Scan.Table expected (fun _ => Cell),
        Scan.observePacked db name = some ⟨expected, rows⟩ ∧
        output.schema = expected ∧ encode limits ⟨expected, rows⟩ = .ok output.wire := by
  cases found : Scan.observePacked db name with
  | none => simp [exportCsv, found]
  | some table =>
    cases table with
    | mk schema rows =>
      by_cases same : expected = schema
      · subst schema
        cases encoded : encode limits ⟨expected, rows⟩ with
        | error cause =>
          simp [exportCsv, found, encoded, Except.map, Except.mapError]
        | ok wire =>
          constructor
          · intro written
            have exact : (⟨expected, wire⟩ : Output) = output := by
              simpa [exportCsv, found, encoded, Except.map, Except.mapError] using written
            subst output
            exact ⟨rows, rfl, rfl, encoded⟩
          · rintro ⟨actual, equal, schemaEq, wireEq⟩
            have eqRows : rows = actual := by simpa using equal
            subst actual
            have equalWire := Except.ok.inj (encoded.symm.trans wireEq)
            cases output
            cases schemaEq
            cases equalWire
            simp [exportCsv, found, encoded, Except.map, Except.mapError]
      · have mismatch : schemaMatches expected schema = false := by
          cases matched : schemaMatches expected schema
          · rfl
          · exact (same ((schemaMatches_eq_true_iff _ _).mp matched)).elim
        constructor
        · simp [exportCsv, found, mismatch]
        · rintro ⟨actual, equal, _, _⟩
          have equalTable := Option.some.inj equal
          exact (same (congrArg Scan.Observation.schema equalTable).symm).elim

theorem ipc_roundtrip {Name : Type*} [DecidableEq Name] {db next : Database Name}
    {name : Name} {expected : Rows.Schema} {source sink : Arrow.MixedFlat.Limits}
    {sourceCsv importLimits exportLimits sinkCsv : Limits} {input output : KBytes} {csv exported : Output}
    (converted : convert source sourceCsv input = .ok csv)
    (inserted : importCsv db name expected csv.schema importLimits csv.wire = .ok next)
    (written : exportCsv next name expected exportLimits = .ok exported)
    (emitted : ToIpc.convert sinkCsv sink exported.schema exported.wire = .ok output) :
    ∃ table, Rows.readRows source input = some table ∧
      Scan.observePacked next name = some table ∧ csv.schema = table.schema ∧
      exported.schema = table.schema ∧ Rows.readRows sink output = some table ∧
      readEvents sink output = some
        ⟨ToIpc.fields table.schema, [Rows.observeColumns (AlignedColumns.ofRows table.rows)]⟩ := by
  obtain ⟨original, sourceRead, sourceSchema, sourceDecoded⟩ := convert_roundtrip converted
  obtain ⟨_, _, rows, namedDecoded, update⟩ := importCsv_ok_iff.mp inserted
  have sameOriginal := decode_agrees sourceDecoded namedDecoded
  subst original
  have atName : Scan.observePacked next name = some ⟨expected, rows⟩ := by
    rw [update]
    simp [Scan.observePacked, Database.Packed.erase, Database.Partial.map]
  obtain ⟨stored, observed, exportSchema, encoded⟩ := exportCsv_ok_iff.mp written
  have sameRows : rows = stored := by simpa [atName] using observed
  subst stored
  obtain ⟨recovered, sinkDecoded, _, sinkEvents, sinkRead⟩ := ToIpc.convert_readback emitted
  rw [exportSchema] at sinkDecoded sinkEvents
  have sameRecovered := decode_agrees (decode_encode encoded) sinkDecoded
  subst recovered
  exact ⟨⟨expected, rows⟩, sourceRead, atName, sourceSchema, exportSchema, sinkRead, sinkEvents⟩

end Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable
