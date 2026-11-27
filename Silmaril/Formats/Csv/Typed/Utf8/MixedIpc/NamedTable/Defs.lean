module

public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.Defs
public import Silmaril.Formats.Relational.NamedTable.Defs

/-! Named tables at the bounded mixed IPC and typed UTF-8 CSV boundary. -/

@[expose] public section

namespace Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable

open Silmaril.Relational
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc
open Silmaril.Formats.Relational.NamedTable (Packed ImportError importCollected schemaMatches)

abbrev Database (Name : Type*) := Packed Name Arrow.MixedFlat.Field (fun _ : Unit => Cell)

inductive ExportError where
  | missingName
  | schemaMismatch
  | encodeError (cause : MixedIpc.Error)
  deriving DecidableEq, Repr

/-- The caller supplies the declared descriptor alongside the CSV and the
expected destination descriptor. A complete checked decode goes through
the existing vacant-name and exact-schema insertion gate. -/
def importCsv {Name : Type*} [DecidableEq Name] (db : Database Name)
    (name : Name) (expected declared : Rows.Schema) (limits : Limits) (input : Csv.Bytes) :
    Except (ImportError MixedIpc.Error) (Database Name) :=
  importCollected db name expected ((decode limits declared input).map fun table => ⟨table, .eos⟩)

/-- Observe the named table, check the exact ordered descriptor, and
return it alongside the bounded typed UTF-8 CSV. -/
def exportCsv {Name : Type*} (db : Database Name) (name : Name)
    (expected : Rows.Schema) (limits : Limits) : Except ExportError Output :=
  match Scan.observePacked db name with
  | none => .error .missingName
  | some table =>
    if schemaMatches expected table.schema then
      ((encode limits table).mapError .encodeError).map fun wire => ⟨table.schema, wire⟩
    else .error .schemaMismatch

end Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable
