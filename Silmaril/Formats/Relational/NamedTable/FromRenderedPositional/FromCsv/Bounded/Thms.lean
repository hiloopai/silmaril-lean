module

public import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Bounded.Defs
import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Thms
import Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Bounded

public section

namespace Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Bounded

open Silmaril.Relational Silmaril.Formats.Parquet
open Int32ByteArrayGroup.File (Kind Value)

variable {Name : Type*}

/-- Both readers succeed on precisely the same rows under the inclusive caps. -/
theorem readCsv_ok_iff (limits : Limits) (declared : Scan.Schema String Kind) (wire : Csv.Bytes)
    (rows : Scan.Table declared Value) :
    Bounded.readCsv limits declared wire = .ok rows ↔
      FromCsv.readCsv limits declared wire = .ok rows :=
  Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Bounded.readCsv_ok_iff limits declared wire rows

/-- Exact-schema success stores only the complete table at the vacant name. -/
theorem importCsv_ok_iff [DecidableEq Name] (db next : Database Name) (name : Name)
    (expected declared : Scan.Schema String Kind) (limits : Limits) (wire : Csv.Bytes) :
    Bounded.importCsv db name expected declared limits wire = .ok next ↔
      db name = none ∧ expected = declared ∧ ∃ rows : Scan.Table declared Value,
        Bounded.readCsv limits declared wire = .ok rows ∧
        next = Function.update db name (some ⟨declared, rows⟩) :=
  Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Bounded.importCsv_ok_iff db next name expected declared limits wire

/-- The two named entry points agree on every successful import result. -/
theorem importCsv_agrees_on_success [DecidableEq Name] (db next : Database Name) (name : Name)
    (expected declared : Scan.Schema String Kind) (limits : Limits) (wire : Csv.Bytes) :
    Bounded.importCsv db name expected declared limits wire = .ok next ↔
      FromCsv.importCsv db name expected declared limits wire = .ok next := by
  simp only [importCsv_ok_iff, FromCsv.importCsv_ok_iff, readCsv_ok_iff]

/-- Observe the exact ordered table, including zero-column rows, and every
original entry at a different name. -/
theorem importCsv_observe [DecidableEq Name] {db next : Database Name} {name : Name}
    {expected declared : Scan.Schema String Kind} {limits : Limits} {wire : Csv.Bytes}
    (loaded : Bounded.importCsv db name expected declared limits wire = .ok next) :
    ∃ rows : Scan.Table declared Value,
      Bounded.readCsv limits declared wire = .ok rows ∧
      Scan.observePacked next name = some ⟨declared, rows⟩ ∧
      ∀ other, other ≠ name → next other = db other :=
  Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Bounded.importCsv_observe loaded

end Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Bounded
