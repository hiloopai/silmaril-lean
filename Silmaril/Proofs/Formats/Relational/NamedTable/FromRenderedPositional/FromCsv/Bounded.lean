module

public import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Bounded.Defs
import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Thms
import Silmaril.Formats.Csv.Typed.Utf8.Bounded.Thms
import Silmaril.Formats.Relational.NamedTable.Thms

public section

namespace Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Bounded

open Silmaril.Relational Silmaril.Formats.Parquet
open Int32ByteArrayGroup.File (Kind Value)

variable {Name : Type*}

open Silmaril.Formats
open Silmaril.Formats.Relational
open NamedTable.FromRenderedPositional
open NamedTable.FromRenderedPositional.FromCsv

theorem readCsv_ok_iff (limits : Limits) (declared : Scan.Schema String Kind) (wire : Csv.Bytes)
    (rows : Scan.Table declared Value) :
    Bounded.readCsv limits declared wire = .ok rows ↔
      FromCsv.readCsv limits declared wire = .ok rows := by
  have shared := FromCsv.readCsv_ok_iff limits declared wire rows
  have budgeted := Csv.Typed.Utf8.Bounded.decode_ok_iff (ToCsv.csvSchema declared) ToCsv.codecs
    limits.maxRows wire rows
  refine Iff.trans ?_ ((and_congr Iff.rfl budgeted).trans shared.symm)
  unfold Bounded.readCsv
  split
  · rename_i large
    simp [Nat.not_le.mpr large]
  · rename_i small
    have fits := Nat.le_of_not_gt small
    cases Csv.Typed.Utf8.Bounded.decode limits.maxRows (ToCsv.csvSchema declared) ToCsv.codecs wire <;>
      simp [Except.mapError, fits]
    constructor <;> intro same <;> cases same <;> rfl

theorem importCsv_ok_iff [DecidableEq Name] (db next : Database Name) (name : Name)
    (expected declared : Scan.Schema String Kind) (limits : Limits) (wire : Csv.Bytes) :
    Bounded.importCsv db name expected declared limits wire = .ok next ↔
      db name = none ∧ expected = declared ∧ ∃ rows : Scan.Table declared Value,
        Bounded.readCsv limits declared wire = .ok rows ∧
        next = Function.update db name (some ⟨declared, rows⟩) := by
  cases existing : db name with
  | some entry => simp [Bounded.importCsv, existing]
  | none =>
    simp only [Bounded.importCsv, existing, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    rw [NamedTable.importCollected_ok_iff]
    by_cases same : expected = declared
    · subst expected
      cases Bounded.readCsv limits declared wire <;> simp [Except.map, existing]
    · cases Bounded.readCsv limits declared wire <;> simp [Except.map, same, Ne.symm same]

theorem importCsv_observe [DecidableEq Name] {db next : Database Name} {name : Name}
    {expected declared : Scan.Schema String Kind} {limits : Limits} {wire : Csv.Bytes}
    (loaded : Bounded.importCsv db name expected declared limits wire = .ok next) :
    ∃ rows : Scan.Table declared Value,
      Bounded.readCsv limits declared wire = .ok rows ∧
      Scan.observePacked next name = some ⟨declared, rows⟩ ∧
      ∀ other, other ≠ name → next other = db other := by
  obtain ⟨_, _, rows, read, rfl⟩ := (importCsv_ok_iff db next name expected declared limits wire).mp loaded
  refine ⟨rows, read, ?_, fun other different => Function.update_of_ne different _ _⟩
  simp [Scan.observePacked, Silmaril.Relational.Database.Packed.erase, Silmaril.Relational.Database.Partial.map]

end Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Bounded
