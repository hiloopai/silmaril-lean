module

public import Silmaril.Formats.Csv.Typed.Utf8.Bounded.Defs

public section

namespace Silmaril.Proofs.Formats.Csv.Typed.Utf8.Bounded

open Silmaril.Formats Silmaril.Formats.Csv
open Silmaril.Formats.Csv.Internal (readField readRecords comma cr lf)
open Silmaril.Formats.Csv.Typed
open Silmaril.Formats.Csv.Typed.Internal (importRow)
open Silmaril.Formats.Csv.Typed.Utf8.Bounded.Internal (readRawRow readRow readBody)

private def finishRecords (row : Row) : Bytes → Option (Row × Rows)
  | [] => some (row, [])
  | b :: bs => (readRecords (b :: bs) .utf8Bytes).map fun (first, rest) => (row, first :: rest)

private theorem readRecords_step (wire : Bytes) :
    readRecords wire .utf8Bytes =
      (readRawRow wire).bind fun (row, rest) => finishRecords row rest := by
  induction len : wire.length using Nat.strongRecOn generalizing wire with
  | ind n ih =>
    rw [readRecords.eq_def wire .utf8Bytes, readRawRow.eq_def wire]
    cases field : readField wire .utf8Bytes with
    | none => rfl
    | some parsed =>
      rcases parsed with ⟨value, rest, bound⟩
      cases rest with
      | nil => rfl
      | cons b bs =>
        change (b :: bs).length ≤ wire.length at bound
        by_cases separator : b = comma
        · have less : bs.length < n := by simp at bound; omega
          have recurse := ih bs.length less bs rfl
          simp only [bind, Option.bind, separator, ↓reduceIte]
          rw [recurse]
          cases raw : readRawRow bs with
          | none => rfl
          | some pair =>
            obtain ⟨row, suffix⟩ := pair
            cases suffix with
            | nil => rfl
            | cons c cs =>
              simp only [Option.bind, finishRecords]
              cases readRecords (c :: cs) .utf8Bytes <;> rfl
        · by_cases line : b = cr
          · subst b
            cases bs with
            | nil => simp [bind, Option.bind, separator]
            | cons c rest =>
              by_cases lfEnd : c = lf
              · subst c
                cases rest with
                | nil => simp [bind, Option.bind, separator, finishRecords]
                | cons d ds =>
                  simp [bind, Option.bind, separator, finishRecords]
                  cases readRecords (d :: ds) .utf8Bytes <;> rfl
              · simp [bind, Option.bind, separator, lfEnd]
          · simp [bind, Option.bind, separator, line]

private theorem scan_step (b : UInt8) (bs : Bytes) :
    Csv.Utf8.Internal.scan (b :: bs) =
      (readRawRow (b :: bs)).bind fun (row, rest) =>
        (Csv.Utf8.Internal.scan rest).map (row :: ·) := by
  simp only [Csv.Utf8.Internal.scan, readRecords_step (b :: bs)]
  cases readRawRow (b :: bs) with
  | none => rfl
  | some pair =>
    obtain ⟨row, rest⟩ := pair
    cases rest with
    | nil => rfl
    | cons c cs =>
      simp only [Option.bind, finishRecords]
      cases readRecords (c :: cs) .utf8Bytes <;> rfl

private theorem lexical_step (b : UInt8) (bs : Bytes) :
    Csv.Utf8.decode (b :: bs) =
      (readRow (b :: bs)).bind fun (row, rest) =>
        (Csv.Utf8.decode rest).map (row :: ·) := by
  simp only [Csv.Utf8.decode, scan_step, readRow]
  cases raw : readRawRow (b :: bs) with
  | none => rfl
  | some pair =>
    obtain ⟨row, rest⟩ := pair
    have prepend (later : Rows) : Csv.Utf8.rowsOK (row :: later) =
        (Csv.Utf8.rowsOK [row] && Csv.Utf8.rowsOK later) := by simp [Csv.Utf8.rowsOK]
    cases tail : Csv.Utf8.Internal.scan rest <;>
      by_cases valid : Csv.Utf8.rowsOK [row] = true <;>
      simp [bind, Option.bind, tail, valid, prepend]

variable {Kind : Type*} {Value : Kind → Type*}
variable (schema : Schema Kind) (codecs : (kind : Kind) → CellCodec (Value kind))

private def bodySpec (wire : Bytes) : Option (Table schema Value) :=
  (Csv.Utf8.decode wire).bind fun rows => (rows.mapM (importRow schema codecs)).toOption

private theorem bodySpec_step (b : UInt8) (bs : Bytes) :
    bodySpec schema codecs (b :: bs) =
      (readRow (b :: bs)).bind fun (raw, rest) =>
        (importRow schema codecs raw).toOption.bind fun row =>
          (bodySpec schema codecs rest).map (row :: ·) := by
  simp only [bodySpec, lexical_step b bs]
  cases readRow (b :: bs) with
  | none => rfl
  | some pair =>
    obtain ⟨raw, rest⟩ := pair
    simp only [Option.bind]
    cases decoded : Csv.Utf8.decode rest with
    | none =>
      cases step : importRow schema codecs raw <;>
        simp [Option.map, Except.toOption]
    | some rows =>
      cases step : importRow schema codecs raw with
      | error reason =>
        simp [step, Option.map, List.mapM_cons, bind, Except.bind, Except.toOption]
      | ok value =>
        cases later : rows.mapM (importRow schema codecs) <;>
          simp [step, later, Option.map, List.mapM_cons, bind, Except.bind,
            Except.toOption, pure, Except.pure]

private theorem toOption_map {α β ε : Type*} (f : α → β) (value : Except ε α) :
    (value.map f).toOption = value.toOption.map f := by
  cases value <;> rfl

private theorem body_agrees (remaining : Nat) (wire : Bytes) :
    (readBody schema codecs remaining wire).toOption =
      (bodySpec schema codecs wire).filter (fun rows => decide (rows.length ≤ remaining)) := by
  induction remaining generalizing wire with
  | zero =>
    cases wire with
    | nil => rfl
    | cons b bs =>
      rw [bodySpec_step]
      cases readRow (b :: bs) with
      | none => rfl
      | some pair =>
        obtain ⟨raw, rest⟩ := pair
        cases parsed : importRow schema codecs raw <;>
          cases tail : bodySpec schema codecs rest <;>
          simp [readBody, parsed, tail, Except.toOption, Option.bind, Option.map, Option.filter]
  | succ remaining ih =>
    cases wire with
    | nil => rfl
    | cons b bs =>
      rw [bodySpec_step]
      cases raw : readRow (b :: bs) with
      | none => simp [readBody, raw, Except.toOption]
      | some pair =>
        obtain ⟨fields, rest⟩ := pair
        cases row : importRow schema codecs fields with
        | error reason => simp [readBody, raw, row, Except.toOption]
        | ok value =>
          simp only [readBody, raw, row]
          rw [toOption_map, ih]
          simp only [row, Except.toOption, Option.bind]
          cases bodySpec schema codecs rest with
          | none => rfl
          | some rows =>
            by_cases fits : rows.length ≤ remaining <;> simp [Option.filter, Option.map, fits]

theorem decode_ok_iff (maxRows : Nat) (wire : Bytes) (rows : Table schema Value) :
    Typed.Utf8.Bounded.decode maxRows schema codecs wire = .ok rows ↔
      Typed.Utf8.decode schema codecs wire = .ok rows ∧ rows.length ≤ maxRows := by
  have agrees : (Typed.Utf8.Bounded.decode maxRows schema codecs wire).toOption =
      (Typed.Utf8.decode schema codecs wire).toOption.filter (fun rows => decide (rows.length ≤ maxRows)) := by
    cases wire with
    | nil => rfl
    | cons b bs =>
      simp only [Typed.Utf8.Bounded.decode, Typed.Utf8.decode, lexical_step b bs]
      cases parsed : readRow (b :: bs) with
      | none => rfl
      | some pair =>
        obtain ⟨raw, rest⟩ := pair
        by_cases exactHeader : raw = header schema
        · simp only [exactHeader, ↓reduceIte, body_agrees, Option.bind]
          cases later : Csv.Utf8.decode rest <;>
            simp [later, bodySpec, Typed.importRows, Option.map, Except.toOption]
        · cases later : Csv.Utf8.decode rest <;>
            simp [later, exactHeader, Typed.importRows, Except.toOption, Option.map, Option.bind]
  cases bounded : Typed.Utf8.Bounded.decode maxRows schema codecs wire <;>
    cases complete : Typed.Utf8.decode schema codecs wire
  all_goals simp [bounded, complete, Except.toOption, Option.filter] at agrees ⊢
  · intro equal
    subst rows
    exact agrees
  · obtain ⟨fits, rfl⟩ := agrees
    exact ⟨fun same => ⟨same, same ▸ fits⟩, And.left⟩

end Silmaril.Proofs.Formats.Csv.Typed.Utf8.Bounded
