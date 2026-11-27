module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Writer

open Silmaril.Formats.Arrow.RecursiveSchema (Schema)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch (Frame Limits readFrame)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Cell Observation Value decode decode_wire)

private theorem list_exact {α : Type} {equal : α → α → Bool}
    (compare : ∀ {left right}, equal left right = true → left = right)
    {left right : List α} (same : left.isEqv right equal = true) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons a as ih =>
    cases right with
    | nil => simp at same
    | cons b bs =>
      obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp same
      exact congrArg₂ List.cons (compare head) (ih tail)

private theorem cell_exact {depth : Nat} {left right : Cell}
    (same : equalCell depth left right = true) : left = right := by
  induction depth generalizing left right with
  | zero => cases left <;> cases right <;> simp_all [equalCell]
  | succ depth ih =>
    cases left with
    | none => cases right <;> simp_all [equalCell]
    | some a =>
      cases right with
      | none => simp [equalCell] at same
      | some b =>
        cases a <;> cases b <;> simp_all only [equalCell, beq_iff_eq, Bool.false_eq_true,
          Option.some.injEq]
        · exact congrArg Value.struct (list_exact ih same)
        · exact congrArg Value.list (list_exact ih same)

theorem agrees_exact {depth : Nat} {input output : Observation}
    (same : agrees depth input output = true) : input = output := by
  obtain ⟨count, values⟩ := Bool.and_eq_true_iff.mp same
  have rows : input.rows = output.rows := list_exact (list_exact cell_exact) values
  have length := beq_iff_eq.mp count
  cases input
  cases output
  simp_all

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem map_ok {α ε δ : Type} {input : Except ε α} {f : ε → δ} {out : α}
    (read : input.mapError f = .ok out) : input = .ok out := by
  cases input with
  | error => simp [Except.mapError] at read
  | ok => simpa only [Except.mapError, Except.ok.injEq] using read

theorem serialize_frame {limits : Limits} {schema : Schema} {input : Observation} {bytes : KBytes}
    (written : serialize limits schema input = .ok bytes) :
    ∃ planned, plan limits schema input = .ok planned ∧
      let record := encode input.rowCount planned
      Formats.Arrow.StreamWriter.emitFrame limits.schema.ipc record.message record.body = .ok bytes := by
  unfold serialize at written
  obtain ⟨planned, measured, framed⟩ := bind_ok written
  exact ⟨planned, measured, map_ok framed⟩

theorem emit_wire {limits : Limits} {schema : Schema} {input : Observation} {bytes : KBytes}
    (written : emit limits schema input = .ok bytes) : EmissionWire limits schema input bytes := by
  unfold emit at written
  obtain ⟨out, serialized, certified⟩ := bind_ok written
  obtain ⟨frame, opened, certified⟩ := bind_ok certified
  obtain ⟨logical, decoded, certified⟩ := bind_ok certified
  split at certified
  · rename_i agreement
    cases Except.ok.inj certified
    have exactRows := (agrees_exact agreement.2).symm
    cases exactRows
    exact ⟨serialize_frame serialized, frame, map_ok opened, agreement.1, map_ok decoded,
      decode_wire (map_ok decoded)⟩
  · contradiction

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Writer
