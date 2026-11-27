module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer

private theorem list_eq_of_check {α : Type} [DecidableEq α] {xs ys : List α}
    (checked : xs.isEqv ys (fun a b => decide (a = b)) = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at checked
    | cons y ys =>
      simp only [List.isEqv_cons_cons, Bool.and_eq_true, decide_eq_true_eq] at checked
      rw [checked.1, ih checked.2]

public theorem construction {limits : Repeated.Chunk.Limits} {input : Input} {output : Output}
    (written : serialize limits input = .ok output) : Construction limits input output := by
  unfold serialize at written
  cases measured : measure limits input with
  | error error => simp [measured, Bind.bind, Except.bind] at written
  | ok plan =>
    simp only [measured, Bind.bind, Except.bind] at written
    split at written
    · contradiction
    · rename_i size
      cases encoded : PlainV1Writer.encodeHeaderWithChecksum input.atoms.length (body input).length
          (header input (body input)).crc with
      | none => simp [encoded, Pure.pure, Except.pure] at written
      | some headerBytes =>
        simp only [encoded, Pure.pure, Except.pure] at written
        split at written
        · contradiction
        · rename_i headerCap
          split at written
          · contradiction
          · rename_i frameCap
            cases Except.ok.inj written
            refine ⟨⟨plan, measured, ?_, rfl⟩, rfl, rfl, encoded, ?_, ?_⟩
            · simpa using size
            · exact Nat.le_of_not_gt headerCap
            · simpa [Output.wire, PlainV1Writer.Encoded.wire] using Nat.le_of_not_gt frameCap

public theorem agrees_exact {input : Input} {after : Repeated.Chunk.State}
    {page : Repeated.Chunk.DecodedPage} (checked : agrees input after page = true) :
    page.levels = input.atoms.map (·.levels) ∧
      page.words = input.atoms.map (·.word) ∧ page.after = after := by
  simp only [agrees, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨list_eq_of_check checked.1.1, list_eq_of_check checked.1.2, checked.2⟩

public theorem readback {limits : Repeated.Chunk.Limits} {input : Input} {output : Output}
    (checked : certify limits input output = .ok ()) : Readback limits input output := by
  unfold certify at checked
  cases framed : Page.readPage limits.framing output.wire ⟨0, output.wire.length⟩ 0 with
  | error error => simp [framed, Except.mapError, Bind.bind, Except.bind] at checked
  | ok frame =>
    simp only [framed, Except.mapError, Bind.bind, Except.bind] at checked
    split at checked
    · contradiction
    · rename_i same
      have sameFrame : frame = output.frame := by simpa using same
      subst frame
      cases decoded : Repeated.Chunk.decodePage limits input.leaf output.wire output.frame
          input.start (limits.maxSlots - input.start.slot) limits.maxRows with
      | error error => simp [decoded] at checked
      | ok page =>
        simp only [decoded] at checked
        split at checked
        · rename_i agreement
          exact ⟨framed, page, decoded, Repeated.Chunk.decodePage_wire decoded,
            agrees_exact agreement⟩
        · contradiction

public theorem state_counts {limits : Repeated.Chunk.Limits} {input : Input} {output : Output}
    (accepted : Readback limits input output) :
    input.start.slot + input.atoms.length = output.after.slot ∧
      input.start.rows + (input.atoms.map (·.levels)).countP Repeated.Chunk.LevelSlot.startsRow =
        output.after.rows := by
  obtain ⟨page, _, wire, levels, _, after⟩ := accepted.exact
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, slots, _⟩ := wire.original
  simpa [levels, after] using slots.counts

public theorem emit_wire {limits : Repeated.Chunk.Limits} {input : Input} {output : Output}
    (written : emit limits input = .ok output) :
    Construction limits input output ∧ Readback limits input output := by
  unfold emit at written
  cases serialized : serialize limits input with
  | error error => simp [serialized, Bind.bind, Except.bind] at written
  | ok page =>
    simp only [serialized, Bind.bind, Except.bind] at written
    cases checked : certify limits input page with
    | error error => simp [checked] at written
    | ok done =>
      cases done
      simp only [checked, Pure.pure, Except.pure] at written
      cases Except.ok.inj written
      exact ⟨construction serialized, readback checked⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer
