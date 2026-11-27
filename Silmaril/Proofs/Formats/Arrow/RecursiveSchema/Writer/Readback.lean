module

public import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Writer.Size
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Writer

open Silmaril.Formats.Arrow.RecursiveSchema (Field Schema Limits)
open Silmaril.Formats.Arrow.RecursiveSchema.Writer

private theorem equalFields_exact {equal : Field → Field → Bool}
    (compare : ∀ {left right}, equal left right = true → left = right)
    {left right : List Field} (same : equalFields equal left right = true) :
    left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [equalFields] at same ⊢
  | cons field rest ih =>
    cases right with
    | nil => simp [equalFields] at same
    | cons other others =>
      obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp same
      exact congrArg₂ List.cons (compare head) (ih tail)

private theorem equalField_exact {depth : Nat} {left right : Field}
    (same : equalField depth left right = true) : left = right := by
  induction depth generalizing left right with
  | zero => simp [equalField] at same
  | succ depth ih =>
    obtain ⟨name, nullable, kind, children⟩ := left
    obtain ⟨otherName, otherNullable, otherKind, otherChildren⟩ := right
    simp only [equalField, Bool.and_eq_true, beq_iff_eq] at same
    obtain ⟨⟨⟨names, flags⟩, kinds⟩, childCompare⟩ := same
    cases names
    cases flags
    cases kinds
    exact congrArg (Field.node name nullable kind) (equalFields_exact ih childCompare)

theorem equalSchema_exact {depth : Nat} {left right : Schema}
    (same : equalFields (equalField depth) left.fields right.fields = true) : left = right :=
  congrArg Schema.mk (equalFields_exact equalField_exact same)

private theorem agrees_exact {depth : Nat} {schema : Schema}
    {decoded : Formats.Arrow.RecursiveSchema.Stream.Trace} (same : agrees depth schema decoded = true) :
    decoded = ⟨schema, decoded.schemaEnd, [], .eos 0 decoded.schemaEnd⟩ := by
  simp only [agrees, Bool.and_eq_true] at same
  obtain ⟨⟨fields, empty⟩, eos⟩ := same
  have declarations : decoded.schema = schema :=
    equalSchema_exact fields
  have noBatches := List.isEmpty_iff.mp empty
  have ending := beq_iff_eq.mp eos
  cases decoded
  simp_all

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

theorem emit_wire {limits : Limits} {schema : Schema} {bytes : KBytes}
    (accepted : emit limits schema = .ok bytes) : EmissionWire limits schema bytes := by
  unfold emit at accepted
  obtain ⟨out, written, accepted⟩ := bind_ok accepted
  cases decoded : Formats.Arrow.RecursiveSchema.Stream.read { schema := limits } out with
  | error cause => simp [decoded, Except.mapError, bind, Except.bind] at accepted
  | ok trace =>
    simp only [decoded, Except.mapError, bind, Except.bind] at accepted
    split at accepted
    · rename_i agreement
      cases Except.ok.inj accepted
      have actual := agrees_exact agreement
      have original := Formats.Arrow.RecursiveSchema.Stream.read_iff.mp decoded |>.1
      have atEnd : trace.terminal = .eos 0 trace.schemaEnd :=
        congrArg Formats.Arrow.RecursiveSchema.Stream.Trace.terminal actual
      have wire := Formats.Arrow.RecursiveSchema.Stream.readTrace_eos original atEnd
      refine ⟨serialize_extent written, trace.schemaEnd, ?_, wire.2⟩
      exact decoded.trans (congrArg Except.ok actual)
    · contradiction

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Writer
