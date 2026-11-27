module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer

open Silmaril.Formats
open Parquet.RecursiveSchema.Repeated
open Parquet.RecursiveSchema.Repeated.Writer

private theorem matching {α : Type} {test : α → α → Bool}
    (exactness : ∀ {a b}, test a b = true → a = b) {xs ys : List α}
    (checked : xs.isEqv ys test = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons head tail ih =>
    cases ys with
    | nil => simp at checked
    | cons first rest =>
      simp only [List.isEqv_cons_cons, Bool.and_eq_true] at checked
      rw [exactness checked.1, ih checked.2]

public theorem column_wire {limits : Limits} {checksum : Bool} {group column rows : Nat}
    {start : Writer.Position} {leaf : Leaf} {atoms : List Rows.Atom} {cuts : Option (List Nat)}
    {placed : Placed}
    (written : writeColumn limits checksum group column rows start leaf atoms cuts = .ok placed) :
    ColumnWire limits checksum group column rows start leaf atoms cuts placed := by
  unfold writeColumn at written
  dsimp only at written
  split at written
  · contradiction
  · cases divided : partition atoms cuts with
    | none => simp [divided] at written
    | some pages =>
      simp only [divided, Pure.pure, Except.pure, bind, Except.bind] at written
      cases emitted : Chunk.Writer.Multi.emit (chunkLimits limits start)
          ⟨leaf, rows, pages.val, checksum, group, column⟩ with
      | error cause => simp [emitted, Except.mapError] at written
      | ok chunk =>
        simp only [emitted, Except.mapError] at written
        cases Except.ok.inj written
        obtain ⟨packed, _, built, checked⟩ := Chunk.Writer.Multi.emit_wire emitted
        exact ⟨pages, chunk, packed, divided, emitted, built, checked, rfl⟩

public theorem serialize_construction {limits : Limits} {input : Input} {output : Output}
    (written : serialize limits input = .ok output) : Construction limits input output := by
  unfold serialize at written
  cases admitted : checkInput limits input with
  | error cause => simp [admitted, bind, Except.bind] at written
  | ok done =>
    cases done
    simp only [admitted, bind, Except.bind] at written
    cases inverse : Schema.emit limits.schema input.schema with
    | error cause => simp [inverse, Except.mapError] at written
    | ok schema =>
      simp only [inverse, Except.mapError] at written
      cases packed : pack limits input schema.source.schema.fields schema.source.schema.leaves.toList with
      | error cause => simp [packed] at written
      | ok body =>
        simp only [packed] at written
        cases framed : Schema.wrap limits.schema body.payload schema.plan body.groups with
        | error cause => simp [framed] at written
        | ok file =>
          simp only [framed, Pure.pure, Except.pure] at written
          cases Except.ok.inj written
          cases file
          exact ⟨schema, body, admitted, Schema.emit_wire inverse, packed, framed, rfl⟩

public theorem certify_readback {limits : Limits} {input : Input} {output : Output}
    (accepted : certify limits input output = .ok ()) : Readback limits input output := by
  unfold certify at accepted
  cases opened : openFile limits.schema.snapshot output.bytes with
  | error cause => simp [opened, Except.mapError, bind, Except.bind] at accepted
  | ok source =>
    simp only [opened, Except.mapError, bind, Except.bind] at accepted
    split at accepted
    · rename_i header
      cases read : Rows.readAll limits.rows source.schema with
      | error cause => simp [read] at accepted
      | ok recovered =>
        simp only [read] at accepted
        split at accepted
        · rename_i equalRows
          have exactRows : recovered = input.observations :=
            matching Arrow.RecursiveSchema.Batch.Writer.agrees_exact equalRows
          subst recovered
          simp only [agrees, Bool.and_eq_true, decide_eq_true_eq] at header
          exact ⟨source, opened, source.bytes_exact, header.2.1, header.2.2.1,
            (Schema.equal_exact header.1).symm, header.2.2.2, read, Rows.readAll_wire read⟩
        · contradiction
    · contradiction

public theorem emit_wire {limits : Limits} {input : Input} {output : Output}
    (written : emit limits input = .ok output) :
    Construction limits input output ∧ Readback limits input output := by
  unfold emit at written
  cases built : serialize limits input with
  | error cause => simp [built, bind, Except.bind] at written
  | ok file =>
    simp only [built, bind, Except.bind] at written
    cases checked : certify limits input file with
    | error cause => simp [checked] at written
    | ok done =>
      cases done
      simp only [checked, Pure.pure, Except.pure] at written
      cases Except.ok.inj written
      exact ⟨serialize_construction built, certify_readback checked⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer
