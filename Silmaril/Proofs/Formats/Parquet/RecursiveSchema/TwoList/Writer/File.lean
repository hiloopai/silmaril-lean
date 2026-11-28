module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Writer

open Silmaril.Formats
open Parquet.RecursiveSchema.TwoList
open Parquet.RecursiveSchema.TwoList.Writer
open Arrow.RecursiveSchema.Stream.Events (eraseBatch)

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (read : (first >>= next) = .ok value) : ∃ found, first = .ok found ∧ next found = .ok value := by
  cases first with
  | error => contradiction
  | ok result => exact ⟨result, rfl, read⟩

private theorem from_mapError {α ε δ : Type} {first : Except ε α} {wrap : ε → δ} {value : α}
    (read : first.mapError wrap = .ok value) : first = .ok value := by
  cases first with
  | error => simp [Except.mapError] at read
  | ok => simpa only [Except.mapError, Except.ok.injEq] using read

private theorem list_eq {α : Type} {test : α → α → Bool}
    (exact : ∀ {a b}, test a b = true → a = b) {xs ys : List α}
    (checked : xs.isEqv ys test = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons head tail ih =>
    cases ys with
    | nil => simp at checked
    | cons first rest =>
      simp only [List.isEqv_cons_cons, Bool.and_eq_true] at checked
      rw [exact checked.1, ih checked.2]

public theorem writeGroup_wire {limits : Limits} {checksum : Bool} {plan : Plan}
    {ordinal offset already : Nat} {input : Arrow.RecursiveSchema.Batch.Rows.Observation} {output : WrittenGroup}
    (written : writeGroup limits checksum plan ordinal offset already input = .ok output) :
    GroupWire limits checksum plan offset already input output := by
  unfold writeGroup at written
  obtain ⟨measured, _, written⟩ := bind_ok written
  dsimp only at written
  split at written
  · contradiction
  · rename_i payloadLength
    split at written
    · rename_i headerBytes encodedHeader
      split at written
      · contradiction
      · rename_i headerCap
        split at written
        · contradiction
        · rename_i frameCap
          cases Except.ok.inj written
          have length := Decidable.not_not.mp payloadLength
          refine ⟨measured.atoms, measured.projected, rfl, rfl, measured.rowCount.symm, rfl, rfl, rfl,
            ?_, measured.rows, measured.slots, measured.levelValues, measured.totalSlots,
            length.symm ▸ measured.bodyCap, Nat.le_of_not_gt headerCap, ?_⟩
          · simpa only [length] using encodedHeader
          · simpa [Parquet.PlainV1Writer.Encoded.wire, Bytes.length_append, length] using
              Nat.le_of_not_gt frameCap
    · contradiction

private theorem packGroups_wire {limits : Limits} {checksum : Bool} {plan : Plan}
    {inputs : List Arrow.RecursiveSchema.Batch.Rows.Observation} {ordinal offset slots : Nat}
    {outputs : List WrittenGroup}
    (written : packGroups limits checksum plan inputs ordinal offset slots = .ok outputs) :
    GroupsWire limits checksum plan offset slots inputs outputs := by
  induction inputs generalizing ordinal offset slots outputs with
  | nil =>
    cases Except.ok.inj written
    exact .nil offset slots
  | cons group groups ih =>
    simp only [packGroups] at written
    obtain ⟨first, firstBuilt, rest⟩ := bind_ok written
    obtain ⟨tail, tailBuilt, done⟩ := bind_ok rest
    cases Except.ok.inj done
    exact .cons (writeGroup_wire firstBuilt) (ih tailBuilt)

public theorem serialize_construction {limits : Limits} {input : Input} {output : Output}
    (built : serialize limits input = .ok output) : Construction limits input output := by
  unfold serialize at built
  obtain ⟨checked, inputRead, built⟩ := bind_ok built
  cases checked
  obtain ⟨declared, shape, built⟩ := bind_ok built
  obtain ⟨schemaOnly, envelope, built⟩ := bind_ok built
  obtain ⟨source, compiled, built⟩ := bind_ok built
  obtain ⟨groups, packed, built⟩ := bind_ok built
  obtain ⟨framed, full, done⟩ := bind_ok built
  cases Except.ok.inj done
  cases framed
  exact ⟨declared, schemaOnly, source, groups, inputRead, shape, from_mapError envelope,
    from_mapError compiled, packGroups_wire packed, from_mapError full, rfl⟩

public theorem certify_readback {limits : Limits} {input : Input} {output : Output}
    (accepted : certify limits input output = .ok ()) : Readback limits input output := by
  unfold certify at accepted
  obtain ⟨source, opened, accepted⟩ := bind_ok accepted
  have original := from_mapError opened
  split at accepted
  · rename_i same
    obtain ⟨⟨schema, trace⟩, eventsRead, accepted⟩ := bind_ok accepted
    have events := from_mapError eventsRead
    dsimp only at accepted
    cases terminal : trace.termination with
    | eos =>
      by_cases batches : (trace.batches.map eraseBatch).isEqv input.groups
          (Arrow.RecursiveSchema.Batch.Writer.agrees limits.schema.snapshot.maxSchemaDepth) = true
      ·
        have exactBatches : trace.batches.map eraseBatch = input.groups :=
          list_eq Arrow.RecursiveSchema.Batch.Writer.agrees_exact batches
        have rows := (Rows.Events.readSource_complete events).mp terminal
        rw [exactBatches] at rows
        simp only [agrees, Bool.and_eq_true, decide_eq_true_eq] at same
        have declarations := (Rows.Events.readSource_wire events).fields
        have shape := (Parquet.RecursiveSchema.Repeated.Writer.Schema.equal_exact same.1).symm
        exact ⟨source, ⟨schema, trace⟩, original, source.bytes_exact, same.2.1, same.2.2.1,
          shape, same.2.2.2, by simp [Rows.Events.read, original, events],
          shape ▸ declarations, terminal, exactBatches, rows, Rows.readAll_wire rows⟩
      · simp [terminal, batches] at accepted
    | closed => simp [terminal] at accepted
    | readError _ => simp [terminal] at accepted
    | closeError _ => simp [terminal] at accepted
  · contradiction

public theorem emit_wire {limits : Limits} {input : Input} {output : Output}
    (written : emit limits input = .ok output) : Construction limits input output ∧ Readback limits input output := by
  unfold emit at written
  obtain ⟨file, serialized, written⟩ := bind_ok written
  obtain ⟨checked, certified, done⟩ := bind_ok written
  cases checked
  cases Except.ok.inj done
  exact ⟨serialize_construction serialized, certify_readback certified⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Writer
