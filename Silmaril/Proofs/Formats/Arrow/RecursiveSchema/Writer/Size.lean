module

public import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Defs
import Silmaril.Formats.Arrow.Writer.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Writer

open Silmaril.Formats.Arrow.RecursiveSchema (Field Schema Limits)
open Silmaril.Formats.Arrow.RecursiveSchema.Writer
open Silmaril.Formats.Arrow.RecursiveSchema.Writer.Wire
open Silmaril.Formats.Arrow.MetadataWriter.Wire
  (words halfwords longs pad fieldOffsets messagePrefix schemaPayloadOf)

private theorem appendLen (left right : KBytes) : (left ++ right).len = left.len + right.len := rfl
private theorem zerosLen (size : Nat) : (KBytes.zeros size).len = size := rfl

private theorem offsets_length (slot start : Nat) (objects : List KBytes) :
    (fieldOffsets slot start objects).length = objects.length := by
  induction objects generalizing slot start with
  | nil => rfl
  | cons object rest ih => simp [fieldOffsets, ih]

private theorem type_extent (kind : Formats.Arrow.RecursiveSchema.Wire.Kind) :
    (typeFragment kind).len = 20 := by
  cases kind <;> rfl

private theorem name_extent (name : Option String) : (nameFragment name).len = nameSize name := by
  cases name with
  | none => rfl
  | some value =>
    have count : value.toByteArray.data.toList.length = value.utf8ByteSize := rfl
    simp only [nameFragment, nameSize, words, Formats.Arrow.Writer.emitWords_length,
      appendLen, zerosLen, List.length_cons, List.length_nil, List.length_map, count]
    omega

theorem header_extent (name : Option String) (nullable : Bool)
    (kind : Formats.Arrow.RecursiveSchema.Wire.Kind) (children : Nat) :
    (fieldHeader name nullable kind children).len = 68 := by
  simp [fieldHeader, words, Formats.Arrow.Writer.emitWords_length, appendLen, type_extent]

theorem prefix_extent (name : Option String) (nullable : Bool)
    (kind : Formats.Arrow.RecursiveSchema.Wire.Kind) (children : List KBytes) :
    (fieldPrefix name nullable kind children).len = fieldPrefixSize name children.length := by
  simp only [fieldPrefix, pad, appendLen, zerosLen, header_extent, name_extent, words,
    Formats.Arrow.Writer.emitWords_length, List.length_cons, offsets_length]
  have rawExtent : 68 + (4 * (children.length + 1) + nameSize name) =
      vectorEnd children.length + nameSize name := by simp [vectorEnd]; omega
  rw [rawExtent]
  rfl

private theorem forest_extent (fields : List Field) :
    ((fields.map fieldFragment).foldr (· ++ ·) KBytes.empty).len = (fields.map fieldSize).sum := by
  refine Field.rec_1
    (motive_1 := fun field => (fieldFragment field).len = fieldSize field)
    (motive_2 := fun fields =>
      ((fields.map fieldFragment).foldr (· ++ ·) KBytes.empty).len = (fields.map fieldSize).sum)
    ?_ ?_ ?_ fields
  · intro name nullable kind children ih
    simp only [fieldFragment, fieldSize, appendLen, prefix_extent, List.length_map, ih]
  · rfl
  · intro head tail headSize tailSize
    simp only [List.map_cons, List.foldr_cons, List.sum_cons, appendLen, headSize, tailSize]

theorem metadata_extent (schema : Schema) :
    (metadata schema).len = metadataSize schema := by
  simp only [metadata, metadataSize, schemaPayloadOf, schemaPrefixSize, appendLen, zerosLen,
    List.length_map, forest_extent, messagePrefix, words, longs, Formats.Arrow.Writer.emitWords_length,
    List.length_cons, List.length_nil, offsets_length]
  rw [Nat.mul_comm schema.fields.length 4]
  omega

theorem offsets_target {slot start index : Nat} {objects : List KBytes}
    (bound : index < objects.length) :
    (fieldOffsets slot start objects)[index]? =
      some (start + ((objects.take index).map KBytes.len).sum + 12 - (slot + 4 * index)) := by
  induction objects generalizing slot start index with
  | nil => simp at bound
  | cons head rest ih =>
    cases index with
    | zero => simp [fieldOffsets]
    | succ index =>
      simp only [fieldOffsets, List.getElem?_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
      rw [ih (by simpa using bound)]
      congr 1
      omega

/-- Every shared child or root offset word points forward inside the forest
extent when objects have space for their table at byte 12. -/
theorem offsets_forward {slot start : Nat} {objects : List KBytes}
    (gap : slot + 4 * objects.length ≤ start)
    (objectsFit : ∀ object ∈ objects, 16 ≤ object.len) :
    ∀ offset ∈ fieldOffsets slot start objects,
      4 ≤ offset ∧ offset < start + (objects.map KBytes.len).sum := by
  induction objects generalizing slot start with
  | nil => simp [fieldOffsets]
  | cons object rest ih =>
    have extent := objectsFit object (by simp)
    have nextGap : slot + 4 + 4 * rest.length ≤ start + object.len := by
      simp only [List.length_cons] at gap
      omega
    intro offset member
    simp only [fieldOffsets, List.mem_cons] at member
    rcases member with rfl | later
    · simp only [List.map_cons, List.sum_cons]
      simp only [List.length_cons] at gap
      omega
    · obtain ⟨lower, upper⟩ := ih nextGap (fun bytes found => objectsFit bytes (by simp [found])) offset later
      exact ⟨lower, by simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using upper⟩

private def Within (limits : Limits) (budget : Budget) : Prop :=
  budget.fields ≤ limits.ipc.fields ∧ budget.bytes < 2^31 ∧ budget.bytes ≤ limits.ipc.metadataBytes

private theorem checked_size {limits : Limits} {bytes : Nat} (accepted : checkSize limits bytes = .ok ()) :
    bytes < 2^31 ∧ bytes ≤ limits.ipc.metadataBytes := by
  unfold checkSize at accepted
  split at accepted
  · contradiction
  · rename_i wire
    split at accepted
    · contradiction
    · rename_i budget
      exact ⟨Nat.lt_of_not_ge wire, Nat.le_of_not_gt budget⟩

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem planned_fields {limits : Limits} {visit : Field → Budget → Except Error Budget}
    (each : ∀ {field start next}, Within limits start → visit field start = .ok next →
      next.bytes = start.bytes + fieldSize field ∧ Within limits next)
    {fields start next} (before : Within limits start) (accepted : planFields visit fields start = .ok next) :
    next.bytes = start.bytes + (fields.map fieldSize).sum ∧ Within limits next := by
  induction fields generalizing start next with
  | nil =>
    simp [planFields] at accepted
    subst next
    exact ⟨rfl, before⟩
  | cons field tail ih =>
    simp only [planFields] at accepted
    obtain ⟨middle, first, rest⟩ := bind_ok accepted
    obtain ⟨extent, within⟩ := each before first
    obtain ⟨total, bound⟩ := ih within rest
    exact ⟨by simp only [List.map_cons, List.sum_cons]; omega, bound⟩

private theorem planned_field {limits : Limits} {depth : Nat} {field : Field} {start next : Budget}
    (before : Within limits start) (accepted : planField limits depth field start = .ok next) :
    next.bytes = start.bytes + fieldSize field ∧ Within limits next := by
  induction depth generalizing field start next with
  | zero => simp [planField] at accepted
  | succ depth ih =>
    obtain ⟨name, nullable, kind, children⟩ := field
    unfold planField at accepted
    split at accepted
    · contradiction
    · rename_i fieldCap
      dsimp only at accepted
      split at accepted
      · contradiction
      · obtain ⟨checked, size, childrenRead⟩ := bind_ok accepted
        cases checked
        have reserved := checked_size size
        have budget : Within limits ⟨start.fields + 1, start.bytes + fieldPrefixSize name children.length⟩ :=
          ⟨by change start.fields + 1 ≤ limits.ipc.fields; omega, reserved.1, reserved.2⟩
        obtain ⟨total, bound⟩ := planned_fields (fun h read => ih h read) budget childrenRead
        dsimp only at total
        exact ⟨by simp only [fieldSize]; omega, bound⟩

theorem plan_extent {limits : Limits} {schema : Schema} {budget : Budget}
    (accepted : plan limits schema = .ok budget) :
    budget.bytes = metadataSize schema ∧ budget.bytes < 2^31 ∧
      budget.bytes ≤ limits.ipc.metadataBytes ∧ budget.fields ≤ limits.ipc.fields := by
  unfold plan at accepted
  obtain ⟨checked, size, fieldsRead⟩ := bind_ok accepted
  cases checked
  have reserved := checked_size size
  have initial : Within limits ⟨0, schemaPrefixSize schema.fields.length⟩ :=
    ⟨Nat.zero_le _, reserved.1, reserved.2⟩
  obtain ⟨extent, bound⟩ := planned_fields planned_field initial fieldsRead
  exact ⟨extent, bound.2.1, bound.2.2, bound.1⟩

theorem serializeFrame_extent {limits : Limits} {schema : Schema} {bytes : KBytes}
    (written : serializeFrame limits schema = .ok bytes) :
    ∃ budget, plan limits schema = .ok budget ∧
      budget.bytes = (metadata schema).len ∧ budget.bytes < 2^31 ∧
      budget.bytes ≤ limits.ipc.metadataBytes ∧
      bytes = Formats.Arrow.StreamWriter.envelopeBytes budget.bytes ++ metadata schema := by
  unfold serializeFrame at written
  obtain ⟨budget, setup, output⟩ := bind_ok written
  obtain ⟨extent, word, cap, _⟩ := plan_extent setup
  cases Except.ok.inj output
  exact ⟨budget, setup, extent.trans (metadata_extent schema).symm, word, cap, rfl⟩

theorem serialize_extent {limits : Limits} {schema : Schema} {bytes : KBytes}
    (accepted : serialize limits schema = .ok bytes) :
    ∃ budget, plan limits schema = .ok budget ∧
      budget.bytes = metadataSize schema ∧ budget.bytes = (metadata schema).len ∧
      budget.bytes < 2^31 ∧ budget.bytes ≤ limits.ipc.metadataBytes ∧
      bytes = Formats.Arrow.StreamWriter.envelopeBytes budget.bytes ++
        (metadata schema ++ Formats.Arrow.StreamWriter.eos) := by
  unfold serialize at accepted
  obtain ⟨budget, setup, output⟩ := bind_ok accepted
  obtain ⟨extent, word, cap, _⟩ := plan_extent setup
  cases Except.ok.inj output
  exact ⟨budget, setup, extent, extent.trans (metadata_extent schema).symm, word, cap, rfl⟩

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Writer
