module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics.Thms
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.Projection
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.Typing

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows

open Silmaril.Formats.Arrow.RecursiveSchema (Schema)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch (Limits Frame First)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows

theorem row_at {physical : Formats.Arrow.RecursiveSchema.Batch.Semantics.Observation}
    {logical : Observation} (wire : ProjectionWire physical logical) {index : Nat} {row : Row}
    (selected : logical.rows[index]? = some row) :
    CellsWire (physical.columns.map fun column => (column, index)) row := by
  obtain ⟨length, entry⟩ := List.forall₂_iff_get.mp wire.positions
  obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp selected
  have source : index < (List.range physical.rowCount).length := length ▸ bound
  simpa only [List.get_eq_getElem, List.getElem_range, value] using entry index source bound

private theorem word_slice {width : Nat} {words : List (List UInt8)} {slot : Nat}
    {word : List UInt8} (sized : ∀ entry ∈ words, entry.length = width)
    (selected : words[slot]? = some word) :
    (words.flatten.drop (width * slot)).take width = word := by
  induction words generalizing slot with
  | nil => simp at selected
  | cons head tail ih =>
    have extent := sized head (by simp)
    cases slot with
    | zero =>
      simp at selected
      subst word
      simp [List.take_left' extent]
    | succ slot =>
      simp only [List.getElem?_cons_succ] at selected
      rw [List.flatten_cons, Nat.mul_succ, Nat.add_comm (width * slot) width,
        ← List.drop_drop, List.drop_left' extent]
      exact ih (fun entry member => sized entry (by simp [member])) selected

theorem signedWord_at {α : Type} {width count slot : Nat} {interpret : List UInt8 → α}
    {bytes : KBytes} {words : List α} {value : α}
    (wire : Formats.Arrow.RecursiveSchema.Batch.Semantics.SignedWords width count interpret bytes words)
    (selected : words[slot]? = some value) :
    value = interpret ((bytes.toList.drop (width * slot)).take width) := by
  obtain ⟨original, regions, _, sized, decoded⟩ := wire
  rw [decoded, List.getElem?_map] at selected
  cases entry : original[slot]? with
  | none => simp [entry] at selected
  | some word =>
    simp [entry] at selected
    rw [regions, word_slice sized entry, selected]

theorem validity_at {body : KBytes} {node : Formats.Arrow.FieldNode} {buffer : Formats.Arrow.Buffer}
    {nullable valid : Bool} {visible : Array Bool}
    {presence : Formats.Arrow.RecursiveSchema.Batch.Semantics.Presence} {slot : Nat}
    (wire : Formats.Arrow.RecursiveSchema.Batch.Semantics.PresenceWire
      body node buffer nullable visible presence)
    (selected : presence.valid[slot]? = some valid) :
    Formats.Arrow.Body.validAt (Formats.Arrow.Body.sliceBuffer body buffer) slot = some valid := by
  obtain ⟨length, entry⟩ := List.forall₂_iff_get.mp wire.fromBitmap
  rw [← Array.getElem?_toList] at selected
  obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp selected
  have source : slot < (List.range node.length).length := length ▸ bound
  simpa only [List.get_eq_getElem, List.getElem_range, value] using entry slot source bound

private theorem wire_of_projection {limits : Limits} {schema : Schema} {input : KBytes}
    {offset : Nat} {frame : Frame limits schema input offset}
    {physical : Formats.Arrow.RecursiveSchema.Batch.Semantics.Observation} {logical : Observation}
    (physicalWire : Formats.Arrow.RecursiveSchema.Batch.Semantics.ObservationWire frame physical)
    (projected : ProjectionWire physical logical) : ObservationWire frame logical := by
  have length : logical.rows.length = physical.rowCount := by
    simpa using projected.positions.length_eq.symm
  refine ⟨⟨physical, physicalWire, projected⟩, projected.rowCount.trans physicalWire.rowCount,
    length.trans physicalWire.rowCount, ?_⟩
  intro row member
  obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp member
  exact cells_typed physicalWire.columns (row_at projected (List.getElem?_eq_getElem bound))

theorem decode_wire {limits : Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    {frame : Frame limits schema input offset} {logical : Observation}
    (read : decode frame = .ok logical) : ObservationWire frame logical := by
  simp only [decode, bind, Except.bind] at read
  cases physical : Formats.Arrow.RecursiveSchema.Batch.Semantics.decode frame with
  | error cause => simp [physical, Except.mapError] at read
  | ok observed =>
    simp only [physical, Except.mapError] at read
    exact wire_of_projection (Formats.Arrow.RecursiveSchema.Batch.Semantics.decode_wire physical)
      (project_wire read)

theorem readFirst_wire {limits : Limits} {input : KBytes} {first : First limits input}
    {logical : Observation} (read : readFirst limits input = .ok (first, logical)) :
    ObservationWire first.batch logical := by
  simp only [readFirst, bind, Except.bind] at read
  cases source : Formats.Arrow.RecursiveSchema.Batch.Semantics.readFirst limits input with
  | error cause => simp [source, Except.mapError] at read
  | ok result =>
    obtain ⟨checked, physical⟩ := result
    simp only [source, Except.mapError] at read
    cases projected : project limits.schema.depth physical with
    | error cause => simp [projected] at read
    | ok observed =>
      simp [projected, pure, Except.pure] at read
      obtain ⟨rfl, rfl⟩ := read
      exact wire_of_projection (Formats.Arrow.RecursiveSchema.Batch.Semantics.readFirst_wire source)
        (project_wire projected)

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows
