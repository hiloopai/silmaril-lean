module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Thms
import Silmaril.Formats.Parquet.Footer.ColumnOrder.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.File.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray.Utf8
open Silmaril.Formats.Arrow.MixedFlat
open Silmaril.Formats.Parquet.Plain.ByteArray
open Parquet.Footer.ColumnOrder (FlatLeaf FlatWire)

variable {parquet : File.Limits} {input : Bytes} {name : String} {layout : FlatColumn.Layout}
variable {checked : Checked name layout}

private theorem logical_exact {selected : FlatLeaf} {member : ThriftCompact.Traversal.Field}
    (accepted : checkLogical selected member = .ok ()) :
    member.id = 1 ∧ member.type = .payload .struct ∧
      ThriftCompact.Traversal.readStruct selected.selection.reader member.start = .ok ([], member.stop) := by
  by_cases tag : member.id = 1
  · by_cases type : member.type = .payload .struct
    · cases parsed : ThriftCompact.Traversal.readStruct selected.selection.reader member.start with
      | error cause => simp [checkLogical, tag, type, parsed, Except.mapError, Bind.bind, Except.bind] at accepted
      | ok result =>
        rcases result with ⟨fields, stop⟩
        by_cases extent : stop = member.stop
        · cases fields with
          | nil => exact ⟨tag, type, by simp [extent]⟩
          | cons first rest =>
            simp [checkLogical, tag, type, parsed, extent, Except.mapError, Bind.bind, Except.bind] at accepted
        · simp [checkLogical, tag, type, parsed, extent, Except.mapError, Bind.bind, Except.bind] at accepted
    · simp [checkLogical, tag, type, Bind.bind, Except.bind] at accepted
  · simp [checkLogical, tag, Bind.bind, Except.bind] at accepted

theorem readAnnotation_exact {selected : FlatLeaf} {annotation : Annotation}
    (accepted : readAnnotation selected = .ok annotation) :
    ∃ modern converted, selected.logicalMember = .ok modern ∧ selected.convertedType = .ok converted ∧
      (∀ member ∈ modern, member.id = 1 ∧ member.type = .payload .struct ∧
        ThriftCompact.Traversal.readStruct selected.selection.reader member.start = .ok ([], member.stop)) ∧
      classify modern.isSome converted = .ok annotation := by
  cases modern : selected.logicalMember with
  | error cause => simp [readAnnotation, modern, Except.mapError, Bind.bind, Except.bind] at accepted
  | ok marker =>
    cases checked : marker.mapM (checkLogical selected) with
    | error cause => simp [readAnnotation, modern, checked, Except.mapError, Bind.bind, Except.bind] at accepted
    | ok unit =>
      cases converted : selected.convertedType with
      | error cause =>
        simp [readAnnotation, modern, checked, converted, Except.mapError, Bind.bind, Except.bind] at accepted
      | ok code =>
        refine ⟨marker, code, rfl, rfl, ?_, ?_⟩
        · cases marker with
          | none => simp
          | some found =>
            intro member present
            have eq : found = member := by simpa using present
            subst member
            cases read : checkLogical selected found with
            | error cause => simp [Option.mapM, read] at checked
            | ok value => cases value; exact logical_exact read
        · simpa [readAnnotation, modern, checked, converted, Except.mapError, Bind.bind, Except.bind] using accepted

theorem openFile_wire (opened : openFile parquet input name layout = .ok checked) :
    File.openFile parquet input name layout = .ok checked.physical ∧
      Snapshot.check (Failure := Unit) parquet.snapshot input = .ok checked.physical.snapshot ∧
      ∃ selected, FlatWire parquet.snapshot.footer checked.physical.snapshot
          checked.physical.binding.columnOrdinal selected ∧
        selected.leaf = checked.physical.binding.leaf ∧
        readAnnotation selected = .ok checked.annotation := by
  unfold openFile at opened
  cases physical : File.openFile parquet input name layout with
  | error cause => simp [physical, Except.mapError, Bind.bind, Except.bind] at opened
  | ok bound =>
    simp only [physical, Except.mapError, Bind.bind, Except.bind] at opened
    split at opened
    · contradiction
    · rename_i selected selection
      split at opened
      · contradiction
      · rename_i observed annotation
        cases opened
        have raw := Footer.ColumnOrder.readFlat_wire selection
        have leaf : selected.leaf = bound.binding.leaf :=
          Option.some.inj (raw.leafAt.symm.trans bound.binding.leafAt)
        exact ⟨rfl, (File.openFile_wire physical).1, selected, raw, leaf, annotation⟩

private theorem decodeSlot_exact {ε : Type} {invalid : Nat → ε} {item : Option Bytes × Nat} {text : Option String}
    (decoded : decodeSlotWith invalid item = .ok text) :
    text.map (fun value => (⟨value.toByteArray⟩ : Bytes)) = item.1 := by
  rcases item with ⟨value, index⟩
  cases value with
  | none => cases decoded; rfl
  | some bytes =>
    by_cases valid : bytes.data.IsValidUTF8
    · have same : some (String.fromUTF8 bytes.data valid) = text := by
        simpa [decodeSlotWith, Option.mapM, String.fromUTF8?, valid, Bind.bind, Except.bind,
          Pure.pure, Except.pure] using decoded
      subst text
      cases bytes
      rfl
    · simp [decodeSlotWith, Option.mapM, String.fromUTF8?, valid] at decoded

theorem decodeSlotsWith_exact {ε : Type} {invalid : Nat → ε} {raw : List (Option Bytes)} {texts : List (Option String)}
    (decoded : decodeSlotsWith invalid raw = .ok texts) :
    texts.map (fun slot => slot.map (fun value => (⟨value.toByteArray⟩ : Bytes))) = raw := by
  have reads : List.Forall₂ (fun pair text => decodeSlotWith invalid pair = .ok text) raw.zipIdx texts :=
    List.mapM_eq_ok_iff_forall₂.mp decoded
  have octets := reads.flip.imp (fun _ _ h => decodeSlot_exact h)
  have same : List.Forall₂ (· = ·)
      (texts.map (fun slot => slot.map (fun value => (⟨value.toByteArray⟩ : Bytes))))
      (raw.zipIdx.map Prod.fst) :=
    List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr octets)
  rw [List.forall₂_eq_eq_eq, List.zipIdx_map_fst] at same
  exact same


theorem decodeSlots_exact {group : Nat} {raw : List (Option Bytes)} {texts : List (Option String)}
    (decoded : decodeSlots group raw = .ok texts) :
    texts.map (fun slot => slot.map (fun value => (⟨value.toByteArray⟩ : Bytes))) = raw :=
  decodeSlotsWith_exact decoded

theorem readGroup_wire {group : Nat} {slots : List (Option String)}
    (decoded : checked.readGroup parquet group = .ok slots) :
    ∃ original raw, File.GroupWire checked.physical parquet group original raw ∧
      decodeSlots group raw = .ok slots ∧
      slots.map (fun slot => slot.map (fun text => (⟨text.toByteArray⟩ : Bytes))) = raw := by
  cases physical : checked.physical.readGroup parquet group with
  | error cause => simp [Checked.readGroup, physical, Except.mapError, Bind.bind, Except.bind] at decoded
  | ok raw =>
    have text : decodeSlots group raw = .ok slots := by
      simpa [Checked.readGroup, physical, Except.mapError, Bind.bind, Except.bind] using decoded
    obtain ⟨original, wire⟩ := File.readGroup_wire physical
    exact ⟨original, raw, wire, text, decodeSlots_exact text⟩

theorem convert_readback {ipc : Arrow.MixedFlat.Limits} {wire : KBytes}
    (written : convert parquet ipc input name layout = .ok wire) :
    ∃ (checked : Checked name layout) (groups : List (List (Option String))) (decoded : Stream.Observed),
      openFile parquet input name layout = .ok checked ∧
      List.Forall₂ (fun index slots => checked.readGroup parquet index = .ok slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc wire = .ok decoded ∧ decoded.fields = fields name layout ∧
      decoded.batches.map StreamWriter.observeBatch = groups.map (fun slots =>
        (slots.length, some [(⟨name, layout == .optional, .view .utf8⟩, .utf8View slots)])) ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches := by
  cases opened : openFile parquet input name layout with
  | error cause => simp [convert, opened, Bind.bind, Except.bind] at written
  | ok checked =>
    cases decoded : (List.range checked.physical.snapshot.groupCount).mapM (checked.readGroup parquet) with
    | error cause => simp [convert, opened, decoded, Bind.bind, Except.bind] at written
    | ok groups =>
      have emitted : OrderedWriter.emit ipc (fields name layout) (groups.map (batch name layout)) = .ok wire := by
        cases h : OrderedWriter.emit ipc (fields name layout) (groups.map (batch name layout)) <;>
          simp_all [convert, Bind.bind, Except.bind, Except.mapError]
      obtain ⟨result, read, schema, values, wireEvidence⟩ := OrderedWriter.emit_readback emitted
      exact ⟨checked, groups, result, rfl, List.mapM_eq_ok_iff_forall₂.mp decoded,
        read, schema, by simpa [List.map_map, Function.comp_def, batch, OrderedWriter.BatchInput.observe,
          OrderedWriter.Column.field, OrderedWriter.Column.observe] using values, wireEvidence⟩

end Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8
