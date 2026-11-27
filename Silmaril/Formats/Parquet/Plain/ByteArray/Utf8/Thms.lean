module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Defs
import Batteries.Data.List.Lemmas
import Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Correctness

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.Utf8

open Footer.ColumnOrder (FlatLeaf FlatWire)
open Arrow.MixedFlat

variable {parquet : File.Limits} {input : Bytes} {name : String} {layout : FlatColumn.Layout}
variable {checked : Checked name layout}

/-- The legacy code must be UTF8 whenever present. A file needs at least one
of the two STRING annotations. -/
theorem classify_ok_iff (logical : Bool) (converted : Option Int) (annotation : Annotation) :
    classify logical converted = .ok annotation ↔
      match annotation with
      | .logical => logical = true ∧ converted = none
      | .logicalAndConverted => logical = true ∧ converted = some 0
      | .converted => logical = false ∧ converted = some 0 := by
  cases logical <;> cases converted <;> cases annotation <;> simp [classify] <;> split <;> simp_all

/-- The original modern marker is exactly an empty STRING struct. -/
theorem readAnnotation_exact {selected : FlatLeaf} {annotation : Annotation}
    (accepted : readAnnotation selected = .ok annotation) :
    ∃ modern converted, selected.logicalMember = .ok modern ∧ selected.convertedType = .ok converted ∧
      (∀ member ∈ modern, member.id = 1 ∧ member.type = .payload .struct ∧
        ThriftCompact.Traversal.readStruct selected.selection.reader member.start = .ok ([], member.stop)) ∧
      classify modern.isSome converted = .ok annotation :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.readAnnotation_exact accepted

/-- The annotation and physical reader use the same original footer leaf and snapshot. -/
theorem openFile_wire (opened : openFile parquet input name layout = .ok checked) :
    File.openFile parquet input name layout = .ok checked.physical ∧
      Snapshot.check (Failure := Unit) parquet.snapshot input = .ok checked.physical.snapshot ∧
      ∃ selected, FlatWire parquet.snapshot.footer checked.physical.snapshot
          checked.physical.binding.columnOrdinal selected ∧
        selected.leaf = checked.physical.binding.leaf ∧
        readAnnotation selected = .ok checked.annotation :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.openFile_wire opened

/-- An invalid present byte string reports its original group and logical slot. -/
theorem decodeSlot_invalid {group slot : Nat} {raw : Bytes} (invalid : ¬ raw.data.IsValidUTF8) :
    decodeSlot group (some raw, slot) = .error (.invalidText group slot) := by
  simp [decodeSlot, decodeSlotWith, Option.mapM, String.fromUTF8?, invalid]

/-- Profile-specific coordinates do not affect the exact octet observation. -/
theorem decodeSlotsWith_exact {ε : Type} {invalid : Nat → ε} {raw : List (Option Bytes)}
    {texts : List (Option String)} (decoded : decodeSlotsWith invalid raw = .ok texts) :
    texts.map (fun slot => slot.map (fun value => (⟨value.toByteArray⟩ : Bytes))) = raw :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.decodeSlotsWith_exact decoded

/-- Strict text decoding preserves the exact original nullable byte slots. -/
theorem decodeSlots_exact {group : Nat} {raw : List (Option Bytes)} {texts : List (Option String)}
    (decoded : decodeSlots group raw = .ok texts) :
    texts.map (fun slot => slot.map (fun value => (⟨value.toByteArray⟩ : Bytes))) = raw :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.decodeSlots_exact decoded

/-- The original framed PLAIN group and definition mask determine every text slot. -/
theorem readGroup_wire {group : Nat} {slots : List (Option String)}
    (decoded : checked.readGroup parquet group = .ok slots) :
    ∃ original raw, File.GroupWire checked.physical parquet group original raw ∧
      decodeSlots group raw = .ok slots ∧
      slots.map (fun slot => slot.map (fun text => (⟨text.toByteArray⟩ : Bytes))) = raw :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.readGroup_wire decoded

/-- Native readback preserves the exact text and one batch per checked footer group through EOS. -/
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
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.convert_readback written

/-- The first failed group returns its original cause before any IPC is written. -/
theorem convert_first_error {ipc : Arrow.MixedFlat.Limits} {before after : List Nat}
    {group : Nat} {earlier : List (List (Option String))} {cause : Error}
    (opened : openFile parquet input name layout = .ok checked)
    (indices : List.range checked.physical.snapshot.groupCount = before ++ group :: after)
    (prefixRead : before.mapM (checked.readGroup parquet) = .ok earlier)
    (failed : checked.readGroup parquet group = .error cause) :
    convert parquet ipc input name layout = .error cause := by
  simp [convert, opened, indices, List.mapM_append, prefixRead, List.mapM_cons, failed,
    Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Plain.ByteArray.Utf8
