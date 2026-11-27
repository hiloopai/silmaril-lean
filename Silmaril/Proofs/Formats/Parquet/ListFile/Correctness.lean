module

public import Silmaril.Formats.Parquet.ListFile.Defs
import all Silmaril.Formats.Parquet.ListFile.Defs
import Silmaril.Formats.Parquet.Footer.NestedLeaf.Thms
import Silmaril.Formats.Parquet.ListPage.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Reader.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile

open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile
open Silmaril.Formats.Parquet.Footer
open Silmaril.Formats.ThriftCompact
open Silmaril.Relational

private theorem field_selected {fields : List Traversal.Field} {id : Int}
    {field : Traversal.Field} (h : ColumnOrder.field? fields id = .ok (some field)) :
    fields.filter (·.id == id) = [field] := by
  unfold ColumnOrder.field? at h
  split at h <;> simp_all

private theorem checkConvertedList_wire {reader : Traversal.Reader}
    {legacy : Option Traversal.Field} (h : checkConvertedList reader legacy = .ok ()) :
    ConvertedWire reader legacy := by
  cases legacy with
  | none => trivial
  | some field =>
    by_cases typed : field.type = .payload .i32
    · cases read : readSigned .i32 reader.mode reader.source field.start with
      | error e => simp [checkConvertedList, typed, read, Except.mapError, Bind.bind, Except.bind] at h
      | ok result =>
        obtain ⟨value, stop⟩ := result
        simp [checkConvertedList, typed, read, Except.mapError, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨typed, read⟩
    · simp [checkConvertedList, typed] at h

public theorem checkList_wire {reader : Traversal.Reader} {outer : ColumnOrder.Item}
    (h : checkList reader outer = .ok ()) :
    AnnotationWire reader outer := by
  constructor
  unfold checkList at h
  cases found : ColumnOrder.field? outer.fields 10 with
  | error e => simp [found, Except.mapError, Bind.bind, Except.bind] at h
  | ok selected =>
    cases selected with
    | none => simp [found, Except.mapError, Bind.bind, Except.bind] at h
    | some logical =>
      simp only [found, Except.mapError, Bind.bind, Except.bind] at h
      split at h
      · contradiction
      · rename_i typed
        push Not at typed
        cases read : Traversal.readStruct reader logical.start with
        | error e => simp [read] at h
        | ok result =>
          obtain ⟨members, stop⟩ := result
          simp only [read] at h
          split at h
          · rename_i member
            split at h
            · contradiction
            · rename_i exactUnion
              push Not at exactUnion
              obtain ⟨rfl, tag, kind⟩ := exactUnion
              cases readMarker : Traversal.readStruct reader member.start with
              | error e => simp [readMarker] at h
              | ok result =>
                obtain ⟨payload, next⟩ := result
                simp only [readMarker] at h
                split at h
                · contradiction
                · rename_i exactMarker
                  push Not at exactMarker
                  obtain ⟨rfl, rfl⟩ := exactMarker
                  cases legacy : ColumnOrder.field? outer.fields 6 with
                  | error e => simp [legacy] at h
                  | ok converted =>
                    simp only [legacy] at h
                    exact ⟨logical, member, converted, field_selected found, typed,
                      read, tag, kind, readMarker, rfl, checkConvertedList_wire h⟩
          · contradiction

public theorem admittedFor_repetition {container : Container} {shape : Shape}
    (h : shape.admittedFor container = true) :
    shape.outer.repetition = some container.repetition ∧ shape.element.repetition = some .optional := by
  simp only [Shape.admittedFor, Bool.and_eq_true, beq_iff_eq] at h
  grind

private theorem readShapeFor_wire {container : Container} {schema : List Footer.SchemaElement} {shape : Shape}
    (h : readShapeFor container schema = .ok shape) :
    schema = [shape.root, shape.outer, shape.repeated, shape.element] ∧ shape.admittedFor container = true := by
  unfold readShapeFor at h
  split at h
  · dsimp only at h
    split at h
    · cases h
      exact ⟨rfl, by assumption⟩
    · contradiction
  · contradiction

public theorem openFileFor_wire {container : Container} {limits : ListFile.Limits} {source : Bytes} {checked : Checked container}
    (h : openFileFor container limits source = .ok checked) : OpenWire limits source checked := by
  unfold openFileFor at h
  split at h
  · contradiction
  · rename_i cap
    simp only [Except.mapError, Bind.bind, Except.bind] at h
    cases snapshotRead : Snapshot.check (Failure := Unit) limits.snapshot source with
    | error err => simp [snapshotRead] at h
    | ok snapshot =>
      simp only [snapshotRead] at h
      cases shapeRead : readShapeFor container snapshot.metadata.schema with
      | error err => simp [shapeRead] at h
      | ok shape =>
        simp only [shapeRead] at h
        cases raw : NestedLeaf.readItems limits.snapshot.footer snapshot with
        | error err => simp [raw] at h
        | ok result =>
          obtain ⟨container, items⟩ := result
          simp only [raw] at h
          split at h
          · rename_i root outer repeated element
            split at h
            · contradiction
            · rename_i extents
              push Not at extents
              split at h
              · contradiction
              · rename_i clean
                have unmarked : unannotated root = true ∧ unannotated repeated = true ∧
                    unannotated element = true := by simpa [and_assoc] using clean
                cases tag : checkList (ColumnOrder.footerReader limits.snapshot.footer snapshot) outer with
                | error err => simp [tag] at h
                | ok accepted =>
                  cases accepted
                  simp only [tag, Pure.pure, Except.pure] at h
                  cases h
                  exact ⟨Nat.le_of_not_gt cap, rfl, snapshotRead, readShapeFor_wire shapeRead,
                    container, root, outer, repeated, element, NestedLeaf.readItems_wire raw,
                    extents.1, extents.2, unmarked.1, unmarked.2.1, unmarked.2.2, checkList_wire tag⟩
          · contradiction

public theorem openFile_wire {limits : ListFile.Limits} {source : Bytes} {checked : Checked}
    (h : openFile limits source = .ok checked) : OpenWire limits source checked :=
  openFileFor_wire h

public theorem frameGroupWith_wire {container : Container} {checked : Checked container} {codec : Int} {allowDictionary : Bool}
    {index : Nat} {framed : FramedGroup} (h : checked.frameGroupWith codec allowDictionary index = .ok framed) :
    ChunkFrameWire checked index framed codec ∧
      (allowDictionary = false → framed.chunk.metadata.dictionaryPageOffset = none) := by
  unfold Checked.frameGroupWith at h
  cases groupRead : checked.snapshot.groupAt index with
  | none => simp [groupRead] at h
  | some group =>
    simp only [groupRead] at h
    split at h
    · rename_i chunk columns
      split at h
      · contradiction
      · rename_i associated
        push Not at associated
        split at h
        · contradiction
        · rename_i codec
          push Not at codec
          split at h
          · contradiction
          · rename_i offsets
            have indexAbsent : chunk.metadata.indexPageOffset = none := by
              cases tag : chunk.metadata.indexPageOffset <;> simp_all
            have dictionaryAbsent (refuses : allowDictionary = false) :
                chunk.metadata.dictionaryPageOffset = none := by simpa [refuses, indexAbsent] using offsets
            cases bounds : Page.columnSpan checked.snapshot.footer.start chunk.metadata with
            | none => simp [bounds] at h
            | some span =>
              simp only [bounds, Except.mapError, Bind.bind, Except.bind] at h
              cases parsed : Page.readChunk checked.limits.framing checked.snapshot.bytes span with
              | error err => simp [parsed] at h
              | ok frames =>
                simp only [parsed] at h
                obtain rfl := Except.ok.inj h
                exact ⟨⟨groupRead, columns, associated.1, associated.2, codec, indexAbsent,
                  bounds, parsed, (Page.readChunk_chain parsed).2.2⟩, dictionaryAbsent⟩
    · contradiction

public theorem frameGroupFor_wire {container : Container} {checked : Checked container} {codec : Int} {index : Nat} {framed : FramedGroup}
    (h : checked.frameGroupFor codec index = .ok framed) : FramedGroupWire checked index framed codec := by
  obtain ⟨origin, absent⟩ := frameGroupWith_wire (allowDictionary := false) h
  exact ⟨origin.group, origin.chunk, origin.path, origin.physical, origin.codec, absent rfl,
    origin.indexPageOffset, origin.span, origin.frames, origin.chain⟩

public theorem frameGroup_wire {container : Container} {checked : Checked container} {index : Nat} {framed : FramedGroup}
    (h : checked.frameGroup index = .ok framed) : FramedGroupWire checked index framed :=
  frameGroupFor_wire h

public theorem readGroup_wire {checked : Checked} {index : Nat} {slots : List ListPage.Row}
    (h : checked.readGroup index = .ok slots) : GroupWire checked index slots := by
  unfold Checked.readGroup at h
  cases selected : checked.frameGroup index with
  | error e => simp [selected, Bind.bind, Except.bind] at h
  | ok framed =>
    simp only [selected, Bind.bind, Except.bind] at h
    split at h
    · rename_i frame singleton
      split at h
      · rename_i info data
        split at h
        · contradiction
        · rename_i slotCount
          push Not at slotCount
          split at h
          · contradiction
          · cases sliced : checked.snapshot.bytes.slice? frame.payload.start
                (some frame.payload.stop) with
            | none => simp [sliced] at h
            | some body =>
              simp only [sliced, Except.mapError] at h
              cases decoded :
                  ListPage.decodeV1 checked.limits.page framed.chunk.metadata.codec frame.value
                    framed.group.numRows.toNat body with
              | error err => simp [decoded] at h
              | ok value =>
                have same : value = slots := by simpa [decoded] using h
                subst value
                have original := frameGroup_wire selected
                have page := ListPage.decodeV1_wire decoded
                obtain ⟨other, sameKind, _, _, _, wire⟩ := page.page
                rw [data] at sameKind
                cases sameKind
                refine ⟨framed.group, framed.chunk, framed.span, frame, body, info,
                  original.group, original.chunk, original.path, original.physical, original.codec,
                  original.dictionaryOffset, original.indexPageOffset, original.span, ?_, ?_,
                  sliced, data, slotCount, page, wire, wire.rowCount⟩
                · simpa only [singleton] using original.frames
                · simpa only [singleton] using original.chain
      · contradiction
    · contradiction

public theorem schema_exact (checked : Checked) :
    (schema checked).width = 1 ∧
      ∀ index : Fin (schema checked).width,
        (schema checked).kind index = (checked.shape.outer.name, .nullableListOfNullableInt32) := by
  simp [schema]

public theorem batch_slots (checked : Checked) (slots : List ListPage.Row)
    (field : Fin (schema checked).width) :
    (AlignedColumns.ofRows (rows checked slots)).rowCount = slots.length ∧
      (AlignedColumns.ofRows (rows checked slots)).values field = slots := by
  constructor
  · exact List.length_map _
  · induction slots with
    | nil => rfl
    | cons head tail ih =>
      change head :: (AlignedColumns.ofRows (rows checked tail)).values field = head :: tail
      rw [ih]

public theorem rowsAt_error_iff {checked : Checked} {index : Nat} {cause : ReadError} :
    rowsAt checked index = .error (.groupFailure index cause) ↔
      checked.readGroup index = .error cause := by
  cases h : checked.readGroup index <;> simp [rowsAt, h, Except.map, Except.mapError]

public theorem readAll_open_error {limits : ListFile.Limits} {source : Bytes} {cause : OpenError}
    (failed : openFile limits source = .error cause) :
    readAll limits source = .error (.openFailure cause) := by
  simp [readAll, openSource, failed, Except.map, Except.mapError, Reader.readAll]

public theorem readAll_reference {limits : ListFile.Limits} {source : Bytes} {checked : Checked}
    (opened : openFile limits source = .ok checked) :
    let reference := Reader.denoteGroups (rowsAt checked) (List.range checked.snapshot.groupCount)
    readAll limits source = .ok ⟨schema checked,
      ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩ := by
  have admitted : openSource limits source = .ok ⟨schema checked, groupSource checked⟩ := by
    simp [openSource, opened, Except.mapError, Except.map]
  unfold readAll
  rw [admitted, Reader.readAll_opened]
  rfl

private theorem denote_prefix {checked : Checked} {before : List Nat}
    {groups : List (List ListPage.Row)}
    (earlier : before.mapM checked.readGroup = .ok groups) (rest : List Nat) :
    Reader.denoteGroups (rowsAt checked) (before ++ rest) =
      let tail := Reader.denoteGroups (rowsAt checked) rest
      (groups.map (rows checked) ++ tail.1, tail.2) := by
  induction before generalizing groups with
  | nil =>
    simp [Pure.pure, Except.pure] at earlier
    subst groups
    simp
  | cons first before ih =>
    cases read : checked.readGroup first with
    | error e => simp [List.mapM_cons, read, Bind.bind, Except.bind] at earlier
    | ok slots =>
      cases tail : before.mapM checked.readGroup with
      | error e => simp [List.mapM_cons, read, tail, Bind.bind, Except.bind] at earlier
      | ok remaining =>
        simp [List.mapM_cons, read, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] at earlier
        subst groups
        simp [Reader.denoteGroups, rowsAt, read, Except.map, Except.mapError, ih tail]

public theorem readAll_success {limits : ListFile.Limits} {source : Bytes} {checked : Checked}
    {groups : List (List ListPage.Row)}
    (opened : openFile limits source = .ok checked)
    (decoded : (List.range checked.snapshot.groupCount).mapM checked.readGroup = .ok groups) :
    readAll limits source = .ok ⟨schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows checked), .eos⟩⟩ := by
  have all := denote_prefix decoded []
  simp only [List.append_nil, Reader.denoteGroups] at all
  rw [readAll_reference opened, all, List.map_map]

public theorem readAll_first_error {limits : ListFile.Limits} {source : Bytes} {checked : Checked}
    {before after : List Nat} {index : Nat} {groups : List (List ListPage.Row)} {cause : ReadError}
    (opened : openFile limits source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM checked.readGroup = .ok groups)
    (failed : checked.readGroup index = .error cause) :
    readAll limits source = .ok ⟨schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows checked), .readError (.groupFailure index cause)⟩⟩ := by
  have errorAt := rowsAt_error_iff.mpr failed
  rw [readAll_reference opened, split, denote_prefix earlier]
  simp [Reader.denoteGroups, errorAt, List.map_map]

end Silmaril.Proofs.Formats.Parquet.ListFile
