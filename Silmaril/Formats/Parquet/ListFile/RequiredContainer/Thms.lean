module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.Correctness

public section

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer

open ListPage (Event Row)
open Silmaril.Relational

/-- The checked header uses the original required parent and optional INT32 child. -/
theorem openFile_repetition {limits : ListFile.Limits} {source : Bytes} {checked : Checked}
    (h : openFile limits source = .ok checked) :
    checked.shape.outer.repetition = some .required ∧ checked.shape.element.repetition = some .optional :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.openFile_repetition h

/-- Required definition zero represents an empty present container. -/
theorem readEvent_empty : readEvent (0, 0, none) = .ok .emptyList := rfl

/-- An empty-list marker cannot continue a preceding row. -/
theorem readEvent_empty_continuation : readEvent (1, 0, none) = .error .levelPair := rfl

/-- Definitions above the required-container maximum fail before PLAIN decode. -/
theorem decodeSections_bad_definition {limits : ListPage.Limits} {slots : Nat}
    {repetition definition scalars : Bytes} {reps defs : List Nat}
    (rep : Hybrid.decode 1 slots limits.levels repetition = .ok reps)
    (defn : Hybrid.decode 2 slots limits.levels definition = .ok defs)
    (bad : defs.any (fun level => 2 < level) = true) :
    decodeSections limits slots repetition definition scalars = .error .levelPair := by
  simp [decodeSections, decodeSectionsUsing, rep, defn, bad, Except.mapError, Bind.bind, Except.bind]
  rfl

/-- A body refusal keeps the original frame-zero ordinal and absolute offset. -/
theorem readGroup_frame_error {checked : Checked} {ordinal : Nat}
    {framed : FramedGroup} {frame : Page.Frame} {cause : ListFile.ReadError}
    (selected : checked.frameGroup ordinal = .ok framed) (single : framed.frames = [frame])
    (failed : readFrame checked framed frame = .error cause) :
    readGroup checked ordinal = .error (.frame 0 frame.header.start cause) := by
  simp [readGroup, readGroupUsing, readGroupWith, selected, single, failed, Except.mapError, Bind.bind, Except.bind]

/-- Every decoded event has its exact required-container raw slot triple. -/
theorem readEvent_wire {entry : Triple} {event : Event}
    (h : readEvent entry = .ok event) : eventWire event = some entry :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.readEvent_wire h

/-- Select exactly the physical slots from the original level streams using the supplied value reader. -/
theorem decodeSectionsUsing_wire {ε : Type} {pageError : ListPage.Error → ε}
    {readValues : Nat → Bytes → Except ε (List Int32)} {limits : ListPage.Limits} {slots : Nat}
    {repetition definition scalars : Bytes} {events : List Event}
    (h : decodeSectionsUsing pageError readValues limits slots repetition definition scalars = .ok events) :
    SectionsWireUsing readValues slots repetition definition scalars events :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.decodeSectionsUsing_wire h

/-- The raw level streams and exact scalar suffix preserve ordered slots. -/
theorem decodeSections_wire {limits : ListPage.Limits} {slots : Nat}
    {repetition definition scalars : Bytes} {events : List Event}
    (h : decodeSections limits slots repetition definition scalars = .ok events) :
    SectionsWire slots repetition definition scalars events :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.decodeSections_wire h

/-- Required-container level events reconstruct only present parent lists. -/
theorem reconstruct_present {slots : Nat} {repetition definition scalars : Bytes}
    {events : List Event} {rows : List Row}
    (sections : SectionsWire slots repetition definition scalars events)
    (assembled : ListPage.reconstruct events = .ok rows) :
    ∀ row ∈ rows, row.isSome = true :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.reconstruct_present sections assembled

/-- The original V1 extents are consumed in serialized order. -/
theorem decodeEvents_wire {limits : ListPage.Limits} {slots : Nat} {body : Bytes}
    {events : List Event} (h : decodeEvents limits slots body = .ok events) :
    EventsWire limits slots body events :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.decodeEvents_wire h

/-- Checked parent rows are all present, with the original signed child slots and counts. -/
theorem readFrame_wire {checked : Checked} {framed : ListFile.FramedGroup} {frame : Page.Frame}
    {rows : List Row} (h : readFrame checked framed frame = .ok rows) : FrameWire checked framed frame rows :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.readFrame_wire h

/-- The group uses its original checked chunk and singleton frame. -/
theorem readGroup_wire {checked : Checked} {ordinal : Nat} {rows : List Row}
    (h : readGroup checked ordinal = .ok rows) : GroupWire checked ordinal rows :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.readGroup_wire h

/-- A failed original group retains earlier batches ahead of any writer refusal. -/
theorem convert_first_error {limits : Limits} {source : Bytes} {checked : Checked}
    {before after : List Nat} {ordinal : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : openFile limits.parquet source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : before.mapM (readGroup checked) = .ok groups)
    (failed : readGroup checked ordinal = .error cause) :
    (convert limits source).trace = .ok ⟨schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ rowsOf checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.convert_first_error opened split earlier failed

/-- The original rows and required Arrow field agree through native EOS. -/
theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.convert_readback h

theorem convertUsing_first_error {error : Type} {read : GroupReader error} {limits : Limits} {source : Bytes} {checked : Checked}
    {before after : List Nat} {ordinal : Nat} {groups : List (List Row)} {cause : error}
    (opened : openFile limits.parquet source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : before.mapM (read checked) = .ok groups)
    (failed : read checked ordinal = .error cause) :
    (convertUsing read limits source).trace = .ok ⟨schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ rowsOf checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convertUsing read limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.convertUsing_first_error opened split earlier failed

theorem convertUsing_readback {error : Type} {read : GroupReader error} {witness : GroupWitness}
    (sound : ∀ {checked ordinal rows}, read checked ordinal = .ok rows → witness checked ordinal rows)
    {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convertUsing read limits source).wire = .ok wire) : ReadbackUsing read witness limits source wire :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.convertUsing_readback sound h

end Silmaril.Formats.Parquet.ListFile.RequiredContainer
