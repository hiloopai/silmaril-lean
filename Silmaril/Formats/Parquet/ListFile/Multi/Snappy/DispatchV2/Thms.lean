module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2.Correctness

public section

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2

open Silmaril.Relational
open ListPage (Row)

/-- A successful framing selects one reader. Its result is returned directly. -/
theorem readGroup_selected {limits : DictionaryV1.Limits} {checked : ListFile.Checked}
    {ordinal expanded : Nat} {framed : ListFile.FramedGroup}
    (h : checked.frameGroupWith 1 true ordinal = .ok framed) :
    readGroup limits checked ordinal expanded = readFramedGroup limits checked framed expanded := by
  simp [readGroup, h, Except.mapError, Bind.bind, Except.bind]

/-- The selected profile's original wire witnesses and budget remain valid. -/
theorem readFramedGroup_wire {limits : DictionaryV1.Limits} {checked : ListFile.Checked}
    {ordinal expanded left : Nat} {framed : ListFile.FramedGroup} {rows : List Row}
    (origin : ListFile.ChunkFrameWire checked ordinal framed 1)
    (h : readFramedGroup limits checked framed expanded = .ok (rows, left)) :
    ProfileWire limits checked ordinal rows (expanded - left) (classify framed.frames) ∧ left ≤ expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2.readFramedGroup_wire origin h

/-- Group admission ties the selected profile to the original same-source frame list. -/
theorem readGroup_wire {limits : DictionaryV1.Limits} {checked : ListFile.Checked}
    {ordinal expanded left : Nat} {rows : List Row}
    (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) ∧ left ≤ expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2.readGroup_wire h

/-- The first indexed source failure retains earlier groups before IPC publication. -/
theorem convert_first_error {limits : DictionaryV1.Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : ListFile.openFile limits.snappy.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : Snappy.readGroupsWith SourceError.groupFailure
      (readGroup limits) checked limits.snappy.maxExpandedBytes before = (groups, .ok left))
    (failed : readGroup limits checked ordinal left = .error cause) :
    (convert limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2.convert_first_error opened split earlier failed

/-- The original ordered group witnesses compose with exact native V5 LIST readback. -/
theorem convert_readback {limits : DictionaryV1.Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2.convert_readback h

/-- A selected plain failure keeps its original cause. -/
theorem readGroup_plain_error {limits : DictionaryV1.Limits} {checked : ListFile.Checked}
    {ordinal expanded : Nat} {framed : ListFile.FramedGroup} {cause : Snappy.GroupError}
    (framing : checked.frameGroupWith 1 true ordinal = .ok framed)
    (selected : classify framed.frames = .plain)
    (absent : framed.chunk.metadata.dictionaryPageOffset = none)
    (failed : Snappy.readFramedGroupFor .v2 limits.snappy checked framed expanded = .error cause) :
    readGroup limits checked ordinal expanded = .error (.plain cause) := by
  simp [readGroup_selected framing, readFramedGroup, selected, absent, failed, Except.mapError]

/-- A selected dictionary failure keeps its original cause. -/
theorem readGroup_dictionary_error {limits : DictionaryV1.Limits} {checked : ListFile.Checked}
    {ordinal expanded : Nat} {framed : ListFile.FramedGroup} {cause : DictionaryV1.GroupError}
    (framing : checked.frameGroupWith 1 true ordinal = .ok framed)
    (selected : classify framed.frames = .dictionary)
    (failed : readDictionaryGroup limits (dictionaryWalk limits) checked framed expanded = .error cause) :
    readGroup limits checked ordinal expanded = .error (.dictionary cause) := by
  simp [readGroup_selected framing, readFramedGroup, selected, failed, Except.mapError]

/-- A selected fallback failure keeps its original cause. -/
theorem readGroup_fallback_error {limits : DictionaryV1.Limits} {checked : ListFile.Checked}
    {ordinal expanded : Nat} {framed : ListFile.FramedGroup} {cause : DictionaryV1.GroupError}
    (framing : checked.frameGroupWith 1 true ordinal = .ok framed)
    (selected : classify framed.frames = .fallback)
    (failed : readDictionaryGroup limits (DictionaryFallbackV2.walk limits) checked framed expanded = .error cause) :
    readGroup limits checked ordinal expanded = .error (.fallback cause) := by
  simp [readGroup_selected framing, readFramedGroup, selected, failed, Except.mapError]

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2
