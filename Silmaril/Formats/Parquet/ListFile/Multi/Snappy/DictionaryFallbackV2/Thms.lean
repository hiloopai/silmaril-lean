module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.Correctness

public section

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2

open Silmaril.Relational
open ListPage (Event State Row)
open DictionaryV1 (readFramesUsing)
open Snappy (Budget expandedSize)

/-- The original frame order splits into nonempty dictionary and PLAIN runs, with exact ordered events and remaining budgets. -/
theorem readFrames_wire {limits : DictionaryV1.Limits} {checked : ListFile.Checked} {entries : Array Int32}
    {ordinal : Nat} {budget left : Budget} {state next : State} {frames : List Page.Frame}
    (h : readFrames limits checked entries ordinal budget state frames = .ok (left, next)) :
    ∃ pages, FramesWire limits checked entries frames pages ∧
      pages.flatten.length + left.slots = budget.slots ∧
      expandedSize frames + left.expanded = budget.expanded ∧ state.feed pages.flatten = .ok next :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.readFrames_wire h

/-- A successful group has the original checked chunk and exact nested rows. -/
theorem readGroup_wire {limits : DictionaryV1.Limits} {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) ∧ left ≤ expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.readGroup_wire h

/-- Both phases contribute the exact original V2 page counts to the selected group. -/
theorem readGroup_counts {limits : DictionaryV1.Limits} {checked : ListFile.Checked}
    {ordinal expanded left : Nat} {rows : List Row}
    (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    ∃ chunk infos, DictionaryV1.ChunkWire checked ordinal chunk ∧
      List.Forall₂ (fun (frame : Page.Frame) (info : Page.DataV2) => frame.value.kind = .dataV2 info)
        (chunk.firstData :: chunk.rest) infos ∧
      (infos.map (·.numValues)).sum = chunk.framed.chunk.metadata.numValues.toNat ∧
      (infos.map (·.numRows)).sum = chunk.framed.group.numRows.toNat ∧
      (infos.map (·.numNulls)).sum = Snappy.pageNulls (rows.flatMap ListPage.rowEvents) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.readGroup_counts h

/-- A dictionary-prefix failure survives every suffix outcome. -/
theorem readFrames_prefix_error {limits : DictionaryV1.Limits} {checked : ListFile.Checked} {entries : Array Int32}
    {ordinal : Nat} {budget : Budget} {state : State} {frames : List Page.Frame} {cause : DictionaryV1.GroupError}
    (nonempty : frames.takeWhile isDictionaryData ≠ [])
    (failed : readFramesUsing (DictionaryV2.readFrame limits checked entries) ordinal budget state
      (frames.takeWhile isDictionaryData) = .error cause) :
    readFrames limits checked entries ordinal budget state frames = .error cause :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.readFrames_prefix_error nonempty failed

/-- After two successful prefixes, the first PLAIN-suffix failure retains its original frame coordinates. -/
theorem readFrames_suffix_error {limits : DictionaryV1.Limits} {checked : ListFile.Checked} {entries : Array Int32}
    {ordinal : Nat} {budget left : Budget} {state next : State}
    {frames earlier rest : List Page.Frame} {frame : Page.Frame} {cause : DictionaryV1.FrameError}
    (nonempty : frames.takeWhile isDictionaryData ≠ [])
    (decodedPrefix : readFramesUsing (DictionaryV2.readFrame limits checked entries) ordinal budget state
      (frames.takeWhile isDictionaryData) = .ok (left, next))
    (split : frames.dropWhile isDictionaryData = earlier ++ frame :: rest)
    {remaining : Budget} {advanced : State}
    (before : readFramesUsing (readPlainFrame limits checked) (ordinal + (frames.takeWhile isDictionaryData).length)
      left next earlier = .ok (remaining, advanced))
    (failed : readPlainFrame limits checked remaining frame = .error cause) :
    readFrames limits checked entries ordinal budget state frames =
      .error (.frame (ordinal + (frames.takeWhile isDictionaryData).length + earlier.length) frame.header.start cause) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.readFrames_suffix_error nonempty decodedPrefix split before failed

/-- An indexed data frame in the PLAIN suffix is refused. -/
theorem readPlainFrame_reentry {limits : DictionaryV1.Limits} {checked : ListFile.Checked}
    {budget : Budget} {frame : Page.Frame} (kind : isDictionaryData frame = true) :
    readPlainFrame limits checked budget frame = .error .dictionaryReentry :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.readPlainFrame_reentry kind

/-- The first indexed source failure retains completed groups and prevents IPC publication. -/
theorem convert_first_error {limits : DictionaryV1.Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : DictionaryV1.GroupError}
    (opened : ListFile.openFile limits.snappy.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : Snappy.readGroupsWith DictionaryV1.SourceError.groupFailure
      (readGroup limits) checked limits.snappy.maxExpandedBytes before = (groups, .ok left))
    (failed : readGroup limits checked ordinal left = .error cause) :
    (convert limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.convert_first_error opened split earlier failed

/-- Successful V5 IPC preserves the signed ordered nullable LIST rows through exact EOS. -/
theorem convert_readback {limits : DictionaryV1.Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.convert_readback h

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2
