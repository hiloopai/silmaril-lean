module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.Wire
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.Events

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- Every admitted V1 page retains its original tag, level encodings and sizes. -/
theorem planData_wire {codec : Codec} {fallback : Bool} {bound : Bound} {frame : Parquet.Page.Frame}
    {page : Dictionary.DataPage} (read : planData codec fallback bound frame = .ok page) :
    PlanWire codec fallback bound frame page :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.planData_wire read

/-- The same stored slice supplies the CRC, prepared mask, values and ordered references. -/
theorem decodePage_wire {codec : Codec} {fallback : Bool} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {frame : Parquet.Page.Frame} {entries : Array Int64} {page : Dictionary.DataPage}
    {ordinal : Nat} {slots : List (Option Int64)}
    (planned : PlanWire codec fallback bound frame page)
    (read : decodePage codec limits leafLimits bound entries page ordinal = .ok slots) :
    PageWire codec limits leafLimits bound entries page slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.decodePage_wire planned read

/-- The original indexed checksum error precedes the whole-body decoder. -/
theorem decodePage_checksum_error {codec : Codec} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {entries : Array Int64} {page : Dictionary.DataPage} {ordinal : Nat}
    {cause : Parquet.Page.Checksum.Error}
    (failed : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame =
      .error cause) :
    decodePage codec limits leafLimits bound entries page ordinal =
      .error (.checksum ordinal page.frame.header.start cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.decodePage_checksum_error failed

/-- A complete V1 group retains the original selection, checked frame chain and exact signed nullable slots. -/
theorem readV1_wire {codec : Codec} {fallback : Bool} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {framed : Dictionary.FramedChunk} {slots : Slots bound}
    (framedOk : frameGroup codec limits leafLimits bound index = .ok framed)
    (read : readV1 codec fallback limits leafLimits bound framed = .ok slots) :
    DictionaryWire codec fallback limits leafLimits bound index framed slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.readV1_wire framedOk read

/-- The original total declared Zstandard expansion is bounded before dictionary or data decoding. -/
theorem readV1_zstd_expansion_error {fallback : Bool} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {framed : Dictionary.FramedChunk}
    (excess : (zstdLimits limits).maxExpandedChunkBytes < (framed.frames.map (·.value.uncompressedSize)).sum) :
    readV1 .zstd fallback limits leafLimits bound framed = .error .expandedChunkLimit :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.readV1_zstd_expansion_error excess

/-- The first failed data page retains its original indexed error. -/
theorem readV1_first_page_error {codec : Codec} {fallback : Bool} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {framed : Dictionary.FramedChunk} {checked : Dictionary.CheckedChunk}
    {before after : List (Dictionary.DataPage × Nat)} {page : Dictionary.DataPage} {ordinal : Nat}
    {outputs : List (List (Option Int64))} {cause : V1Error}
    (admitted : checkFramed codec fallback limits leafLimits bound framed = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun item => decodePage codec limits leafLimits bound checked.entries.toArray
      item.1 item.2) = .ok outputs)
    (failed : decodePage codec limits leafLimits bound checked.entries.toArray page ordinal = .error cause) :
    readV1 codec fallback limits leafLimits bound framed = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.readV1_first_page_error admitted split earlier failed

/-- A classified V1 chunk calls the selected V1 route on the retained frames. -/
theorem readDictionary_v1 {codec : Codec} {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {framed : Dictionary.FramedChunk} {fallback : Bool}
    (framedOk : frameGroup codec limits leafLimits bound index = .ok framed)
    (chosen : Leaf.ScalarAndDictionary.WithV1.classifyFrames framed = .ok ⟨.v1, fallback⟩) :
    readDictionary codec limits leafLimits bound index =
      (readV1 codec fallback limits leafLimits bound framed).mapError (.v1 codec) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.readDictionary_v1 framedOk chosen

/-- A classified V2 chunk preserves the complete prior result, including typed errors. -/
theorem readDictionary_v2_agrees {codec : Codec} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {framed : Dictionary.FramedChunk}
    {profile : Leaf.ScalarAndDictionary.WithV1.Profile}
    (framedOk : frameGroup codec limits leafLimits bound index = .ok framed)
    (chosen : Leaf.ScalarAndDictionary.WithV1.classifyFrames framed = .ok profile)
    (version : profile.version = .v2) :
    readDictionary codec limits leafLimits bound index =
      (Leaf.ScalarAndDictionary.readSelected limits leafLimits bound index codec.branch).mapError
        (.existing ∘ .existing) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.readDictionary_v2_agrees framedOk chosen version

/-- The original selected footer chooses the codec and dictionary route. -/
theorem readGroup_dictionary {codec : Codec} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} (routed : Leaf.ScalarAndDictionary.route bound index = .ok codec.branch) :
    readGroup limits leafLimits bound index = readDictionary codec limits leafLimits bound index :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.readGroup_dictionary routed

/-- The scalar, Snappy and GZIP routes keep their existing results. -/
theorem readGroup_existing {branch : Leaf.ScalarAndDictionary.Branch} {limits : Limits}
    {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (routed : Leaf.ScalarAndDictionary.route bound index = .ok branch)
    (uncompressed : branch ≠ .dictionary .uncompressed) (zstd : branch ≠ .dictionary .zstd) :
    readGroup limits leafLimits bound index =
      (Leaf.ScalarAndDictionary.WithV1.readGroup limits leafLimits bound index).mapError .existing :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.readGroup_existing routed uncompressed zstd

/-- Each completed original group carries its selected wire witness. -/
theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    GroupWire limits leafLimits bound index slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.readGroup_wire read

/-- A failed source group preserves precisely the earlier complete Events. -/
theorem trace_first_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    trace limits leafLimits bound =
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (.groupFailure index cause)⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.trace_first_error split earlier failed

/-- The first indexed source failure precedes IPC writer admission. -/
theorem convert_first_error {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : GroupError}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits output input ordinal = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.convert_first_error opened split earlier failed

/-- Native IPC through EOS preserves the original descriptor and ordered signed nullable batches. -/
theorem convert_readback {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert limits inputLimits output input ordinal = .ok wire) :
    ∃ bound groups, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound ∧
      List.Forall₂ (GroupWire limits inputLimits.leaf bound) (List.range bound.snapshot.groupCount) groups ∧
      trace limits inputLimits.leaf bound =
        ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .eos⟩ ∧
      ∃ result, Arrow.TimestampStream.read output.ipc wire = .ok result ∧
        result.binding = Leaf.Events.ToIpc.selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          groups.map (List.map (Option.map Ticks.ticks)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.convert_readback written

end Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs
