module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.Wire
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.Events

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- The original data headers determine the common version and the presence of PLAIN. -/
theorem classifyFrames_ok {framed : Dictionary.FramedChunk} {profile : Profile}
    (chosen : classifyFrames framed = .ok profile) :
    profile.version = firstVersion framed ∧ profile.fallback = hasPlain profile.version framed ∧
      ∀ pair ∈ framed.data.zipIdx 1, hasOtherVersion profile.version pair.1 = false :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.classifyFrames_ok chosen

/-- A mixed-version refusal identifies the earliest contrary data frame in original order. -/
theorem classifyFrames_mixed {framed : Dictionary.FramedChunk} {page offset : Nat}
    (rejected : classifyFrames framed = .error (.mixedVersions page offset)) :
    ∃ before frame after, framed.data.zipIdx 1 = before ++ (frame, page) :: after ∧
      frame.header.start = offset ∧ hasOtherVersion (firstVersion framed) frame = true ∧
      ∀ pair ∈ before, hasOtherVersion (firstVersion framed) pair.1 = false :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.classifyFrames_mixed rejected

/-- The original selected footer chooses the codec and its dictionary-backed route. -/
theorem readGroup_dictionary {codec : Codec} {limits : ScalarAndDictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} (route : Leaf.ScalarAndDictionary.route bound index = .ok codec.branch) :
    readGroup limits leafLimits bound index =
      readDictionary codec limits leafLimits bound index :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.readGroup_dictionary route

/-- The scalar, codec-0 dictionary and Zstandard dictionary routes retain their complete existing results. -/
theorem readGroup_existing {branch : Leaf.ScalarAndDictionary.Branch} {limits : ScalarAndDictionary.Limits}
    {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (route : Leaf.ScalarAndDictionary.route bound index = .ok branch)
    (snappy : branch ≠ .dictionary .snappy) (gzip : branch ≠ .dictionary .gzip) :
    readGroup limits leafLimits bound index =
      (Leaf.ScalarAndDictionary.readGroup limits leafLimits bound index).mapError .existing :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.readGroup_existing route snappy gzip

/-- After framing and classification, the branch preserves the full standalone result, including typed errors. -/
theorem readDictionary_agrees {codec : Codec} {limits : ScalarAndDictionary.Limits}
    {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {framed : Dictionary.FramedChunk}
    {profile : Profile} (framedOk : frameGroup codec limits leafLimits bound index = .ok framed)
    (chosen : classifyFrames framed = .ok profile) :
    readDictionary codec limits leafLimits bound index =
      (standalone codec profile limits leafLimits bound index).mapError (codec.error profile.version) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.readDictionary_agrees framedOk chosen

/-- A classified V2 chunk preserves the previous strict V2 result and error. -/
theorem readDictionary_v2_agrees {codec : Codec} {limits : ScalarAndDictionary.Limits}
    {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {framed : Dictionary.FramedChunk}
    {profile : Profile} (framedOk : frameGroup codec limits leafLimits bound index = .ok framed)
    (chosen : classifyFrames framed = .ok profile) (version : profile.version = .v2) :
    readDictionary codec limits leafLimits bound index =
      (Leaf.ScalarAndDictionary.readSelected limits leafLimits bound index codec.branch).mapError .existing :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.readDictionary_v2_agrees framedOk chosen version

/-- Successful dictionary reads retain the original frame chain, integrity, plans and exact nullable signed slots. -/
theorem readDictionary_wire {codec : Codec} {limits : ScalarAndDictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readDictionary codec limits leafLimits bound index = .ok slots) :
    DictionaryWire codec limits leafLimits bound index slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.readDictionary_wire read

/-- Each completed original group supplies the selected branch witness. -/
theorem readGroup_wire {limits : ScalarAndDictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    GroupWire limits leafLimits bound index slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.readGroup_wire read

/-- A source error retains precisely the complete earlier groups. -/
theorem trace_first_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    trace limits leafLimits bound =
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (.groupFailure index cause)⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.trace_first_error split earlier failed

/-- A typed original source failure precedes writer admission. -/
theorem convert_first_error {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : GroupError}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits output input ordinal = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.convert_first_error opened split earlier failed

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
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.convert_readback written

end Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1
