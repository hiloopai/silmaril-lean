module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.Wire
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.Events

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- The decoded codec is exactly the original supported codec ID. -/
theorem codec_ok_iff {id : Int} {codec : Codec} :
    Codec.ofId id = some codec ↔ id = codec.id :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.codec_ok_iff

/-- Footer classification is exact for the original codec and dictionary offset. -/
theorem classify_ok_iff {metadata : Footer.ColumnMetadata} {branch : Branch} :
    classify metadata = .ok branch ↔ branch.Matches metadata :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.classify_ok_iff

/-- Selection uses the retained footer group and serialized leaf column ordinals. -/
theorem selectedColumn_ok_iff {bound : Bound} {index : Nat} {column : Footer.ColumnChunk} :
    selectedColumn bound index = .ok column ↔
      ∃ group, bound.snapshot.groupAt index = some group ∧
        group.columns[bound.ordinal - 1]? = some column :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.selectedColumn_ok_iff

/-- A route is admitted precisely by the original selected footer column. -/
theorem route_ok_iff {bound : Bound} {index : Nat} {branch : Branch} :
    route bound index = .ok branch ↔
      ∃ group column, bound.snapshot.groupAt index = some group ∧
        group.columns[bound.ordinal - 1]? = some column ∧ branch.Matches column.metadata :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.route_ok_iff

/-- The dictionary-free route preserves the entire ScalarDispatch result. -/
theorem readGroup_scalar_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {codec : Codec} (chosen : route bound index = .ok (.scalar codec)) :
    readGroup limits leafLimits bound index =
      (Leaf.ScalarDispatch.readGroup limits.scalar leafLimits bound index).mapError .scalar :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.readGroup_scalar_agrees chosen

/-- The codec-0 dictionary route preserves the entire strict dispatcher result. -/
theorem readGroup_uncompressed_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} (chosen : route bound index = .ok (.dictionary .uncompressed)) :
    readGroup limits leafLimits bound index =
      (Leaf.Uncompressed.Dispatch.V2.readGroup limits.dictionary.uncompressed leafLimits bound index).mapError
        .uncompressedDictionary :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.readGroup_uncompressed_agrees chosen

/-- The Snappy dictionary route preserves the entire strict dispatcher result. -/
theorem readGroup_snappy_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} (chosen : route bound index = .ok (.dictionary .snappy)) :
    readGroup limits leafLimits bound index =
      (Leaf.Snappy.Dispatch.V2.readGroup limits.dictionary.threeCodec.snappy leafLimits bound index).mapError
        .snappyDictionary :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.readGroup_snappy_agrees chosen

/-- The GZIP dictionary route preserves the entire strict dispatcher result. -/
theorem readGroup_gzip_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} (chosen : route bound index = .ok (.dictionary .gzip)) :
    readGroup limits leafLimits bound index =
      (Leaf.Gzip.Dispatch.V2.readGroup limits.dictionary.threeCodec.twoCodec.gzip leafLimits bound index).mapError
        .gzipDictionary :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.readGroup_gzip_agrees chosen

/-- The Zstandard dictionary route preserves the entire strict dispatcher result. -/
theorem readGroup_zstd_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} (chosen : route bound index = .ok (.dictionary .zstd)) :
    readGroup limits leafLimits bound index =
      (Leaf.Zstd.Dispatch.V2.readGroup limits.dictionary.threeCodec.twoCodec.zstd leafLimits bound index).mapError
        .zstdDictionary :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.readGroup_zstd_agrees chosen

/-- Every completed group has its selected branch witness on the original source. -/
theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    GroupWire limits leafLimits bound index slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.readGroup_wire read

/-- The first failed source group retains exactly the earlier complete batches. -/
theorem trace_first_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    trace limits leafLimits bound =
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (.groupFailure index cause)⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.trace_first_error split earlier failed

/-- The original indexed source failure precedes native IPC writer admission. -/
theorem convert_first_error {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : GroupError}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits output input ordinal = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.convert_first_error opened split earlier failed

/-- The original descriptor and exact ordered ticks read back through native IPC EOS. -/
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
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.convert_readback written

/-- The dictionary-bearing footer policy is exactly modern references and optional PLAIN and RLE. -/
theorem dictionaryEncodings_ok_iff {declared : List Int} :
    dictionaryEncodings declared = true ↔
      8 ∈ declared ∧ (∀ tag ∈ declared, tag = 0 ∨ tag = 3 ∨ tag = 8) := by
  simp [dictionaryEncodings, List.all_eq_true, or_assoc]

/-- A codec outside the route's domain is an unsupported profile at classification. -/
theorem classify_codec_error {metadata : Footer.ColumnMetadata}
    (unsupported : Codec.ofId metadata.codec = none) :
    classify metadata = .error (.codec metadata.codec) := by
  simp [classify, unsupported]

/-- A dictionary encoding declaration outside the strict V2 domain fails at classification. -/
theorem classify_dictionary_error {metadata : Footer.ColumnMetadata} {codec : Codec} {offset : Int}
    (supportedCodec : Codec.ofId metadata.codec = some codec)
    (dictionary : metadata.dictionaryPageOffset = some offset)
    (unsupported : dictionaryEncodings metadata.encodings = false) :
    classify metadata = .error (.dictionaryEncodings metadata.encodings) := by
  simp [classify, supportedCodec, dictionary, unsupported]

/-- A failed route returns its original typed error before any branch is called. -/
theorem readGroup_route_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {cause : GroupError} (failed : route bound index = .error cause) :
    readGroup limits leafLimits bound index = .error cause := by
  simp [readGroup, failed, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary
