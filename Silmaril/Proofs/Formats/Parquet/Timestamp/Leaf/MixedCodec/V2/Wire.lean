module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2

open Silmaril.Formats Parquet Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2

theorem selectedCodec_exact {encoding : Leaf.ChunkEncoding} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {chunk : Leaf.Chunk}
    (selected : selectChunkWith encoding leafLimits bound index = .ok chunk) :
    selectedCodec bound index = .ok chunk.column.metadata.codec := by
  obtain ⟨group, column, _⟩ := Leaf.selectChunkWith_sound selected
  simp [selectedCodec, group, column, pure, Except.pure]

theorem readGroup_selection_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {cause : Leaf.Error} (failed : selectedCodec bound index = .error cause) :
    readGroup limits leafLimits bound index = .error (.selection cause) := by
  simp [readGroup, failed, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_unsupported_codec {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {codec : Int} (selected : selectedCodec bound index = .ok codec)
    (gzip : codec ≠ Payload.Codec.gzip.id) (zstd : codec ≠ Payload.Codec.zstd.id) :
    readGroup limits leafLimits bound index = .error (.unsupportedCodec codec) := by
  simp [readGroup, readGroupForCodec, selected, gzip, zstd, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_gzip_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (selected : selectedCodec bound index = .ok Payload.Codec.gzip.id) :
    readGroup limits leafLimits bound index =
      (Leaf.Gzip.Dispatch.V2.readGroup limits.gzip leafLimits bound index).mapError .gzip := by
  simp [readGroup, readGroupForCodec, selected, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_zstd_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (selected : selectedCodec bound index = .ok Payload.Codec.zstd.id) :
    readGroup limits leafLimits bound index =
      (Leaf.Zstd.Dispatch.V2.readGroup limits.zstd leafLimits bound index).mapError .zstd := by
  simp [readGroup, readGroupForCodec, selected, Payload.Codec.id, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    GroupWire limits leafLimits bound index slots := by
  cases selected : selectedCodec bound index with
  | error cause =>
    rw [readGroup_selection_error selected] at read
    contradiction
  | ok codec =>
    by_cases gzip : codec = Payload.Codec.gzip.id
    · subst codec
      rw [readGroup_gzip_agrees selected] at read
      cases branch : Leaf.Gzip.Dispatch.V2.readGroup limits.gzip leafLimits bound index with
      | error cause => simp [branch, Except.mapError] at read
      | ok decoded =>
        simp [branch, Except.mapError] at read
        subst slots
        exact .gzip selected (Leaf.Gzip.Dispatch.V2.readGroup_wire branch)
    · by_cases zstd : codec = Payload.Codec.zstd.id
      · subst codec
        rw [readGroup_zstd_agrees selected] at read
        cases branch : Leaf.Zstd.Dispatch.V2.readGroup limits.zstd leafLimits bound index with
        | error cause => simp [branch, Except.mapError] at read
        | ok decoded =>
          simp [branch, Except.mapError] at read
          subst slots
          exact .zstd selected (Leaf.Zstd.Dispatch.V2.readGroup_wire branch)
      · rw [readGroup_unsupported_codec selected gzip zstd] at read
        contradiction

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2
