module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.Dispatch.V2.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed

open Silmaril.Formats Parquet Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed

theorem readGroup_uncompressed_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (selected : Leaf.MixedCodec.V2.selectedCodec bound index = .ok Payload.Codec.uncompressed.id) :
    readGroup limits leafLimits bound index =
      (Leaf.Uncompressed.Dispatch.V2.readGroup limits.uncompressed leafLimits bound index).mapError .uncompressed := by
  simp [readGroup, selected, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_threeCodec_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (other : Leaf.MixedCodec.V2.selectedCodec bound index ≠ .ok Payload.Codec.uncompressed.id) :
    readGroup limits leafLimits bound index =
      (Leaf.MixedCodec.V2.WithSnappy.readGroup limits.threeCodec leafLimits bound index).mapError .threeCodec := by
  cases selected : Leaf.MixedCodec.V2.selectedCodec bound index with
  | error cause =>
    simp [readGroup, Leaf.MixedCodec.V2.WithSnappy.readGroup, selected, Except.mapError, Bind.bind, Except.bind]
  | ok codec =>
    have different : codec ≠ Payload.Codec.uncompressed.id := by
      intro same
      exact other (same ▸ selected)
    simp [readGroup, Leaf.MixedCodec.V2.WithSnappy.readGroup, selected, different,
      Except.mapError, Bind.bind, Except.bind]

theorem readGroup_snappy_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (selected : Leaf.MixedCodec.V2.selectedCodec bound index = .ok Payload.Codec.snappy.id) :
    readGroup limits leafLimits bound index =
      (Leaf.Snappy.Dispatch.V2.readGroup limits.threeCodec.snappy leafLimits bound index).mapError
        (GroupError.threeCodec ∘ Leaf.MixedCodec.V2.WithSnappy.GroupError.snappy) := by
  rw [readGroup_threeCodec_agrees (by simp [selected, Payload.Codec.id]),
    Leaf.MixedCodec.V2.WithSnappy.readGroup_snappy_agrees selected]
  cases Leaf.Snappy.Dispatch.V2.readGroup limits.threeCodec.snappy leafLimits bound index <;> rfl

theorem readGroup_gzip_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (selected : Leaf.MixedCodec.V2.selectedCodec bound index = .ok Payload.Codec.gzip.id) :
    readGroup limits leafLimits bound index =
      (Leaf.Gzip.Dispatch.V2.readGroup limits.threeCodec.twoCodec.gzip leafLimits bound index).mapError
        (GroupError.threeCodec ∘ Leaf.MixedCodec.V2.WithSnappy.GroupError.twoCodec ∘
          Leaf.MixedCodec.V2.GroupError.gzip) := by
  rw [readGroup_threeCodec_agrees (by simp [selected, Payload.Codec.id]),
    Leaf.MixedCodec.V2.WithSnappy.readGroup_gzip_agrees selected]
  cases Leaf.Gzip.Dispatch.V2.readGroup limits.threeCodec.twoCodec.gzip leafLimits bound index <;> rfl

theorem readGroup_zstd_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (selected : Leaf.MixedCodec.V2.selectedCodec bound index = .ok Payload.Codec.zstd.id) :
    readGroup limits leafLimits bound index =
      (Leaf.Zstd.Dispatch.V2.readGroup limits.threeCodec.twoCodec.zstd leafLimits bound index).mapError
        (GroupError.threeCodec ∘ Leaf.MixedCodec.V2.WithSnappy.GroupError.twoCodec ∘
          Leaf.MixedCodec.V2.GroupError.zstd) := by
  rw [readGroup_threeCodec_agrees (by simp [selected, Payload.Codec.id]),
    Leaf.MixedCodec.V2.WithSnappy.readGroup_zstd_agrees selected]
  cases Leaf.Zstd.Dispatch.V2.readGroup limits.threeCodec.twoCodec.zstd leafLimits bound index <;> rfl

theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    GroupWire limits leafLimits bound index slots := by
  by_cases selected : Leaf.MixedCodec.V2.selectedCodec bound index = .ok Payload.Codec.uncompressed.id
  · rw [readGroup_uncompressed_agrees selected] at read
    cases branch : Leaf.Uncompressed.Dispatch.V2.readGroup limits.uncompressed leafLimits bound index with
    | error => simp [branch, Except.mapError] at read
    | ok decoded =>
      simp [branch, Except.mapError] at read
      subst slots
      exact .uncompressed selected (Leaf.Uncompressed.Dispatch.V2.readGroup_wire branch)
  · rw [readGroup_threeCodec_agrees selected] at read
    cases branch : Leaf.MixedCodec.V2.WithSnappy.readGroup limits.threeCodec leafLimits bound index with
    | error => simp [branch, Except.mapError] at read
    | ok decoded =>
      simp [branch, Except.mapError] at read
      subst slots
      exact .threeCodec (Leaf.MixedCodec.V2.WithSnappy.readGroup_wire branch)

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed
