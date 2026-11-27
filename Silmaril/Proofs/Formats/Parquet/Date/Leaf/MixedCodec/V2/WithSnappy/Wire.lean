module

public import Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.Defs
import Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy
open Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2 (selectedCodec)

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

theorem readGroup_twoCodec_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (outsideSnappy : ∀ actual, selectedCodec bound index = .ok actual → actual ≠ Payload.Codec.snappy.id) :
    readGroup limits bound index =
      (Date.Leaf.MixedCodec.V2.readGroup limits.toTwoCodecLimits bound index).mapError .twoCodec := by
  cases found : selectedCodec bound index with
  | error =>
    simp [readGroup, Date.Leaf.MixedCodec.V2.readGroup, found, Except.mapError, Bind.bind, Except.bind]
  | ok actual =>
    simp [readGroup, Date.Leaf.MixedCodec.V2.readGroup, found, outsideSnappy actual found,
      Except.mapError, Bind.bind, Except.bind]

private theorem selected_nonSnappy {bound : Bound} {index : Nat} {actual : Int}
    (selected : selectedCodec bound index = .ok actual) (different : actual ≠ Payload.Codec.snappy.id) :
    ∀ codec, selectedCodec bound index = .ok codec → codec ≠ Payload.Codec.snappy.id := by
  intro codec found
  cases Except.ok.inj (selected.symm.trans found)
  exact different

theorem readGroup_selectionError {limits : Limits} {bound : Bound} {index : Nat} {cause : Date.Leaf.Error}
    (failed : selectedCodec bound index = .error cause) :
    readGroup limits bound index = .error (.twoCodec (.selection cause)) := by
  simp [readGroup, failed, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_unsupportedCodec {limits : Limits} {bound : Bound} {index : Nat} {actual : Int}
    (selected : selectedCodec bound index = .ok actual)
    (snappy : actual ≠ Payload.Codec.snappy.id) (gzip : actual ≠ Payload.Codec.gzip.id)
    (zstd : actual ≠ Payload.Codec.zstd.id) :
    readGroup limits bound index = .error (.twoCodec (.unsupportedCodec actual)) := by
  rw [readGroup_twoCodec_agrees (selected_nonSnappy selected snappy),
    Date.Leaf.MixedCodec.V2.readGroup_unsupportedCodec selected gzip zstd]
  rfl

theorem readGroup_gzip_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (selected : selectedCodec bound index = .ok Payload.Codec.gzip.id) :
    readGroup limits bound index =
      ((Date.Leaf.Gzip.Dispatch.V2.WithPlain.readGroup limits.gzip bound index).mapError
        Date.Leaf.MixedCodec.V2.GroupError.gzip).mapError .twoCodec := by
  rw [readGroup_twoCodec_agrees (selected_nonSnappy selected (by decide)),
    Date.Leaf.MixedCodec.V2.readGroup_gzip_agrees selected]

theorem readGroup_zstd_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (selected : selectedCodec bound index = .ok Payload.Codec.zstd.id) :
    readGroup limits bound index =
      ((Date.Leaf.Zstd.Dispatch.V2.readGroup limits.zstd bound index).mapError
        Date.Leaf.MixedCodec.V2.GroupError.zstd).mapError .twoCodec := by
  rw [readGroup_twoCodec_agrees (selected_nonSnappy selected (by decide)),
    Date.Leaf.MixedCodec.V2.readGroup_zstd_agrees selected]

theorem readGroup_snappy_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (selected : selectedCodec bound index = .ok Payload.Codec.snappy.id) :
    readGroup limits bound index =
      (Date.Leaf.Snappy.Dispatch.V2.readGroup limits.snappy bound index).mapError .snappy := by
  simp [readGroup, selected, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) : GroupWire limits bound index slots := by
  cases selected : selectedCodec bound index with
  | error => rw [readGroup_selectionError selected] at read; contradiction
  | ok actual =>
    by_cases snappy : actual = Payload.Codec.snappy.id
    · subst actual
      have decoded := mapError_ok ((readGroup_snappy_agrees selected).symm.trans read)
      exact .snappy selected (Date.Leaf.Snappy.Dispatch.V2.readGroup_wire decoded)
    · have decoded := mapError_ok
        ((readGroup_twoCodec_agrees (selected_nonSnappy selected snappy)).symm.trans read)
      exact .twoCodec (Date.Leaf.MixedCodec.V2.readGroup_wire decoded)

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy
