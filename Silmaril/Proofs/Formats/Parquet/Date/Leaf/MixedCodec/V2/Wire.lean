module

public import Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots selectChunk)
open Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2

theorem selectedCodec_exact {bound : Bound} {index : Nat} {selected : Date.Leaf.Chunk}
    (admitted : selectChunk bound index = .ok selected) :
    selectedCodec bound index = .ok selected.column.metadata.codec := by
  obtain ⟨group, column, _⟩ := Date.Leaf.selectChunk_exact admitted
  simp [selectedCodec, group, column, Pure.pure, Except.pure]

theorem readGroup_selectionError {limits : Limits} {bound : Bound} {index : Nat} {cause : Date.Leaf.Error}
    (failed : selectedCodec bound index = .error cause) :
    readGroup limits bound index = .error (.selection cause) := by
  simp [readGroup, failed, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_unsupportedCodec {limits : Limits} {bound : Bound} {index : Nat} {actual : Int}
    (selected : selectedCodec bound index = .ok actual)
    (gzip : actual ≠ Payload.Codec.gzip.id) (zstd : actual ≠ Payload.Codec.zstd.id) :
    readGroup limits bound index = .error (.unsupportedCodec actual) := by
  simp [readGroup, selected, gzip, zstd, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_gzip_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (selected : selectedCodec bound index = .ok Payload.Codec.gzip.id) :
    readGroup limits bound index =
      (Date.Leaf.Gzip.Dispatch.V2.WithPlain.readGroup limits.gzip bound index).mapError .gzip := by
  simp [readGroup, selected, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_zstd_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (selected : selectedCodec bound index = .ok Payload.Codec.zstd.id) :
    readGroup limits bound index =
      (Date.Leaf.Zstd.Dispatch.V2.readGroup limits.zstd bound index).mapError .zstd := by
  simp [readGroup, selected, Payload.Codec.id, Except.mapError, Bind.bind, Except.bind]

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) : GroupWire limits bound index slots := by
  cases selected : selectedCodec bound index with
  | error => rw [readGroup_selectionError selected] at read; contradiction
  | ok actual =>
    by_cases gzip : actual = Payload.Codec.gzip.id
    · subst actual
      have decoded := mapError_ok ((readGroup_gzip_agrees selected).symm.trans read)
      exact .gzip selected (Date.Leaf.Gzip.Dispatch.V2.WithPlain.readGroup_wire decoded)
    by_cases zstd : actual = Payload.Codec.zstd.id
    · subst actual
      have decoded := mapError_ok ((readGroup_zstd_agrees selected).symm.trans read)
      exact .zstd selected (Date.Leaf.Zstd.Dispatch.V2.readGroup_wire decoded)
    rw [readGroup_unsupportedCodec selected gzip zstd] at read
    contradiction

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2
