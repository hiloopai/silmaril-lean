module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Snappy.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary

open Silmaril.Formats Parquet Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

theorem codec_ok_iff {id : Int} {codec : Codec} :
    Codec.ofId id = some codec ↔ id = codec.id := by
  cases codec <;> by_cases raw : id = 0 <;> by_cases snappy : id = 1 <;>
    by_cases gzip : id = 2 <;> by_cases zstd : id = 6 <;> simp_all [Codec.ofId, Codec.id]

theorem classify_ok_iff {metadata : Footer.ColumnMetadata} {branch : Branch} :
    classify metadata = .ok branch ↔ branch.Matches metadata := by
  cases codec : Codec.ofId metadata.codec with
  | none =>
    have unknown (known : Codec) : metadata.codec ≠ known.id :=
      fun claimed => by simpa [codec] using codec_ok_iff.mpr claimed
    cases branch <;> simp [classify, codec, Branch.Matches, unknown]
  | some found =>
    have same (known : Codec) : metadata.codec = known.id ↔ found = known := by
      rw [← codec_ok_iff, codec, Option.some.injEq]
    cases branch with
    | scalar chosen =>
      cases offset : metadata.dictionaryPageOffset with
      | none => simp [classify, codec, offset, Branch.Matches, same]
      | some _ =>
        by_cases allowed : dictionaryEncodings metadata.encodings = true <;>
          simp [classify, codec, offset, Branch.Matches, allowed]
    | dictionary chosen =>
      cases offset : metadata.dictionaryPageOffset with
      | none => simp [classify, codec, offset, Branch.Matches]
      | some _ =>
        by_cases allowed : dictionaryEncodings metadata.encodings = true <;>
          simp [classify, codec, offset, Branch.Matches, same, allowed]

theorem selectedColumn_ok_iff {bound : Bound} {index : Nat} {column : Footer.ColumnChunk} :
    selectedColumn bound index = .ok column ↔
      ∃ group, bound.snapshot.groupAt index = some group ∧
        group.columns[bound.ordinal - 1]? = some column := by
  cases selected : bound.snapshot.groupAt index with
  | none => simp [selectedColumn, selected]
  | some group =>
    cases chosen : group.columns[bound.ordinal - 1]? <;>
      simp [selectedColumn, selected, chosen, pure, Except.pure]

theorem route_ok_iff {bound : Bound} {index : Nat} {branch : Branch} :
    route bound index = .ok branch ↔
      ∃ group column, bound.snapshot.groupAt index = some group ∧
        group.columns[bound.ordinal - 1]? = some column ∧ branch.Matches column.metadata := by
  constructor
  · intro accepted
    unfold route at accepted
    obtain ⟨column, picked, accepted⟩ := bind_ok accepted
    obtain ⟨group, found, selected⟩ := selectedColumn_ok_iff.mp (mapError_ok picked)
    exact ⟨group, column, found, selected, classify_ok_iff.mp (mapError_ok accepted)⟩
  · rintro ⟨group, column, found, selected, chosen⟩
    simp [route, selectedColumn_ok_iff.mpr ⟨group, found, selected⟩, classify_ok_iff.mpr chosen,
      Except.mapError, Bind.bind, Except.bind]

private theorem route_dictionary_offset {bound : Bound} {index : Nat} {codec : Codec}
    (chosen : route bound index = .ok (.dictionary codec)) :
    Leaf.Snappy.Dispatch.V2.hasDictionary bound index = .ok true := by
  obtain ⟨group, column, found, selected, _, offset, _⟩ := route_ok_iff.mp chosen
  simp [Leaf.Snappy.Dispatch.V2.hasDictionary, found, selected, offset, pure, Except.pure]

theorem readGroup_scalar_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {codec : Codec} (chosen : route bound index = .ok (.scalar codec)) :
    readGroup limits leafLimits bound index =
      (Leaf.ScalarDispatch.readGroup limits.scalar leafLimits bound index).mapError .scalar := by
  simp [readGroup, chosen, readSelected, Bind.bind, Except.bind]

theorem readGroup_uncompressed_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} (chosen : route bound index = .ok (.dictionary .uncompressed)) :
    readGroup limits leafLimits bound index =
      (Leaf.Uncompressed.Dispatch.V2.readGroup limits.dictionary.uncompressed leafLimits bound index).mapError
        .uncompressedDictionary := by
  simp [readGroup, chosen, readSelected, Leaf.Uncompressed.Dispatch.V2.readGroup, route_dictionary_offset chosen,
    Bind.bind, Except.bind]

theorem readGroup_snappy_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} (chosen : route bound index = .ok (.dictionary .snappy)) :
    readGroup limits leafLimits bound index =
      (Leaf.Snappy.Dispatch.V2.readGroup limits.dictionary.threeCodec.snappy leafLimits bound index).mapError
        .snappyDictionary := by
  simp [readGroup, chosen, readSelected, Leaf.Snappy.Dispatch.V2.readGroup, route_dictionary_offset chosen,
    Bind.bind, Except.bind]

theorem readGroup_gzip_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} (chosen : route bound index = .ok (.dictionary .gzip)) :
    readGroup limits leafLimits bound index =
      (Leaf.Gzip.Dispatch.V2.readGroup limits.dictionary.threeCodec.twoCodec.gzip leafLimits bound index).mapError
        .gzipDictionary := by
  have offset : Leaf.Gzip.Dispatch.V2.hasDictionary bound index = .ok true :=
    route_dictionary_offset chosen
  simp [readGroup, chosen, readSelected, Leaf.Gzip.Dispatch.V2.readGroup, offset, Bind.bind, Except.bind]

theorem readGroup_zstd_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} (chosen : route bound index = .ok (.dictionary .zstd)) :
    readGroup limits leafLimits bound index =
      (Leaf.Zstd.Dispatch.V2.readGroup limits.dictionary.threeCodec.twoCodec.zstd leafLimits bound index).mapError
        .zstdDictionary := by
  have offset : Leaf.Zstd.Dispatch.V2.hasDictionary bound index = .ok true :=
    route_dictionary_offset chosen
  simp [readGroup, chosen, readSelected, Leaf.Zstd.Dispatch.V2.readGroup, offset, Except.mapError,
    Bind.bind, Except.bind]

theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    GroupWire limits leafLimits bound index slots := by
  unfold readGroup at read
  obtain ⟨branch, chosen, read⟩ := bind_ok read
  refine ⟨branch, chosen, ?_⟩
  cases branch with
  | scalar _ => exact Leaf.ScalarDispatch.readGroup_wire (mapError_ok read)
  | dictionary codec =>
    cases codec with
    | uncompressed =>
      have raw := mapError_ok read
      have planned := raw
      unfold Leaf.Uncompressed.Dispatch.V2.readDictionary at planned
      obtain ⟨plan, picked, _⟩ := bind_ok planned
      exact ⟨plan, picked, Leaf.Uncompressed.Dispatch.V2.readDictionary_wire picked raw⟩
    | snappy =>
      have raw := mapError_ok read
      have planned := raw
      unfold Leaf.Snappy.Dispatch.V2.readDictionary at planned
      obtain ⟨plan, picked, _⟩ := bind_ok planned
      exact ⟨plan, picked, Leaf.Snappy.Dispatch.V2.readDictionary_wire picked raw⟩
    | gzip =>
      have raw := mapError_ok read
      have planned := raw
      unfold Leaf.Gzip.Dispatch.V2.readDictionary at planned
      obtain ⟨plan, picked, _⟩ := bind_ok planned
      exact ⟨plan, picked, Leaf.Gzip.Dispatch.V2.readDictionary_wire picked raw⟩
    | zstd =>
      have raw := mapError_ok read
      have planned := raw
      unfold Leaf.Zstd.Dispatch.V2.readDictionary at planned
      obtain ⟨plan, picked, _⟩ := bind_ok planned
      exact ⟨plan, picked, Leaf.Zstd.Dispatch.V2.readDictionary_wire picked raw⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary
