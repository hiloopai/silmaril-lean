module

public import Silmaril.Formats.Compression.Inflate.Stream.MemberSemantics
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.ContainerFields
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.ReaderOffset
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.RawContainers
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.Protocol

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.MemberSemantics`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.MemberSemantics

open Silmaril.Formats.Compression

theorem afterRaw_aligned_inputView (kind : Kind) (output input : List UInt8) (total : Nat) :
    inputView (afterRaw kind (.ok (output, ContainerFields.alignedReader input total))) =
      (checkTrailer kind output input).map (fun rest => (output, rest)) := by
  cases kind with
  | zlib =>
    simp only [afterRaw, trailer, inputView, ContainerFields.validationReader_zlibTrailer,
      checkTrailer, Option.map_map]
    cases zlibCheckTrailer output input <;> rfl
  | gzip =>
    simp only [afterRaw, trailer, inputView, ContainerFields.validationReader_gzipTrailer,
      checkTrailer, Option.map_map]
    cases gzipCheckTrailer output input <;> rfl

/-- Final-byte padding is already removed by the raw result; its whole-byte
suffix remains available to the trailer parser at the same absolute position. -/
theorem afterRaw_alignResult_inputView (kind : Kind) (result : RawSemantics.Result) :
    inputView (afterRaw kind (RawSemantics.alignResult result)) =
      finishView kind (Blocks.inputView (RawSemantics.alignResult result)) := by
  cases result with
  | error err => rfl
  | ok pair =>
    obtain ⟨output, reader⟩ := pair
    exact afterRaw_aligned_inputView kind output reader.input (reader.totalRead + reader.count)

theorem body_aligned_inputView (kind : Kind) (input : List UInt8) (total : Nat) :
    inputView (body kind (ContainerFields.alignedReader input total)) =
      finishView kind (Deflate.deflateTake input) := by
  change inputView (afterRaw kind (RawSemantics.alignResult _)) = _
  rw [afterRaw_alignResult_inputView]
  change finishView kind (Blocks.inputView
    (RawSemantics.format (ContainerFields.alignedReader input total) [])) = _
  exact congrArg (finishView kind) (ReaderOffset.format_aligned_inputView input total)

/-- After an independently validated zlib header, the shared member meaning
equals `zlibTake`, for any absolute payload bit position. -/
theorem body_zlib_eq_spec (member input : List UInt8) (total : Nat)
    (hheader : zlibCheckHeader member = some input) :
    inputView (body .zlib (ContainerFields.alignedReader input total)) = zlibTake member := by
  rw [body_aligned_inputView]
  simp only [zlibTake, hheader, finishView, checkTrailer]
  cases Deflate.deflateTake input with
  | error err => rfl
  | ok pair =>
    obtain ⟨output, afterData⟩ := pair
    dsimp only
    cases zlibCheckTrailer output afterData <;> rfl

/-- The gzip bridge includes the shared optional-field/FHCRC header checker.
It is a single member observation rather than the concatenating client loop. -/
theorem body_gzip_eq_spec (member input : List UInt8) (total : Nat)
    (hheader : RawContainers.gzipBody member = some input) :
    inputView (body .gzip (ContainerFields.alignedReader input total)) = gzipMember member := by
  rw [body_aligned_inputView, RawContainers.gzipMember_eq_body]
  simp only [hheader, finishView, checkTrailer]
  cases Deflate.deflateTake input with
  | error err => rfl
  | ok pair =>
    obtain ⟨output, afterData⟩ := pair
    dsimp only
    cases gzipCheckTrailer output afterData <;> rfl

/-! The accepted stored-A vectors also check the start bridges with arbitrary
following bytes and nonzero absolute reader positions. -/

theorem storedA_zlib (tail : List UInt8) (total : Nat) :
    inputView (body .zlib (ContainerFields.alignedReader
      (RawContainers.storedAInput ++ ([0, 66, 0, 66] ++ tail)) total)) = some ([65], tail) := by
  exact (body_zlib_eq_spec
    ([0x78, 0x01] ++ RawContainers.storedAInput ++ ([0, 66, 0, 66] ++ tail))
    (RawContainers.storedAInput ++ ([0, 66, 0, 66] ++ tail)) total rfl).trans
      (RawContainers.storedA_zlib .v131 tail)

theorem storedA_gzip (tail : List UInt8) (total : Nat) :
    inputView (body .gzip (ContainerFields.alignedReader
      (RawContainers.storedAInput ++ ([139, 158, 217, 211, 1, 0, 0, 0] ++ tail)) total)) =
      some ([65], tail) := by
  exact (body_gzip_eq_spec
    ([31, 139, 8, 0, 0, 0, 0, 0, 0, 255] ++ RawContainers.storedAInput ++
      ([139, 158, 217, 211, 1, 0, 0, 0] ++ tail))
    (RawContainers.storedAInput ++ ([139, 158, 217, 211, 1, 0, 0, 0] ++ tail)) total rfl).trans
      (RawContainers.storedA_gzip .develop tail)

end Silmaril.Formats.Compression.Inflate.Stream.MemberSemantics
