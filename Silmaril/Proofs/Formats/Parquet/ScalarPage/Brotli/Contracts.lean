module

public import Silmaril.Formats.Parquet.ScalarPage.Brotli.Defs
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Silmaril.Formats.Parquet.Payload.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import Silmaril.Formats.Compression.Brotli.Stream.Dictionary.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Parquet.ScalarPage.Brotli

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.ScalarPage.Brotli
open Silmaril.Formats.Compression

theorem decodePayload_sound {limits : Limits} {bounds : Payload.Bounds} {input output : List UInt8}
    (read : Internal.decodePayload limits bounds input = .ok output) : PayloadWire limits bounds input output := by
  unfold Internal.decodePayload at read
  split at read <;> try contradiction
  rename_i inputFits
  split at read <;> try contradiction
  rename_i outputFits
  split at read <;> try contradiction
  rename_i hasLength
  cases decode : Brotli.Stream.Dictionary.decode (streamLimits limits bounds) input with
  | error reason => simp [decode, Except.mapError, bind, Except.bind] at read
  | ok decoded =>
    simp only [decode, Except.mapError, bind, Except.bind] at read
    split at read <;> try contradiction
    rename_i extent
    cases read
    have inputSize := Payload.hasLength_iff.mp (by simpa using hasLength)
    have outputSize : decoded.execution.output.toList.length = bounds.expectedSize := by
      simpa using (not_not.mp extent)
    exact ⟨inputSize, inputSize ▸ Nat.le_of_not_gt inputFits, outputSize, outputSize ▸ Nat.le_of_not_gt outputFits,
      decoded, (Brotli.Stream.Dictionary.decode_sound decode).1, rfl⟩

theorem decodePayload_stream_error {limits : Limits} {bounds : Payload.Bounds} {input : List UInt8}
    {error : Brotli.Stream.DistanceSwitch.Error} (inputFits : bounds.compressedSize ≤ bounds.compressedLimit)
    (outputFits : bounds.expectedSize ≤ bounds.outputLimit) (extent : input.length = bounds.compressedSize)
    (decoded : Brotli.Stream.Dictionary.decode (streamLimits limits bounds) input = .error error) :
    Internal.decodePayload limits bounds input = .error (Internal.streamError error) := by
  simp [Internal.decodePayload, Nat.not_lt.mpr inputFits, Nat.not_lt.mpr outputFits,
    Payload.hasLength_iff.mpr extent, decoded, Except.mapError, bind, Except.bind]

private theorem validate_bounds {limits : ScalarPage.Limits} {params : ScalarPage.Parameters}
    {stored : Bytes} {layout : FlatPage.Layout} (read : ScalarPage.validate params limits stored = .ok layout) :
    stored.length = params.sizes.compressed ∧ stored.length ≤ limits.compressedBytes ∧
    params.sizes.uncompressed ≤ limits.uncompressedBytes := by
  simp only [ScalarPage.validate, ScalarPage.validateFor] at read
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  rename_i input
  split at read <;> try contradiction
  rename_i output
  split at read <;> try contradiction
  rename_i extent
  exact ⟨not_not.mp extent, by omega, by omega⟩

private theorem raw_sound {bounds : Payload.Bounds} {encoded plain : List UInt8}
    (read : Payload.decode bounds Payload.Codec.uncompressed.id encoded = .ok plain) :
    encoded.length = bounds.compressedSize ∧ plain.length = bounds.expectedSize ∧ plain = encoded := by
  obtain ⟨codec, id, wire, inputSize, _, outputSize, _⟩ := Payload.decode_sound read
  have raw : codec = .uncompressed := by simpa [Payload.Codec.ofId, Payload.Codec.id] using id.symm
  subst codec
  cases wire
  exact ⟨inputSize, outputSize, rfl⟩

private theorem bind_ok {ε α β : Type} {action : Except ε α} {next : α → Except ε β}
    {result : β} (read : (action >>= next) = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error reason => cases read
  | ok value => exact ⟨value, rfl, read⟩

theorem expand_sound {limits : Limits} {params : ScalarPage.Parameters} {stored : Bytes} {expanded : List UInt8}
    (read : Internal.expand limits params stored = .ok expanded) : ExpansionWire limits params stored expanded := by
  unfold Internal.expand at read
  cases validated : ScalarPage.validate params limits.page stored with
  | error reason => simp [validated, Except.mapError, bind, Except.bind] at read
  | ok layout =>
    simp only [validated, Except.mapError, bind, Except.bind] at read
    obtain ⟨extent, inputCap, outputCap⟩ := validate_bounds validated
    refine ⟨extent, inputCap, ?_⟩
    cases version : params.version with
    | v1 definitions repetitions =>
      simp only [version] at read ⊢
      obtain ⟨_, _, size, _, wire⟩ := decodePayload_sound read
      simp only [ScalarPage.Limits.payloadBounds, Nat.sub_zero] at size
      exact ⟨size, size ▸ outputCap, wire⟩
    | v2 nulls rows repetitions definitions flag =>
      simp only [version] at read ⊢
      cases sliced : ScalarPage.splitV2 params.sizes limits.page.levels.bytes repetitions definitions stored with
      | error reason => simp [sliced] at read
      | ok pair =>
        obtain ⟨levels, encoded⟩ := pair
        simp only [sliced] at read
        obtain ⟨plain, expandedPayload, joined⟩ := bind_ok read
        cases joined
        obtain ⟨rep, comp, uncomp, _, levelCap, levelSize, sourceParts⟩ := ScalarPage.splitV2_ok_iff.mp sliced
        have parts : encoded.length = params.sizes.compressed - definitions ∧
            plain.length = params.sizes.uncompressed - definitions ∧
            (if flag.getD true then
              StreamWire limits (limits.page.payloadBounds params.sizes definitions) encoded plain
            else plain = encoded) := by
          cases flagValue : flag.getD true
          · simp only [flagValue, Bool.false_eq_true, ite_false] at expandedPayload ⊢
            cases raw : Payload.decode (limits.page.payloadBounds params.sizes definitions)
                Payload.Codec.uncompressed.id encoded with
            | error reason => simp [raw] at expandedPayload
            | ok value =>
              simp only [raw, Except.ok.injEq] at expandedPayload
              subst value
              exact raw_sound raw
          · simp only [flagValue, ite_true] at expandedPayload ⊢
            obtain ⟨inputSize, _, outputSize, _, wire⟩ := decodePayload_sound expandedPayload
            exact ⟨inputSize, outputSize, wire⟩
        obtain ⟨inputSize, outputSize, wire⟩ := parts
        have fullSize : (levels.toList ++ plain).length = params.sizes.uncompressed := by
          rw [List.length_append, Bytes.length_toList, levelSize, outputSize]
          omega
        exact ⟨fullSize, fullSize ▸ outputCap, rep, comp, uncomp, levelCap,
          levels.toList, encoded, plain, by simpa using levelSize, sourceParts, rfl, inputSize, outputSize, wire⟩

private theorem pageParameters_sizes {layout : FlatColumn.Layout} {codec : Int} {header : Page.Header}
    {params : ScalarPage.Parameters} (selected : FlatColumn.pageParameters layout codec header = some params) :
    params.sizes = ⟨header.compressedSize, header.uncompressedSize⟩ := by
  unfold FlatColumn.pageParameters at selected
  split at selected <;> cases selected <;> rfl

theorem decodeAt_sound {limits : Limits} {layout : FlatColumn.Layout} {codec : Int}
    {source : Bytes} {chunk : Footer.Span} {cursor : Nat} {result : Result}
    (read : decodeAt limits layout codec source chunk cursor = .ok result) :
    Wire limits layout codec source chunk cursor result := by
  unfold decodeAt at read
  split at read <;> try contradiction
  rename_i codecKnown
  cases framed : Page.readPage limits.framing source chunk cursor with
  | error reason => simp [framed, Except.mapError, bind, Except.bind] at read
  | ok frame =>
    simp only [framed, Except.mapError, bind, Except.bind] at read
    cases checked : Page.Checksum.verify limits.page.compressedBytes source frame with
    | error reason => simp [checked] at read
    | ok status =>
      simp only [checked] at read
      cases selected : FlatColumn.pageParameters layout codec frame.value with
      | none => simp [selected] at read
      | some params =>
        simp only [selected] at read
        obtain ⟨expanded, expandedRead, assembled⟩ := bind_ok read
        cases assembled
        have wire := expand_sound expandedRead
        have size := wire.2.2.1
        rw [pageParameters_sizes selected] at size
        obtain ⟨extent, bound⟩ := Page.readPage_within framed
        obtain ⟨slice, length⟩ := Page.Checksum.payload_exact (Page.Checksum.payloadWithin_of_readPage framed)
        exact ⟨not_not.mp codecKnown, framed, extent, bound, checked, size, wire.2.2.2.1,
          params, _, selected, slice, rfl, length, wire⟩

theorem decodeAt_checksum_error {limits : Limits} {layout : FlatColumn.Layout} {codec : Int}
    {source : Bytes} {chunk : Footer.Span} {cursor : Nat} {frame : Page.Frame} {reason : Page.Checksum.Error}
    (admitted : codec = Payload.Codec.brotli.id)
    (framed : Page.readPage limits.framing source chunk cursor = .ok frame)
    (failed : Page.Checksum.verify limits.page.compressedBytes source frame = .error reason) :
    decodeAt limits layout codec source chunk cursor = .error (.checksum reason) := by
  simp [decodeAt, admitted, framed, failed, Except.mapError, bind, Except.bind]

theorem Wire.crc {limits : Limits} {layout : FlatColumn.Layout} {codec : Int}
    {source : Bytes} {chunk : Footer.Span} {cursor : Nat} {result : Result}
    (wire : Wire limits layout codec source chunk cursor result) :
    match result.checksum with
    | .absent => result.frame.value.crc = none
    | .valid value => result.frame.value.crc = some value ∧
      Compression.crc32Spec (Page.Checksum.payloadBytes source result.frame).toList = value := by
  have verified := wire.checksum
  cases status : result.checksum with
  | absent =>
    rw [status] at verified
    exact (Page.Checksum.verify_absent_iff.mp verified).2.2
  | valid declared =>
    rw [status] at verified
    exact (Page.Checksum.verify_valid_iff.mp verified).2.2

end Silmaril.Proofs.Formats.Parquet.ScalarPage.Brotli
