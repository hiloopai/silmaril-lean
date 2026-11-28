module

public import Silmaril.Formats.Parquet.FlatColumn.Defs
public import Silmaril.Formats.Compression.Brotli.Stream.Dictionary.Defs

/-! Opt-in codec 4 payload expansion for flat PLAIN Parquet data pages. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ScalarPage.Brotli

open Silmaril.Formats.Compression

structure Limits where
  framing : Page.Limits
  page : ScalarPage.Limits
  window : Nat
  bits : Nat
  blocks : Nat
  commands : Nat
  mapEntries : Nat := 17408
  trees : Nat := 768

inductive Error where
  | codec (actual : Int)
  | framing (reason : Page.Error)
  | checksum (reason : Page.Checksum.Error)
  | unsupportedKind
  | page (reason : ScalarPage.Error)
  | stream (reason : Brotli.Stream.DistanceSwitch.Error)
  deriving DecidableEq, Repr

structure Result where
  frame : Page.Frame
  checksum : Page.Checksum.Status
  expanded : List UInt8
  deriving DecidableEq, Repr

def streamLimits (limits : Limits) (bounds : Payload.Bounds) : Brotli.Stream.Dictionary.Limits :=
  ⟨⟨bounds.compressedSize, bounds.expectedSize, limits.window, limits.bits, limits.blocks, limits.mapEntries, limits.trees⟩,
    limits.commands⟩

namespace Internal

/-- The stream output cap is the checked declaration. An overrun is a
    size mismatch, while caller caps are checked at the outer boundary. -/
def streamError : Brotli.Stream.DistanceSwitch.Error → Error
  | .envelope ⟨_, _, _, .framing .outputLimit⟩ => .page (.payload .outputSizeMismatch)
  | error => .stream error

def decodePayload (limits : Limits) (bounds : Payload.Bounds) (input : List UInt8) :
    Except Error (List UInt8) :=
  if bounds.compressedLimit < bounds.compressedSize then .error (.page (.payload .compressedLimit))
  else if bounds.outputLimit < bounds.expectedSize then .error (.page (.payload .outputLimit))
  else if !Payload.Internal.hasLength bounds.compressedSize input then
    .error (.page (.payload .compressedSizeMismatch))
  else do
    let decoded ← (Brotli.Stream.Dictionary.decode (streamLimits limits bounds) input).mapError streamError
    if decoded.execution.output.size ≠ bounds.expectedSize then .error (.page (.payload .outputSizeMismatch))
    else .ok decoded.execution.output.toList

def expand (limits : Limits) (params : Parameters) (stored : Bytes) : Except Error (List UInt8) := do
  let _ ← (validate params limits.page stored).mapError Error.page
  match params.version with
  | .v1 _ _ => decodePayload limits (limits.page.payloadBounds params.sizes 0) stored.toList
  | .v2 _ _ repetitions definitions flag =>
    let (levels, encoded) ←
      (splitV2 params.sizes limits.page.levels.bytes repetitions definitions stored).mapError Error.page
    let bounds := limits.page.payloadBounds params.sizes definitions
    let action := if flag.getD true then decodePayload limits bounds encoded
      else (Payload.decode bounds Payload.Codec.uncompressed.id encoded).mapError (.page ∘ .payload)
    let plain ← action
    pure (levels.toList ++ plain)

end Internal

/-- Parse and expand one flat PLAIN data page in the given chunk. Check
    the CRC, when present, over the bounded original stored body before
    interpreting levels or invoking either payload decoder. The codec ID
    comes from the caller's selected column metadata. -/
def decodeAt (limits : Limits) (layout : FlatColumn.Layout) (codec : Int)
    (source : Bytes) (chunk : Footer.Span) (cursor : Nat) : Except Error Result := do
  if codec ≠ Payload.Codec.brotli.id then throw (.codec codec)
  let frame ← (Page.readPage limits.framing source chunk cursor).mapError Error.framing
  let checksum ← (Page.Checksum.verify limits.page.compressedBytes source frame).mapError Error.checksum
  let some params := FlatColumn.pageParameters layout codec frame.value | throw .unsupportedKind
  let expanded ← Internal.expand limits params (Page.Checksum.payloadBytes source frame)
  pure ⟨frame, checksum, expanded⟩

def StreamWire (limits : Limits) (bounds : Payload.Bounds) (input output : List UInt8) : Prop :=
  ∃ decoded, Brotli.Stream.Dictionary.Wire (streamLimits limits bounds) input (.ok decoded) ∧
    decoded.execution.output.toList = output

def PayloadWire (limits : Limits) (bounds : Payload.Bounds) (input output : List UInt8) : Prop :=
  input.length = bounds.compressedSize ∧ input.length ≤ bounds.compressedLimit ∧
  output.length = bounds.expectedSize ∧ output.length ≤ bounds.outputLimit ∧
  StreamWire limits bounds input output

/-- Exact stored and expanded extents, with the original uncompressed
    V2 level prefix excepted from codec dispatch. -/
def ExpansionWire (limits : Limits) (params : Parameters) (stored : Bytes) (expanded : List UInt8) : Prop :=
  stored.length = params.sizes.compressed ∧ stored.length ≤ limits.page.compressedBytes ∧
  expanded.length = params.sizes.uncompressed ∧ expanded.length ≤ limits.page.uncompressedBytes ∧
  match params.version with
  | .v1 _ _ => StreamWire limits (limits.page.payloadBounds params.sizes 0) stored.toList expanded
  | .v2 _ _ repetitions definitions flag =>
    repetitions = 0 ∧ definitions ≤ params.sizes.compressed ∧ definitions ≤ params.sizes.uncompressed ∧
    definitions ≤ limits.page.levels.bytes ∧
    ∃ levels encoded plain : List UInt8,
      levels.length = definitions ∧ stored.toList = levels ++ encoded ∧ expanded = levels ++ plain ∧
      encoded.length = params.sizes.compressed - definitions ∧
      plain.length = params.sizes.uncompressed - definitions ∧
      if flag.getD true then StreamWire limits (limits.page.payloadBounds params.sizes definitions) encoded plain
      else plain = encoded

structure Wire (limits : Limits) (layout : FlatColumn.Layout) (codec : Int)
    (source : Bytes) (chunk : Footer.Span) (cursor : Nat) (result : Result) : Prop where
  codecExact : codec = Payload.Codec.brotli.id
  parsed : Page.readPage limits.framing source chunk cursor = .ok result.frame
  extent : Page.FrameWithin chunk cursor result.frame
  chunkBound : chunk.stop ≤ source.length
  checksum : Page.Checksum.verify limits.page.compressedBytes source result.frame = .ok result.checksum
  expandedSize : result.expanded.length = result.frame.value.uncompressedSize
  expandedCap : result.expanded.length ≤ limits.page.uncompressedBytes
  body : ∃ params stored,
    FlatColumn.pageParameters layout codec result.frame.value = some params ∧
    source.slice? result.frame.payload.start (some result.frame.payload.stop) = some stored ∧
    stored = Page.Checksum.payloadBytes source result.frame ∧ stored.length = result.frame.value.compressedSize ∧
    ExpansionWire limits params stored result.expanded

end Silmaril.Formats.Parquet.ScalarPage.Brotli
