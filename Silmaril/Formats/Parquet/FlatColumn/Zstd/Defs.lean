module

public import Silmaril.Formats.Parquet.FlatColumn.Defs
public import Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman.Defs

/-! # Opt-in flat PLAIN INT32 Parquet columns with codec 6

The same-snapshot walk supplies the original data page. V1 decodes its
complete body. V2 keeps the raw levels and decodes only the value suffix
selected by the resolved flag. The frame profile follows RFC 8878's
strict match distance rule and uses no dictionary.
-/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatColumn.Zstd

open Silmaril.Formats.Compression.Zstd

structure CompressionLimits where
  window : Nat
  commandsPerBlock : Nat

structure Limits where
  column : FlatColumn.Limits
  scalar : ScalarPage.Limits
  compression : CompressionLimits

inductive Error where
  | codec (actual : Int)
  | unsupportedKind
  | scalar (reason : ScalarPage.Error)
  | frame (reason : CheckedFrame.Huffman.Error)
  deriving DecidableEq, Repr

/-- The expected payload size is the decoder's remaining output budget. -/
def frameLimits (limits : CompressionLimits) (bounds : Payload.Bounds) : CheckedFrame.Huffman.Limits :=
  ⟨⟨bounds.compressedSize, bounds.expectedSize, limits.window⟩, limits.commandsPerBlock, ⟨128, ⟨256, 11⟩⟩⟩

/-- Codec 0 is used for a raw V2 value suffix in a codec-6 column. Use
    the existing exact uncompressed identity path for this case. -/
def decodePayload (limits : CompressionLimits) (bounds : Payload.Bounds) (codec : Int)
    (input : List UInt8) : Except Error (List UInt8) :=
  if codec = 0 then
    (Payload.decode bounds codec input).mapError (.scalar ∘ .payload)
  else if codec ≠ 6 then .error (.codec codec)
  else if bounds.compressedLimit < bounds.compressedSize then .error (.scalar (.payload .compressedLimit))
  else if bounds.outputLimit < bounds.expectedSize then .error (.scalar (.payload .outputLimit))
  else if !Payload.Internal.hasLength bounds.compressedSize input then
    .error (.scalar (.payload .compressedSizeMismatch))
  else do
    let out ← (CheckedFrame.Huffman.decode (frameLimits limits bounds) input).mapError Error.frame
    if out.length = bounds.expectedSize then pure out else .error (.scalar (.payload .outputSizeMismatch))

def PayloadWire (limits : CompressionLimits) (bounds : Payload.Bounds) (codec : Int)
    (input output : List UInt8) : Prop :=
  input.length = bounds.compressedSize ∧ input.length ≤ bounds.compressedLimit ∧
  output.length = bounds.expectedSize ∧ output.length ≤ bounds.outputLimit ∧
  ((codec = 0 ∧ output = input) ∨
    (codec = 6 ∧ ∃ header, CheckedFrame.Huffman.FrameWire (frameLimits limits bounds) input output header ∧
      header.windowSize ≤ limits.window))

namespace Internal

def prepare (limits : Limits) (params : ScalarPage.Parameters) (layout : FlatPage.Layout)
    (body : Bytes) : Except Error ScalarPage.Prepared := do
  match params.version with
  | .v1 definitions repetitions =>
    if definitions ≠ 3 ∨ repetitions ≠ 3 then throw (.scalar .unsupportedLevelEncoding)
    let decoded ← decodePayload limits.compression (limits.scalar.payloadBounds params.sizes 0)
      params.codec body.toList
    let slices ← (FlatPage.split layout limits.scalar.levels.bytes (.v1 (Bytes.ofList decoded))).mapError
      (.scalar ∘ .levels)
    let mask ← (FlatPage.readMask layout params.numValues limits.scalar.levels slices.definitions).mapError
      (.scalar ∘ .levels)
    pure ⟨mask, slices.scalars⟩
  | .v2 nulls rows repetitions definitions flag =>
    if params.numValues < nulls then throw (.scalar .invalidNullCount)
    if rows ≠ params.numValues then throw (.scalar .invalidRowCount)
    let (levels, encoded) ←
      (ScalarPage.splitV2 params.sizes limits.scalar.levels.bytes repetitions definitions body).mapError Error.scalar
    let mask ← (FlatPage.readMask layout params.numValues limits.scalar.levels levels).mapError (.scalar ∘ .levels)
    if mask.count true ≠ params.numValues - nulls then throw (.scalar (.levels .presentCountMismatch))
    let decoded ← decodePayload limits.compression (limits.scalar.payloadBounds params.sizes definitions)
      (ScalarPage.v2Codec params.codec flag) encoded
    pure ⟨mask, Bytes.ofList decoded⟩

end Internal

/-- Each branch retains the exact codec-covered bytes and checked level mask. -/
def PreparedWire (limits : Limits) (params : ScalarPage.Parameters) (layout : FlatPage.Layout)
    (body : Bytes) (page : ScalarPage.Prepared) : Prop :=
  match params.version with
  | .v1 definitions repetitions =>
    definitions = 3 ∧ repetitions = 3 ∧ ∃ decoded slices,
      PayloadWire limits.compression (limits.scalar.payloadBounds params.sizes 0) 6 body.toList decoded ∧
      FlatPage.split layout limits.scalar.levels.bytes (.v1 (Bytes.ofList decoded)) = .ok slices ∧
      FlatPage.readMask layout params.numValues limits.scalar.levels slices.definitions = .ok page.mask ∧
      page.scalars = slices.scalars
  | .v2 nulls rows repetitions definitions flag =>
    nulls ≤ params.numValues ∧ rows = params.numValues ∧ repetitions = 0 ∧
    definitions ≤ params.sizes.compressed ∧ definitions ≤ params.sizes.uncompressed ∧
    definitions ≤ limits.scalar.levels.bytes ∧ ∃ levels : Bytes, ∃ encoded : List UInt8,
      levels.length = definitions ∧ body.toList = levels.toList ++ encoded ∧
      FlatPage.readMask layout params.numValues limits.scalar.levels levels = .ok page.mask ∧
      page.mask.count true = params.numValues - nulls ∧
      PayloadWire limits.compression (limits.scalar.payloadBounds params.sizes definitions)
        (ScalarPage.v2Codec 6 flag) encoded page.scalars.toList

/-- Prepare the caller's selected data encoding in an admitted codec-6 page.
The V2 path preserves the raw levels and dispatches only the value suffix. -/
def prepareFor (encoding : Int) (limits : Limits) (params : ScalarPage.Parameters)
    (body : Bytes) : Except Error ScalarPage.Prepared := do
  if params.codec ≠ Payload.Codec.zstd.id then throw (.codec params.codec)
  let layout ← (ScalarPage.validateFor encoding params limits.scalar body).mapError Error.scalar
  Internal.prepare limits params layout body

def PageWire (limits : Limits) (columnLayout : FlatColumn.Layout) (metadata : Footer.ColumnMetadata)
    (header : Page.Header) (body : Bytes) (slots : List (Option Int32)) : Prop :=
  metadata.codec = 6 ∧ ∃ params layout page values,
    pageParameters columnLayout metadata.codec header = some params ∧
    ScalarPage.validate params limits.scalar body = .ok layout ∧
    body.length = header.compressedSize ∧ header.compressedSize ≤ limits.scalar.compressedBytes ∧
    header.uncompressedSize ≤ limits.scalar.uncompressedBytes ∧
    PreparedWire limits params layout body page ∧
    Plain.decodeInt32 (page.mask.count true) page.scalars = .ok values ∧
    FlatPage.reconstruct page.mask values = .ok slots

def decodePage (limits : Limits) (layout : FlatColumn.Layout) : DecodePage Int32 Error :=
  fun _ metadata header body =>
    if metadata.codec ≠ 6 then .error (.codec metadata.codec)
    else
      match pageParameters layout metadata.codec header with
      | none => .error .unsupportedKind
      | some params => do
        let levelLayout ← (ScalarPage.validate params limits.scalar body).mapError Error.scalar
        let page ← Internal.prepare limits params levelLayout body
        let values ← (Plain.decodeInt32 (page.mask.count true) page.scalars).mapError (.scalar ∘ .plain)
        (FlatPage.reconstruct page.mask values).mapError (.scalar ∘ .levels)

/-- Read one group of an admitted selected codec-6 PLAIN INT32 column. -/
def readColumn {snapshot : Snapshot.Checked} {name : String} {layout : FlatColumn.Layout}
    (binding : Binding snapshot ⟨name, .int32, layout⟩) (limits : Limits) (index : Nat) :
    Except (FlatColumn.Error Error) (List (Option Int32)) :=
  FlatColumn.readColumnFor .zstd binding limits.column ⟨0, .v1AndV2⟩ (decodePage limits layout) index

/-- The selected column retains its original ordered frames, codec-covered
    byte slices, and the exact output slots established for each page. -/
def ColumnWire {snapshot : Snapshot.Checked} {name : String} {layout : FlatColumn.Layout}
    (binding : Binding snapshot ⟨name, .int32, layout⟩) (limits : Limits) (index : Nat)
    (slots : List (Option Int32)) : Prop :=
  ∃ group column chunk frames pages,
    snapshot.groupAt index = some group ∧
    group.columns[binding.columnOrdinal]? = some column ∧
    column.metadata.pathInSchema = [binding.leaf.name] ∧
    column.metadata.physicalType = .int32 ∧ column.metadata.numValues = group.numRows ∧
    column.metadata.codec = 6 ∧ Page.columnSpan snapshot.footer.start column.metadata = some chunk ∧
    Page.readChunk limits.column.framing snapshot.bytes chunk = .ok frames ∧
    (frames.map (pageSlots ∘ Page.Frame.value)).sum = group.numRows.toNat ∧
    List.Forall₂ (fun frame out =>
      PageWire limits layout column.metadata frame.value (frameBody snapshot.bytes frame) out ∧
        out.length = pageSlots frame.value) frames pages ∧
    slots = pages.flatten ∧ slots.length = group.numRows.toNat

end Silmaril.Formats.Parquet.FlatColumn.Zstd
