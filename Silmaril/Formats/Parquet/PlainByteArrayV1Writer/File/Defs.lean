module

public import Silmaril.Formats.Parquet.MixedV1Writer.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.File.Defs

/-! One unannotated flat BYTE_ARRAY leaf with one uncompressed PLAIN V1
page in a single row group. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File

open FlatInt32Writer.Compact (ColumnIndex)

abbrev Limits := Plain.ByteArray.File.Limits

structure Input where
  name : String
  page : PlainByteArrayV1Writer.Input

def Input.layout (input : Input) : FlatColumn.Layout :=
  match input.page with
  | .required _ => .required
  | .optional _ => .optional

def Input.column (input : Input) (span : Footer.Span) : ColumnIndex :=
  ⟨input.name, decide (input.layout = .optional), span⟩

structure Encoded where
  bytes : Bytes
  footer : Footer.Span
  page : PlainByteArrayV1Writer.Encoded

def Encoded.pageSpan (output : Encoded) : Footer.Span :=
  ⟨4, 4 + output.page.wire.length⟩

def rowGroup (input : Input) (output : Encoded) : Footer.RowGroup :=
  let column := input.column output.pageSpan
  ⟨[MixedV1Writer.byteChunk column input.page.numValues], column.size, input.page.numValues, none, none⟩

def metadata (input : Input) (output : Encoded) : Footer.Metadata :=
  ⟨1, [FlatInt32Writer.Compact.schemaRoot 1, MixedV1Writer.byteSchema (input.column output.pageSpan)],
    input.page.numValues, [rowGroup input output], none⟩

inductive Error where
  | rowLimit (maximum actual : Nat)
  | schemaLimit
  | pageBudget
  | chunkLimit (maximum actual : Nat)
  | fileLimit
  | footer (cause : FlatInt32Writer.Compact.Error)
  | page (cause : PlainByteArrayV1Writer.Error)
  | extent
  | openReadback (cause : Plain.ByteArray.File.Error)
  | footerMismatch
  | groupReadback (cause : FlatColumn.Error Plain.ByteArray.File.PageError)
  | valuesMismatch
  deriving DecidableEq, Repr

def pageLimits (limits : Limits) : PlainByteArrayV1Writer.Limits :=
  ⟨⟨limits.column.framing.header, limits.column.framing.maxHeaderBytes, limits.scalar⟩, limits.values⟩

def fileLimit (limits : Limits) : Nat := min limits.maxFileBytes (2^63 - 1)

def footerLimit (limits : Limits) (stop : Nat) : Nat :=
  min (min limits.snapshot.footer.maxFooterBytes (2^32 - 1)) (fileLimit limits - stop - 8)

def serializeFooter (input : Input) (limits : Limits) (span : Footer.Span) :
    Except FlatInt32Writer.Compact.Error Bytes :=
  let column := input.column span
  FlatInt32Writer.Compact.encodeGroupsFor 6 MixedV1Writer.Compact.byteLeaf (footerLimit limits span.stop)
    [column] [(input.page.numValues, [column])]

def wrap (page : PlainByteArrayV1Writer.Encoded) (footer : Bytes) : Encoded :=
  let stop := 4 + page.wire.length
  let bytes := (((Footer.magic.append page.wire).append footer).append
    (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic
  ⟨bytes, ⟨stop, stop + footer.length⟩, page⟩

/-- Fix the chunk extent and budget the Compact footer before building
the page body. Every input, including zero rows, uses one framed page. -/
def assemble (limits : Limits) (input : Input) : Except Error Encoded := do
  if limits.maxFileRows < input.page.numValues then throw (.rowLimit limits.maxFileRows input.page.numValues)
  let compact := limits.snapshot.footer.compact
  let rootName := (FlatInt32Writer.Compact.schemaRoot 1).name
  if compact.maxCollectionSize < 2 ||
      max rootName.utf8ByteSize input.name.utf8ByteSize > compact.maxBinaryBytes then throw .schemaLimit
  let pageSize ← (MixedV1Writer.measuredBytePage (pageLimits limits) input.page).mapError (fun _ => .pageBudget)
  if limits.column.maxChunkBytes < pageSize then throw (.chunkLimit limits.column.maxChunkBytes pageSize)
  let stop := 4 + pageSize
  if fileLimit limits < stop + 8 then throw .fileLimit
  let footer ← (serializeFooter input limits ⟨4, stop⟩).mapError .footer
  let page ← (PlainByteArrayV1Writer.emit (pageLimits limits) input.page).mapError .page
  if page.wire.length = pageSize then return wrap page footer else throw .extent

/-- Publish only a complete file with the exact singleton footer and
indexed readback of every original slot. -/
def emit (limits : Limits) (input : Input) : Except Error Encoded := do
  let output ← assemble limits input
  let checked ← (Plain.ByteArray.File.openFile limits output.bytes input.name input.layout).mapError .openReadback
  if checked.snapshot.footer ≠ output.footer ∨ checked.snapshot.metadata ≠ metadata input output then
    throw .footerMismatch
  let slots ← (checked.readGroup limits 0).mapError .groupReadback
  if slots = input.page.slots then return output else throw .valuesMismatch

end Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File
