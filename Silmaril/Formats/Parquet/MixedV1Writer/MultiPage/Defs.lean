module

public import Silmaril.Formats.Parquet.MixedV1Writer.Multi.Defs

/-! Bounded uncompressed PLAIN V1 mixed files with independent page cuts. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.MultiPage

open Int32ByteArrayGroup (Field Row Selection)
open FlatInt32Writer.Compact (ColumnIndex)

/-- Page inputs are in logical slot order in each column. Their cuts may differ. -/
structure Group where
  integers : List PlainV1Writer.Input
  octets : List PlainByteArrayV1Writer.Input

structure Input where
  intField : Field
  byteField : Field
  groups : List Group

structure Limits where
  file : Multi.Limits
  maxPagesPerChunk : Nat
  maxPages : Nat

inductive Error where
  | groupLimit
  | rowLimit
  | chunkPageLimit
  | pageLimit
  | schemaOrCuts
  | fileLimit
  | measure (group : Nat) (column : Selection) (page : Nat) (cause : MixedV1Writer.Error)
  | emitPage (group : Nat) (column : Selection) (page : Nat) (cause : MixedV1Writer.Error)
  | footer (cause : FlatInt32Writer.Compact.Error)
  | extent
  | readback (cause : Multi.Error)
  deriving DecidableEq, Repr

def Group.intCuts (group : Group) : List Nat := group.integers.map PlainV1Writer.Input.numValues

def Group.byteCuts (group : Group) : List Nat := group.octets.map PlainByteArrayV1Writer.Input.numValues

def Group.intSlots (group : Group) : List (Option Int32) := group.integers.flatMap PlainV1Writer.Input.slots

def Group.byteSlots (group : Group) : List (Option Bytes) := group.octets.flatMap PlainByteArrayV1Writer.Input.slots

def Group.rowCount (group : Group) : Nat := group.intCuts.sum

def Group.pageCount (group : Group) : Nat := group.integers.length + group.octets.length

def Group.rows (group : Group) : List Row := group.intSlots.zip group.byteSlots

/-- The sole zero-slot page form is one explicit page in an empty chunk. -/
def ValidCuts (cuts : List Nat) : Prop := cuts = [0] ∨ cuts ≠ [] ∧ ∀ count ∈ cuts, 0 < count

instance (cuts : List Nat) : Decidable (ValidCuts cuts) := by
  unfold ValidCuts
  infer_instance

def Group.Matches (group : Group) (intField byteField : Field) : Prop :=
  group.rowCount = group.byteCuts.sum ∧ ValidCuts group.intCuts ∧ ValidCuts group.byteCuts ∧
  (∀ page ∈ group.integers,
    page.schema = (if intField.layout = .optional then ⟨0, 1⟩ else ⟨0, 0⟩)) ∧
  (∀ page ∈ group.octets, page.schema = (if byteField.layout = .optional then ⟨0, 1⟩ else ⟨0, 0⟩))

instance (group : Group) (intField byteField : Field) : Decidable (group.Matches intField byteField) := by
  unfold Group.Matches
  infer_instance

def Input.Valid (input : Input) (limits : Limits) : Prop :=
  input.intField.name ≠ "" ∧ input.byteField.name ≠ "" ∧ input.intField.name ≠ input.byteField.name ∧
  3 ≤ limits.file.writer.footer.compact.maxCollectionSize ∧
  input.intField.name.utf8ByteSize ≤ limits.file.writer.footer.compact.maxBinaryBytes ∧
  input.byteField.name.utf8ByteSize ≤ limits.file.writer.footer.compact.maxBinaryBytes ∧
  ∀ group ∈ input.groups, group.Matches input.intField input.byteField

instance (input : Input) (limits : Limits) : Decidable (input.Valid limits) := by
  unfold Input.Valid
  infer_instance

def Input.totalRows (input : Input) : Nat := (input.groups.map Group.rowCount).sum

def Input.totalPages (input : Input) : Nat := (input.groups.map Group.pageCount).sum

def Input.ChunkPageBound (input : Input) (limits : Limits) : Prop :=
  ∀ group ∈ input.groups,
    group.integers.length ≤ limits.maxPagesPerChunk ∧ group.octets.length ≤ limits.maxPagesPerChunk

instance (input : Input) (limits : Limits) : Decidable (input.ChunkPageBound limits) := by
  unfold Input.ChunkPageBound
  infer_instance

/-- Apply count and layout checks before measuring or allocating page bodies. -/
def admit (limits : Limits) (input : Input) : Except Error Unit :=
  if input.groups = [] ∨ input.groups.length > limits.file.maxGroups ∨
      input.groups.length > limits.file.writer.footer.compact.maxCollectionSize then .error .groupLimit
  else if input.totalRows > limits.file.maxTotalRows ∨ input.totalRows ≥ 2 ^ 63 then .error .rowLimit
  else if ¬ input.ChunkPageBound limits then .error .chunkPageLimit
  else if input.totalPages > limits.maxPages then .error .pageLimit
  else if ¬ input.Valid limits then .error .schemaOrCuts
  else .ok ()

def measureChunk {α : Type} (measure : α → Except MixedV1Writer.Error Nat)
    (group : Nat) (column : Selection) (pages : List α) : Except Error Nat := do
  let sizes ← pages.zipIdx.mapM fun (page, ordinal) => (measure page).mapError (.measure group column ordinal)
  return sizes.sum

/-- Place both chunks of every group using bounded header/body measurements.
The Compact footer can be sized before materializing the page bodies. -/
def place (order : Order) (limits : Limits) (input : Input) :
    Nat → Nat → List Group → Except Error (List Compact.GroupIndex)
  | _, _, [] => .ok []
  | offset, ordinal, group :: rest => do
    let intSize ← measureChunk
      (fun page => (FlatInt32Writer.measuredPage limits.file.writer.intPage page).mapError (fun _ => .intBudget))
      ordinal .int32 group.integers
    let byteSize ← measureChunk (measuredBytePage limits.file.writer.bytePage) ordinal .byteArray group.octets
    let (firstSize, secondSize) := order.arrange intSize byteSize
    let middle := offset + firstSize
    let stop := middle + secondSize
    if stop + 8 > limits.file.fileLimit then throw .fileLimit
    let (ints, octets) := order.arrange (⟨offset, middle⟩ : Footer.Span) ⟨middle, stop⟩
    let tail ← place order limits input stop (ordinal + 1) rest
    return ⟨group.rowCount, columnIndex input.intField ints, columnIndex input.byteField octets⟩ :: tail

abbrev EncodedPage := PlainV1Writer.Encoded

structure Chunks where
  index : Compact.GroupIndex
  integers : List EncodedPage
  octets : List EncodedPage

def emitChunks (limits : Limits) : Nat → List Group → List Compact.GroupIndex → Except Error (List Chunks)
  | _, [], [] => .ok []
  | ordinal, group :: rest, index :: indices => do
    let integers ← group.integers.zipIdx.mapM fun (page, pageIndex) =>
      (PlainV1Writer.emit limits.file.writer.intPage page).mapError
        (fun cause => .emitPage ordinal .int32 pageIndex (.intPage cause))
    let octets ← group.octets.zipIdx.mapM fun (page, pageIndex) =>
      (PlainByteArrayV1Writer.emit limits.file.writer.bytePage page).mapError
        (fun cause => .emitPage ordinal .byteArray pageIndex (.bytePage cause))
    let tail ← emitChunks limits (ordinal + 1) rest indices
    return ⟨index, integers, octets⟩ :: tail
  | _, _, _ => .error .extent

def Chunks.wire (group : Chunks) (order : Order) : List UInt8 :=
  (order.columns group.integers group.octets).flatten.flatMap fun page =>
    page.headerBytes.toList ++ page.body.toList

structure Encoded where
  bytes : Bytes
  footer : Footer.Span
  groups : List Chunks

def Input.intIndex (input : Input) : ColumnIndex := columnIndex input.intField ⟨0, 0⟩

def Input.byteIndex (input : Input) : ColumnIndex := columnIndex input.byteField ⟨0, 0⟩

def metadata (order : Order) (input : Input) (groups : List Chunks) : Footer.Metadata :=
  let rows := groups.map fun group => group.index.rows
  let entries := groups.map fun chunks =>
    let group := chunks.index
    ⟨order.columns (group.ints.metadata group.rows) (byteChunk group.octets group.rows),
      group.ints.size + group.octets.size, group.rows, none, none⟩
  ⟨1, FlatInt32Writer.Compact.schemaRoot 2 :: order.columns input.intIndex.schema (byteSchema input.byteIndex),
    rows.sum, entries, none⟩

def contiguous (order : Order) (start : Nat) : List Chunks → Nat → Bool
  | [], stop => start == stop
  | group :: rest, stop =>
    let (first, second) := group.index.spans order
    first.start == start && second.start == first.stop && contiguous order second.stop rest stop

/-- The first chunk starts after PAR1. Chunks and successive groups adjoin,
and the last chunk ends where the footer begins. -/
def Contiguous (order : Order) (start : Nat) (groups : List Chunks) (stop : Nat) : Prop :=
  contiguous order start groups stop = true

instance (order : Order) (start : Nat) (groups : List Chunks) (stop : Nat) :
    Decidable (Contiguous order start groups stop) :=
  inferInstanceAs (Decidable (contiguous order start groups stop = true))

def frames : Nat → List EncodedPage → List Page.Frame
  | _, [] => []
  | offset, page :: rest =>
    let stop := offset + page.headerBytes.length + page.body.length
    frame ⟨offset, stop⟩ page :: frames stop rest

def pageRows (page : EncodedPage) : Option Nat :=
  match page.header.kind with
  | .dataV1 header => some header.numValues
  | _ => none

def framingLimits (limits : PlainV1Writer.Limits) (count : Nat) : Page.Limits :=
  ⟨limits.headerBytes, count, limits.header⟩

/-- Reparse the original chunk and check every indexed header and body slice. -/
def ColumnChecked (limits : Page.Limits) (file : Bytes) (footerStart : Nat)
    (column : Footer.ColumnMetadata) (span : Footer.Span) (pages : List EncodedPage) : Prop :=
  let expected := frames span.start pages
  Page.columnSpan footerStart column = some span ∧
  Page.readChunk limits file span = .ok expected ∧
  ∀ entry ∈ expected.zip pages,
    Footer.fileBytes file entry.1.header.start entry.1.header.stop = entry.2.headerBytes ∧
    Footer.fileBytes file entry.1.payload.start entry.1.payload.stop = entry.2.body

instance (limits : Page.Limits) (file : Bytes) (footerStart : Nat)
    (column : Footer.ColumnMetadata) (span : Footer.Span) (pages : List EncodedPage) :
    Decidable (ColumnChecked limits file footerStart column span pages) := by
  unfold ColumnChecked
  infer_instance

def PageByteBound (limits : PlainV1Writer.Limits) (page : EncodedPage) : Prop :=
  page.headerBytes.length ≤ limits.headerBytes ∧
    page.body.length ≤ limits.scalar.compressedBytes ∧ page.body.length ≤ limits.scalar.uncompressedBytes

instance (limits : PlainV1Writer.Limits) (page : EncodedPage) : Decidable (PageByteBound limits page) := by
  unfold PageByteBound
  infer_instance

def Encoded.Checked (output : Encoded) (order : Order) (limits : Limits) (input : Input) : Prop :=
  output.bytes.length ≤ limits.file.fileLimit ∧ output.bytes.length = output.footer.stop + 8 ∧
    output.footer.stop - output.footer.start ≤ limits.file.writer.footer.maxFooterBytes ∧
    output.groups.map (·.index.rows) = input.groups.map Group.rowCount ∧
    output.groups.map (fun group => group.integers.map pageRows) =
      input.groups.map (fun group => group.intCuts.map some) ∧
    output.groups.map (fun group => group.octets.map pageRows) =
      input.groups.map (fun group => group.byteCuts.map some) ∧
    Contiguous order 4 output.groups output.footer.start ∧
    Footer.readFooter limits.file.writer.footer output.bytes = .ok (output.footer, metadata order input output.groups) ∧
    ∀ group ∈ output.groups,
      (∀ page ∈ group.integers, PageByteBound limits.file.writer.intPage page) ∧
      (∀ page ∈ group.octets, PageByteBound limits.file.writer.bytePage.page page) ∧
      ColumnChecked (framingLimits limits.file.writer.intPage limits.maxPagesPerChunk) output.bytes output.footer.start
        (group.index.ints.metadata group.index.rows).metadata group.index.ints.span group.integers ∧
      ColumnChecked (framingLimits limits.file.writer.bytePage.page limits.maxPagesPerChunk) output.bytes
        output.footer.start (byteChunk group.index.octets group.index.rows).metadata group.index.octets.span group.octets

instance (output : Encoded) (order : Order) (limits : Limits) (input : Input) :
    Decidable (output.Checked order limits input) := by
  unfold Encoded.Checked
  infer_instance

def assemble (order : Order) (limits : Limits) (input : Input) : Except Error Encoded := do
  let indices ← place order limits input 4 0 input.groups
  let start := (indices.getLast?.map (fun index => (index.spans order).2.stop)).getD 4
  if start + 8 > limits.file.fileLimit then throw .fileLimit
  let cap := min (min limits.file.writer.footer.maxFooterBytes (2 ^ 32 - 1)) (limits.file.fileLimit - start - 8)
  let footer ← (Compact.encodeGroupsOrdered order cap input.intIndex input.byteIndex indices).mapError .footer
  if footer.length > cap then throw .extent
  let groups ← emitChunks limits 0 input.groups indices
  let payload := Bytes.ofList (groups.flatMap (·.wire order))
  if 4 + payload.length ≠ start then throw .extent
  let bytes := (((Footer.magic.append payload).append footer).append
    (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic
  return ⟨bytes, ⟨start, start + footer.length⟩, groups⟩

/-- Package the flattened slots for the shared group equality checker. -/
def Group.observation (group : Group) : Multi.Group :=
  ⟨.optional group.intSlots, .optional group.byteSlots⟩

def certify (limits : Limits) (input : Input) (output : Encoded) : Except Multi.Error Unit := do
  let readback := limits.file.writer.readback
  let opened ← (Int32ByteArrayGroup.openFile readback output.bytes input.intField input.byteField).mapError .openReadback
  if opened.snapshot.groupCount = input.groups.length then
    Multi.checkGroups readback opened 0 (input.groups.map Group.observation)
  else .error .extent

/-- Admit one or more groups, then return a complete file after exact wire
checks and checked readback of each original logical group. -/
def emit (order : Order) (limits : Limits) (input : Input) : Except Error Encoded := do
  admit limits input
  let output ← assemble order limits input
  if output.Checked order limits input then
    (certify limits input output).mapError .readback |>.map fun _ => output
  else throw .extent

end Silmaril.Formats.Parquet.MixedV1Writer.MultiPage
