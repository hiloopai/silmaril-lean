module

public import Silmaril.Formats.Parquet.ListFile.Multi.Defs
public import Silmaril.Formats.Parquet.FlatInt32Writer.Defs

/-! Bounded canonical LIST writes with one complete PLAIN V1 frame per group. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.Writer

open ListPage (Event Row rowEvents)

structure Input where
  name : String
  childName : String
  groups : List (List Row)

structure Limits where
  readback : Multi.Limits := {}
  maxGroups : Nat := 4096
  maxTotalRows : Nat := 1024 * 1024
  maxTotalSlots : Nat := 8 * 1024 * 1024

def Limits.fileLimit (limits : Limits) : Nat :=
  min limits.readback.file.maxFileBytes (2^63 - 1)

namespace PageEncoding

def slotCount (rows : List Row) : Nat :=
  (rows.map fun row => max 1 (row.getD []).length).sum

def valueCount (rows : List Row) : Nat :=
  (rows.map fun row => (row.getD []).countP Option.isSome).sum

def entries (rows : List Row) : List (Nat × Nat × Option Int32) :=
  (rows.flatMap rowEvents).map Event.wire

/-- A singleton RLE run uses two octets at either of the LIST level widths. -/
def runs (width : Nat) (values : List Nat) : List UInt8 :=
  values.flatMap fun value => (Hybrid.Run.repeated 1 value).wire width

def lengthPrefixed (octets : List UInt8) : Bytes :=
  Bytes.ofList (KBytes.unpack 4 octets.length ++ octets)

def body (rows : List Row) : Bytes :=
  let slots := entries rows
  let repetition := lengthPrefixed (runs 1 (slots.map Prod.fst))
  let definition := lengthPrefixed (runs 2 (slots.map fun slot => slot.2.1))
  (repetition.append definition).append (Plain.encodeInt32 (slots.filterMap (·.2.2)))

def bodySize (rows : List Row) : Nat :=
  8 + 4 * slotCount rows + 4 * valueCount rows

def header (rows : List Row) : Page.Header :=
  ⟨bodySize rows, bodySize rows, none, .dataV1 ⟨slotCount rows, 0, 3, 3⟩⟩

def Fits (limits : Multi.Limits) (rows : List Row) : Prop :=
  rows.length ≤ limits.file.page.maxRows ∧
  slotCount rows < Hybrid.runLimit ∧ slotCount rows ≤ limits.maxGroupSlots ∧
  slotCount rows ≤ limits.file.page.levels.values ∧
  2 * slotCount rows ≤ limits.file.page.levels.bytes ∧
  bodySize rows < 2^31 ∧ bodySize rows ≤ limits.file.page.maxBodyBytes ∧
  0 < limits.file.framing.maxPages

instance (limits : Multi.Limits) (rows : List Row) : Decidable (Fits limits rows) := by
  unfold Fits
  infer_instance

inductive Error where
  | budget
  | headerInteger
  | headerLimit
  | decode (cause : ListPage.Error)
  | mismatch
  deriving DecidableEq, Repr

/-- Measure the complete page without allocating either level stream or
the scalar buffer. The two length words fit because the body fits signed i32. -/
def measure (limits : Multi.Limits) (rows : List Row) : Except Error Bytes := do
  if ¬ Fits limits rows then return ← throw .budget
  let some bytes := PlainV1Writer.encodeHeader (slotCount rows) (bodySize rows) | throw .headerInteger
  if limits.file.framing.maxHeaderBytes < bytes.length then return ← throw .headerLimit
  pure bytes

/-- Check the exact nested page before it can be included in a file. -/
def encode (limits : Multi.Limits) (rows : List Row) (headerBytes : Bytes) :
    Except Error PlainV1Writer.Encoded := do
  let page : PlainV1Writer.Encoded := ⟨header rows, headerBytes, body rows⟩
  let decoded ← (ListPage.decodeV1 limits.file.page 0 page.header rows.length page.body).mapError .decode
  if decoded = rows then pure page else throw .mismatch

end PageEncoding

structure GroupIndex where
  rows : Nat
  slots : Nat
  span : Footer.Span
  deriving DecidableEq

def GroupIndex.size (index : GroupIndex) : Nat := index.span.stop - index.span.start

def GroupIndex.chunk (input : Input) (index : GroupIndex) : Footer.ColumnChunk :=
  ⟨0, ⟨.int32, [0, 3], [input.name, "list", input.childName], 0, index.slots, index.size, index.size,
    index.span.start, none, none, none, none⟩, none, none, none, none⟩

namespace Compact

open FlatInt32Writer.Compact (Write field integer octet text listHeader root leaf)

def outer (input : Input) : Write Unit := do
  field 3 5
  integer .i32 1
  field 1 8
  text input.name
  field 1 5
  integer .i32 1
  field 1 5
  integer .i32 3
  -- Field 10 contains the modern LIST arm (3) and its empty marker.
  field 4 12
  field 3 12
  octet 0
  octet 0
  octet 0

def repeatedGroup : Write Unit := do
  field 3 5
  integer .i32 2
  field 1 8
  text "list"
  field 1 5
  integer .i32 1
  octet 0

def chunk (input : Input) (index : GroupIndex) : Write Unit := do
  field 2 6
  integer .i64 0
  field 1 12
  field 1 5
  integer .i32 1
  field 1 9
  listHeader 5 2
  integer .i32 0
  integer .i32 3
  field 1 9
  listHeader 8 3
  text input.name
  text "list"
  text input.childName
  field 1 5
  integer .i32 0
  field 1 6
  integer .i64 index.slots
  field 1 6
  integer .i64 index.size
  field 1 6
  integer .i64 index.size
  field 2 6
  integer .i64 index.span.start
  octet 0
  octet 0

def group (input : Input) (index : GroupIndex) : Write Unit := do
  field 1 9
  listHeader 12 1
  chunk input index
  field 1 6
  integer .i64 index.size
  field 1 6
  integer .i64 index.rows
  octet 0

def footer (input : Input) (groups : List GroupIndex) : Write Unit := do
  field 1 5
  integer .i32 1
  field 1 9
  listHeader 12 4
  root 1
  outer input
  repeatedGroup
  leaf ⟨input.childName, true, ⟨0, 0⟩⟩
  field 1 6
  integer .i64 (groups.map GroupIndex.rows).sum
  field 1 9
  listHeader 12 groups.length
  for index in groups do group input index
  octet 0

def encode (limit : Nat) (input : Input) (groups : List GroupIndex) :
    Except FlatInt32Writer.Compact.Error Bytes :=
  ((footer input groups).run ⟨limit, .empty⟩).map (·.2.bytes)

end Compact

inductive Error where
  | childName
  | schemaBudget
  | groupLimit
  | totalRows
  | totalSlots
  | fileLimit
  | measure (index : Nat) (cause : PageEncoding.Error)
  | page (index : Nat) (cause : PageEncoding.Error)
  | footer (cause : FlatInt32Writer.Compact.Error)
  | layout
  | openReadback (cause : ListFile.OpenError)
  | groupReadback (index : Nat) (cause : Multi.GroupError)
  | readbackMismatch
  deriving DecidableEq, Repr

def Input.totalRows (input : Input) : Nat := (input.groups.map List.length).sum

def Input.totalSlots (input : Input) : Nat := (input.groups.map PageEncoding.slotCount).sum

def checkInput (limits : Limits) (input : Input) : Except Error Unit := do
  if input.childName ≠ "element" then return ← throw .childName
  let compact := limits.readback.file.snapshot.footer.compact
  if compact.maxCollectionSize < 4 || compact.maxBinaryBytes < max 7 input.name.utf8ByteSize then
    return ← throw .schemaBudget
  if limits.maxGroups < input.groups.length || compact.maxCollectionSize < input.groups.length then
    return ← throw .groupLimit
  if limits.maxTotalRows < input.totalRows || 2^63 ≤ input.totalRows then return ← throw .totalRows
  if limits.maxTotalSlots < input.totalSlots then return ← throw .totalSlots

structure PlannedPage where
  index : GroupIndex
  headerBytes : Bytes

/-- Place all chunk spans before creating any body. -/
def place (limits : Limits) : Nat → Nat → List (List Row) → Except Error (List PlannedPage)
  | _, _, [] => .ok []
  | offset, ordinal, rows :: rest => do
    let header ← (PageEncoding.measure limits.readback rows).mapError (.measure ordinal)
    let stop := offset + header.length + PageEncoding.bodySize rows
    if limits.fileLimit < stop + 8 then return ← throw .fileLimit
    let next ← place limits stop (ordinal + 1) rest
    pure (⟨⟨rows.length, PageEncoding.slotCount rows, ⟨offset, stop⟩⟩, header⟩ :: next)

structure GroupPage where
  index : GroupIndex
  page : PlainV1Writer.Encoded

def GroupPage.frame (group : GroupPage) : Page.Frame :=
  let start := group.index.span.start
  let middle := start + group.page.headerBytes.length
  ⟨group.page.header, ⟨start, middle⟩, ⟨middle, group.index.span.stop⟩⟩

def encodePages (limits : Multi.Limits) :
    Nat → List (List Row) → List PlannedPage → Except Error (List GroupPage)
  | _, [], [] => .ok []
  | ordinal, rows :: rest, plan :: tail => do
    let page ← (PageEncoding.encode limits rows plan.headerBytes).mapError (.page ordinal)
    if page.wire.length ≠ plan.index.size then return ← throw .layout
    let groups ← encodePages limits (ordinal + 1) rest tail
    pure (⟨plan.index, page⟩ :: groups)
  | _, _, _ => .error .layout

structure Encoded where
  bytes : Bytes
  footer : Footer.Span
  groups : List GroupPage

def metadata (input : Input) (groups : List GroupPage) : Footer.Metadata :=
  let schema : List Footer.SchemaElement := [FlatInt32Writer.Compact.schemaRoot 1,
    ⟨none, none, some .optional, input.name, some 1⟩,
    ⟨none, none, some .repeated, "list", some 1⟩,
    ⟨some .int32, none, some .optional, input.childName, none⟩]
  let groupMetadata : List Footer.RowGroup := groups.map fun page =>
    ⟨[page.index.chunk input], page.index.size, page.index.rows, none, none⟩
  ⟨1, schema, (groups.map (·.index.rows)).sum, groupMetadata, none⟩

def Contiguous : Nat → List GroupPage → Nat → Prop
  | start, [], stop => start = stop
  | start, group :: rest, stop =>
    group.index.span.start = start ∧ Contiguous group.index.span.stop rest stop

instance instDecidableContiguous (start : Nat) (groups : List GroupPage) (stop : Nat) :
    Decidable (Contiguous start groups stop) :=
  match groups with
  | [] => inferInstanceAs (Decidable (start = stop))
  | group :: rest =>
    letI := instDecidableContiguous group.index.span.stop rest stop
    inferInstanceAs (Decidable (group.index.span.start = start ∧ Contiguous group.index.span.stop rest stop))

def Encoded.Layout (output : Encoded) (limits : Limits) (input : Input) : Prop :=
  output.bytes.length ≤ limits.fileLimit ∧ output.footer.stop + 8 = output.bytes.length ∧
  output.groups.map (fun group => (group.index.rows, group.index.slots)) =
    input.groups.map (fun rows => (rows.length, PageEncoding.slotCount rows)) ∧
  Contiguous 4 output.groups output.footer.start ∧
  Footer.readFooter limits.readback.file.snapshot.footer output.bytes =
    .ok (output.footer, metadata input output.groups) ∧
  ∀ group ∈ output.groups,
    Page.columnSpan output.footer.start (group.index.chunk input).metadata = some group.index.span ∧
    Page.readChunk limits.readback.file.framing output.bytes group.index.span = .ok [group.frame] ∧
    output.bytes.slice? group.frame.payload.start (some group.frame.payload.stop) = some group.page.body

instance (output : Encoded) (limits : Limits) (input : Input) : Decidable (output.Layout limits input) := by
  unfold Encoded.Layout
  infer_instance

def assemble (limits : Limits) (input : Input) : Except Error Encoded := do
  let plan ← place limits 4 0 input.groups
  let start := (plan.getLast?.map (·.index.span.stop)).getD 4
  if limits.fileLimit < start + 8 then return ← throw .fileLimit
  let footerLimit := min (min limits.readback.file.snapshot.footer.maxFooterBytes (2^32 - 1))
    (limits.fileLimit - start - 8)
  let footer ← (Compact.encode footerLimit input (plan.map (·.index))).mapError .footer
  if footerLimit < footer.length then return ← throw .layout
  let groups ← encodePages limits.readback 0 input.groups plan
  let payload := Bytes.ofList (groups.flatMap (·.page.wire.toList))
  if 4 + payload.length ≠ start then return ← throw .layout
  let bytes := (((Footer.magic.append payload).append footer).append
    (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic
  pure ⟨bytes, ⟨start, start + footer.length⟩, groups⟩

def readGroups (limits : Multi.Limits) (checked : ListFile.Checked) :
    Except Error (List (List Row)) :=
  (List.range checked.snapshot.groupCount).mapM fun ordinal =>
    (Multi.readGroup limits.maxGroupSlots checked ordinal).mapError (.groupReadback ordinal)

/-- Return only a file with its exact checked positions and complete native
LIST readback. An absent group sequence and a framed empty group stay distinct. -/
def emit (limits : Limits) (input : Input) : Except Error Encoded := do
  checkInput limits input
  let output ← assemble limits input
  if ¬ output.Layout limits input then return ← throw .layout
  let checked ← (ListFile.openFile limits.readback.file output.bytes).mapError .openReadback
  if ¬ (checked.shape.outer.name = input.name ∧ checked.shape.element.name = input.childName ∧
      checked.snapshot.groupCount = input.groups.length) then return ← throw .readbackMismatch
  let rows ← readGroups limits.readback checked
  if rows = input.groups then pure output else throw .readbackMismatch

end Silmaril.Formats.Parquet.ListFile.Writer
