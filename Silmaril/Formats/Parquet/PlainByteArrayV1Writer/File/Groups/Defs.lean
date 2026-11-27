module

public import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Defs

/-! A shared unannotated flat BYTE_ARRAY leaf with one uncompressed PLAIN
V1 page per original group, including framed zero-row groups. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Groups

open FlatInt32Writer.Compact (ColumnIndex)

structure Input where
  name : String
  layout : FlatColumn.Layout
  groups : List (List (Option Bytes))

def Input.totalRows (input : Input) : Nat := (input.groups.map List.length).sum

def Input.column (input : Input) (span : Footer.Span) : ColumnIndex :=
  ⟨input.name, decide (input.layout = .optional), span⟩

structure Limits where
  file : File.Limits := {}
  maxGroups : Nat := 4096

def Limits.groupLimit (limits : Limits) : Nat :=
  min limits.maxGroups limits.file.snapshot.footer.compact.maxCollectionSize

def Limits.rowLimit (limits : Limits) : Nat := min limits.file.maxFileRows (2^63 - 1)

inductive Error where
  | groupLimit (maximum actual : Nat)
  | rowLimit (maximum actual : Nat)
  | schemaLimit
  | requiredSlot (group : Nat)
  | pageBudget (group : Nat)
  | chunkLimit (group maximum actual : Nat)
  | fileLimit
  | footer (cause : FlatInt32Writer.Compact.Error)
  | page (group : Nat) (cause : PlainByteArrayV1Writer.Error)
  | extent
  | openReadback (cause : Plain.ByteArray.File.Error)
  | footerMismatch
  | groupReadback (cause : FlatColumn.Error Plain.ByteArray.File.PageError)
  | valuesMismatch
  deriving DecidableEq, Repr

structure Plan where
  input : PlainByteArrayV1Writer.Input
  span : Footer.Span

structure Group where
  span : Footer.Span
  rows : Nat
  page : PlainByteArrayV1Writer.Encoded

structure Encoded where
  bytes : Bytes
  footer : Footer.Span
  groups : List Group

def Group.chunk (group : Group) (input : Input) : Footer.ColumnChunk :=
  MixedV1Writer.byteChunk (input.column group.span) group.rows

def Group.rowGroup (group : Group) (input : Input) : Footer.RowGroup :=
  ⟨[group.chunk input], (input.column group.span).size, group.rows, none, none⟩

def metadata (input : Input) (output : Encoded) : Footer.Metadata :=
  ⟨1, [FlatInt32Writer.Compact.schemaRoot 1, MixedV1Writer.byteSchema (input.column ⟨0, 0⟩)],
    (output.groups.map Group.rows).sum,
    output.groups.map (·.rowGroup input), none⟩

/-- Measure and place each page before allocating any page body. -/
def place (limits : Limits) (input : Input) :
    Nat → Nat → List (List (Option Bytes)) → Except Error (List Plan)
  | _, _, [] => .ok []
  | start, ordinal, slots :: rest => do
    let some prepared := File.Input.ofSlots input.name input.layout slots | throw (.requiredSlot ordinal)
    let size ← (MixedV1Writer.measuredBytePage (File.pageLimits limits.file) prepared.page).mapError
      (fun _ => .pageBudget ordinal)
    if limits.file.column.maxChunkBytes < size then
      throw (.chunkLimit ordinal limits.file.column.maxChunkBytes size)
    let stop := start + size
    if File.fileLimit limits.file < stop + 8 then throw .fileLimit
    let tail ← place limits input stop (ordinal + 1) rest
    return ⟨prepared.page, ⟨start, stop⟩⟩ :: tail

def assemble (limits : Limits) (input : Input) : Except Error Encoded := do
  let plans ← place limits input 4 0 input.groups
  let start := (plans.getLast?.map (·.span.stop)).getD 4
  if File.fileLimit limits.file < start + 8 then throw .fileLimit
  let cap := File.footerLimit limits.file start
  let indexed := plans.map fun plan => (plan.input.numValues, [input.column plan.span])
  let footer ← (FlatInt32Writer.Compact.encodeGroupsFor 6 MixedV1Writer.Compact.byteLeaf cap
    [input.column ⟨0, 0⟩] indexed).mapError .footer
  let groups ← plans.zipIdx.mapM fun (plan, ordinal) => do
    let page ← (PlainByteArrayV1Writer.emit (File.pageLimits limits.file) plan.input).mapError (.page ordinal)
    if page.wire.length ≠ plan.span.stop - plan.span.start then throw .extent
    return (⟨plan.span, plan.input.numValues, page⟩ : Group)
  let data := groups.foldl (fun bytes group => bytes.append group.page.wire) Footer.magic
  let bytes := ((data.append footer).append
    (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic
  return ⟨bytes, ⟨start, start + footer.length⟩, groups⟩

/-- The page spans partition the original data area in group order. -/
def Contiguous : Nat → List Group → Nat → Prop
  | start, [], stop => start = stop
  | start, group :: rest, stop =>
    group.span.start = start ∧ group.span.stop = start + group.page.wire.length ∧
      Contiguous group.span.stop rest stop

instance instDecidableContiguous : (start : Nat) → (groups : List Group) → (stop : Nat) →
    Decidable (Contiguous start groups stop)
  | start, [], stop => inferInstanceAs (Decidable (start = stop))
  | start, group :: rest, stop =>
    letI := instDecidableContiguous group.span.stop rest stop
    inferInstanceAs (Decidable (group.span.start = start ∧
      group.span.stop = start + group.page.wire.length ∧ Contiguous group.span.stop rest stop))

/-- The sole chunk's exact span contains exactly the emitted page. -/
def Group.Wire (group : Group) (input : Input) (limits : Limits) (bytes : Bytes)
    (footerStart : Nat) : Prop :=
  Page.columnSpan footerStart (group.chunk input).metadata = some group.span ∧
    Page.readChunk limits.file.column.framing bytes group.span =
      .ok [MixedV1Writer.frame group.span group.page] ∧
    Footer.fileBytes bytes group.span.start group.span.stop = group.page.wire

instance (group : Group) (input : Input) (limits : Limits) (bytes : Bytes) (footerStart : Nat) :
    Decidable (group.Wire input limits bytes footerStart) := by
  unfold Group.Wire
  infer_instance

def Encoded.Checked (output : Encoded) (limits : Limits) (input : Input) : Prop :=
  output.bytes.length ≤ File.fileLimit limits.file ∧
    output.groups.map Group.rows = input.groups.map List.length ∧
    Contiguous 4 output.groups output.footer.start ∧
    ∀ group ∈ output.groups, group.Wire input limits output.bytes output.footer.start

instance (output : Encoded) (limits : Limits) (input : Input) : Decidable (output.Checked limits input) := by
  unfold Encoded.Checked
  infer_instance

def certify (limits : Limits) (input : Input) (output : Encoded) : Except Error Unit := do
  let checked ← (Plain.ByteArray.File.openFile limits.file output.bytes input.name input.layout).mapError
    .openReadback
  if checked.snapshot.footer ≠ output.footer ∨ checked.snapshot.metadata ≠ metadata input output then
    throw .footerMismatch
  let slots ← ((List.range checked.snapshot.groupCount).mapM (checked.readGroup limits.file)).mapError
    .groupReadback
  if slots ≠ input.groups then throw .valuesMismatch

/-- Publish the full file after exact footer, frame, and indexed slot checks.
An empty plan writes only the schema. Empty groups still get a V1 page. -/
def emit (limits : Limits) (input : Input) : Except Error Encoded := do
  if limits.groupLimit < input.groups.length then throw (.groupLimit limits.groupLimit input.groups.length)
  if limits.rowLimit < input.totalRows then throw (.rowLimit limits.rowLimit input.totalRows)
  let compact := limits.file.snapshot.footer.compact
  let rootName := (FlatInt32Writer.Compact.schemaRoot 1).name
  if compact.maxCollectionSize < 2 ||
      max rootName.utf8ByteSize input.name.utf8ByteSize > compact.maxBinaryBytes then throw .schemaLimit
  let output ← assemble limits input
  certify limits input output
  if output.Checked limits input then return output else throw .extent

end Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Groups
