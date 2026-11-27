module

public import Silmaril.Formats.Parquet.Footer.Defs
public import Silmaril.Formats.Parquet.Footer.PageLessInt32.Defs
public import Silmaril.Formats.Parquet.Footer.PageLessRecursive.Defs
public import Silmaril.Formats.Parquet.Reader.Defs

/-! Bind a finite immutable Parquet byte snapshot to a typed Arrow reader.
The footer is checked at open. The supplied group decoder runs only when
its zero-based footer index is pulled. -/

public section

namespace Silmaril.Formats.Parquet.Snapshot

open Silmaril.Relational Silmaril.Formats.Arrow

structure Limits where
  footer : Footer.Limits := {}
  maxSchemaDepth : Nat := 32

inductive Error (Failure : Type*) where
  | input (reason : Failure)
  | footer (reason : Footer.Error)
  | invalidMetadata (reason : Footer.ValidationError)
  | schema (reason : Failure)
  | groupIndex (index : Nat)
  | decode (index : Nat) (reason : Failure)
  | rowCount (index expected actual : Nat)
  deriving DecidableEq, Repr

/-- A single byte value with its checked plaintext footer and a dense lookup
array in footer order. The constructor is private. -/
structure Checked where
  private mk ::
  bytes : Bytes
  footer : Footer.Span
  metadata : Footer.Metadata
  private groups : Array Footer.RowGroup
  private pageLessTimestamp : Bool
  private pageLessRecursive : Bool

def check {Failure : Type*} (limits : Limits) (bytes : Bytes) : Except (Error Failure) Checked := do
  let (footer, metadata) ← (Footer.readFooter limits.footer bytes).mapError .footer
  (Footer.validate footer.start limits.maxSchemaDepth metadata).mapError .invalidMetadata
  pure ⟨bytes, footer, metadata, metadata.rowGroups.toArray, false, false⟩

/-- Explicitly admit the pinned zero-page INT32 convention. Retain the original
unfiltered metadata and bytes in footer order. -/
def checkPageLessInt32 (limits : Limits) (bytes : Bytes) :
    Except Footer.PageLessInt32.Error Checked := do
  let (footer, metadata) ← (Footer.readFooter limits.footer bytes).mapError .footer
  Footer.PageLessInt32.validate limits.footer limits.maxSchemaDepth bytes footer metadata
  pure ⟨bytes, footer, metadata, metadata.rowGroups.toArray, false, false⟩

/-- An exact zero-byte TIMESTAMP group is available only through this profile. -/
def checkPageLessTimestamp (limits : Limits) (bytes : Bytes) :
    Except Footer.PageLessTimestamp.Error Checked := do
  let (footer, metadata) ← (Footer.readFooter limits.footer bytes).mapError .footer
  Footer.PageLessTimestamp.validate limits.footer limits.maxSchemaDepth bytes footer metadata
  pure ⟨bytes, footer, metadata, metadata.rowGroups.toArray, true, false⟩

def Checked.admitsPageLessTimestamp (snapshot : Checked) (group : Footer.RowGroup) : Bool :=
  snapshot.pageLessTimestamp && Footer.PageLessTimestamp.isPageLess group

inductive RecursiveError where
  | original (cause : Error Unit)
  | pageLess (cause : Footer.PageLessRecursive.Error)
  deriving DecidableEq, Repr

/-- Retain ordinary strict admission. Only a failed strict interval check with
an exact typed empty-group candidate can enter the raw no-page policy. -/
def checkRecursive (limits : Limits) (bytes : Bytes) : Except RecursiveError Checked := do
  let (footer, metadata) ← (Footer.readFooter limits.footer bytes).mapError
    (fun error => .original (.footer error))
  match Footer.validate footer.start limits.maxSchemaDepth metadata with
  | .ok () =>
    return ⟨bytes, footer, metadata, metadata.rowGroups.toArray, false, false⟩
  | .error reason =>
    if reason ≠ .pageInterval ||
        !metadata.rowGroups.any Footer.PageLessRecursive.isPageLess then
      throw (.original (.invalidMetadata reason))
    (Footer.PageLessRecursive.validate limits.footer limits.maxSchemaDepth bytes footer metadata).mapError .pageLess
    return ⟨bytes, footer, metadata, metadata.rowGroups.toArray, false, true⟩

def Checked.admitsPageLessRecursive (snapshot : Checked) (group : Footer.RowGroup) : Bool :=
  snapshot.pageLessRecursive && Footer.PageLessRecursive.isPageLess group

def Checked.groupCount (snapshot : Checked) : Nat := snapshot.groups.size

def Checked.groupAt (snapshot : Checked) (index : Nat) : Option Footer.RowGroup :=
  snapshot.groups[index]?

variable {Id Kind Failure : Type*} {Value : Kind → Type*} {schema : Scan.Schema Id Kind}

/-- Decode a single indexed group against the same bytes and footer as open.
The capability supplies the physical decoding and typed schema interpretation.
The adapter independently checks the number of returned rows. -/
abbrev DecodeGroup (schema : Scan.Schema Id Kind) (Value : Kind → Type*) (Failure : Type*) :=
  Checked → Nat → Footer.RowGroup → Except Failure (Reader.RowGroup schema Value)

/-- Check the requested typed schema against the file metadata and configure
the per-group decoder. Binding sees metadata before any group is read. -/
abbrev Bind (schema : Scan.Schema Id Kind) (Value : Kind → Type*) (Failure : Type*) :=
  Footer.Metadata → Except Failure (DecodeGroup schema Value Failure)

@[expose] def Checked.readGroup (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (index : Nat) : Except (Error Failure) (Reader.RowGroup schema Value) :=
  match snapshot.groupAt index with
  | none => .error (.groupIndex index)
  | some group =>
    match decode snapshot index group with
    | .error reason => .error (.decode index reason)
    | .ok rows =>
      if rows.length = group.numRows.toNat then .ok rows
      else .error (.rowCount index group.numRows.toNat rows.length)

/-- The cursor is the unread suffix of this snapshot's footer indices.
Early close releases the cursor without decoding the tail. An immutable
in-memory snapshot has no failing cleanup operation. -/
@[expose] def Checked.source (snapshot : Checked) (decode : DecodeGroup schema Value Failure) :
    Reader.Source Nat schema Value (Error Failure) :=
  ⟨List.range snapshot.groupCount, snapshot.readGroup decode, fun _ => .ok ()⟩

/-- Pull a checked source through its final EOF, unless an indexed read fails. -/
@[expose] def Checked.readAll (snapshot : Checked) (decode : DecodeGroup schema Value Failure) :
    Events.EventStream Id Value (Error Failure) :=
  Reader.readAll (.ok ⟨schema, snapshot.source decode⟩)

def openSource (limits : Limits) (bind : Bind schema Value Failure) (bytes : Bytes) :
    Except (Error Failure) (Reader.Source Nat schema Value (Error Failure)) :=
  match check limits bytes with
  | .error error => .error error
  | .ok snapshot =>
    match bind snapshot.metadata with
    | .error reason => .error (.schema reason)
    | .ok decode => .ok (snapshot.source decode)

/-- Use the common Arrow lifetime: an open failure has no schema, a read
failure consumes the live cursor, and a caller may close before EOF. -/
def batchReader (limits : Limits) (bind : Bind schema Value Failure) :
    Events.BatchReader Bytes Id Value (Error Failure)
      (fun s => Reader.Source Nat s Value (Error Failure)) :=
  Reader.batchReader (fun bytes => (openSource limits bind bytes).map fun source => ⟨schema, source⟩)

/-- Open immutable bytes and pull through EOF or the first read failure.
The opened group count determines the pull budget. -/
@[expose] def readAll (limits : Limits) (bind : Bind schema Value Failure) (bytes : Bytes) :
    Events.EventStream Id Value (Error Failure) :=
  Reader.readAll ((openSource limits bind bytes).map fun source => ⟨schema, source⟩)

end Silmaril.Formats.Parquet.Snapshot
