module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Defs
public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Defs

/-! Opt-in Snappy DATE dictionary data followed by a nonempty PLAIN suffix. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy

open DictionaryChunk (DataPage)

abbrev Limits := Dictionary.Snappy.Limits

inductive GroupError where
  | snappy (cause : Dictionary.Snappy.GroupError)
  | sequence (cause : Fallback.GroupError)
  | plain (page offset : Nat) (cause : ScalarPage.Error)
  deriving DecidableEq, Repr

inductive Error where
  | openFailure (cause : Leaf.Error)
  | groupFailure (index : Nat) (cause : GroupError)
  deriving DecidableEq, Repr

inductive IpcError where
  | source (cause : Error)
  | closed
  | writer (cause : Arrow.DateStream.Writer.Error)
  deriving DecidableEq, Repr

def admits (tag : Int) : Bool := tag == 8 || tag == 0

/-- Retain the header prefix preceding the first unsupported frame so an
earlier phase error keeps priority. No page body is read here. -/
def planPrefix (bound : Bound) :
    List (Page.Frame × Nat) → List DataPage × Option Dictionary.Snappy.GroupError
  | [] => ([], none)
  | (frame, ordinal) :: rest =>
    match Dictionary.Snappy.planDataWith admits bound frame with
    | .error cause => ([], some (Dictionary.Snappy.atFrame ordinal frame cause))
    | .ok page =>
      let (pages, failure) := planPrefix bound rest
      (page :: pages, failure)

/-- Reuse the uncompressed phase rule on the original admitted prefix.
Only errors at an actual earlier frame take precedence over a header failure. -/
def planPages (bound : Bound) (frames : List Page.Frame) : Except GroupError (List DataPage) :=
  let (pages, failure) := planPrefix bound (frames.zipIdx 1)
  match Fallback.checkSequence pages with
  | .error (.prefixEncoding i offset tag) => .error (.sequence (.prefixEncoding i offset tag))
  | .error (.suffixEncoding i offset tag) => .error (.sequence (.suffixEncoding i offset tag))
  | sequence =>
    match failure with
    | some cause => .error (.snappy cause)
    | none => (sequence.mapError .sequence).map fun _ => pages

def checkGroup (limits : Limits) (bound : Bound) (index : Nat) :
    Except GroupError Dictionary.Snappy.CheckedGroup :=
  Dictionary.Snappy.checkGroupWith .snappy (planPages bound) limits bound index

/-- Both branches use the original stored frame and checksum policy. -/
def decodePage (limits : Limits) (source : Bytes) (entries : Array Int32)
    (page : DataPage) (ordinal : Nat) : Except GroupError Slots :=
  if page.params.encoding = 0 then do
    let _ ← (Dictionary.Snappy.verifyData limits source page ordinal).mapError .snappy
    (ScalarPage.decode .int32 page.params limits.scalar
      (Page.Checksum.payloadBytes source page.frame)).mapError (.plain ordinal page.frame.header.start)
  else
    (Dictionary.Snappy.decodePage limits source entries page ordinal).mapError .snappy

def PageWire (limits : Limits) (source : Bytes) (entries : Array Int32) (page : DataPage)
    (slots : Slots) : Prop :=
  slots.length = page.params.numValues ∧
    ((page.params.encoding = 8 ∧ Dictionary.Snappy.PageWire limits source entries page slots) ∨
      (page.params.encoding = 0 ∧ ∃ status,
        Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .ok status ∧
        ScalarPage.decode .int32 page.params limits.scalar
          (Page.Checksum.payloadBytes source page.frame) = .ok slots))

def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots := do
  let checked ← checkGroup limits bound index
  let entries := checked.entries.toArray
  let pages ← (checked.data.zipIdx 1).mapM fun (page, ordinal) =>
    decodePage limits bound.snapshot.bytes entries page ordinal
  return pages.flatten

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Emit native Date32 IPC only after the original selected source reaches EOF. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

end Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy
