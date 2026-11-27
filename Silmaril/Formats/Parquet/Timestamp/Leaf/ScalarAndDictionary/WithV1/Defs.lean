module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.Defs

/-! Opt-in extension admitting modern Snappy and GZIP dictionary-backed V1 groups. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1

open Silmaril.Numeric.Timestamp (Ticks)

inductive GroupError where
  | existing (cause : ScalarAndDictionary.GroupError)
  | mixedVersions (page offset : Nat)
  | snappyV1 (cause : Leaf.Error)
  | gzipV1 (cause : Leaf.Error)
  deriving DecidableEq, Repr

inductive SourceError where
  | groupFailure (index : Nat) (cause : GroupError)
  deriving DecidableEq, Repr

inductive Error where
  | openFailure (cause : Events.ToIpc.Error)
  | source (cause : SourceError)
  | closed
  | writer (cause : Arrow.TimestampStream.Writer.Error)
  deriving DecidableEq, Repr

inductive Version where
  | v1 | v2
  deriving DecidableEq, Repr

def dataVersion (frame : Parquet.Page.Frame) : Option Version :=
  match frame.value.kind with
  | .dataV1 _ => some .v1
  | .dataV2 _ => some .v2
  | _ => none

def firstVersion (framed : Dictionary.FramedChunk) : Version :=
  ((framed.data.findSome? dataVersion).getD .v2)

def hasOtherVersion (version : Version) (frame : Parquet.Page.Frame) : Bool :=
  (dataVersion frame).any (· != version)

def hasPlain (version : Version) (framed : Dictionary.FramedChunk) : Bool :=
  match version with
  | .v1 => framed.data.any Gzip.Dispatch.V1.isPlainV1
  | .v2 => framed.data.any Snappy.Dispatch.V2.isPlainV2

structure Profile where
  version : Version
  fallback : Bool
  deriving DecidableEq, Repr

/-- Inspect retained headers only. Non-data frames keep their strict branch errors.
The first contrary data version has its original ordinal and absolute offset. -/
def classifyFrames (framed : Dictionary.FramedChunk) : Except GroupError Profile :=
  let version := firstVersion framed
  match (framed.data.zipIdx 1).find? (fun pair => hasOtherVersion version pair.1) with
  | some (frame, page) => .error (.mixedVersions page frame.header.start)
  | none => .ok ⟨version, hasPlain version framed⟩

/-- The two dictionary codecs whose original frames can select V1 or V2. -/
inductive Codec where
  | snappy | gzip
  deriving DecidableEq, Repr

def Codec.encoding : Codec → Leaf.ChunkEncoding
  | .snappy => .snappyDictionary
  | .gzip => .gzipDictionaryV2

def Codec.payload : Codec → Payload.Codec
  | .snappy => .snappy
  | .gzip => .gzip

def Codec.dictionaryLimits (codec : Codec) (limits : Limits) : Dictionary.Limits :=
  match codec with
  | .snappy => limits.dictionary.threeCodec.snappy
  | .gzip => limits.dictionary.threeCodec.twoCodec.gzip.dictionary

def Codec.scalarLimits (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) : Leaf.Limits :=
  match codec with
  | .snappy => leafLimits
  | .gzip => limits.dictionary.threeCodec.twoCodec.gzip.withFuel leafLimits

def Codec.readEntries (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Parquet.Page.Frame → Except DictionaryPageError (List Int64) :=
  match codec with
  | .snappy => Dictionary.Snappy.readEntries (codec.dictionaryLimits limits) leafLimits bound
  | .gzip => Dictionary.Gzip.readEntries limits.dictionary.threeCodec.twoCodec.gzip leafLimits bound

def Codec.error (codec : Codec) (version : Version) : Leaf.Error → GroupError :=
  match codec, version with
  | .snappy, .v1 => .snappyV1
  | .gzip, .v1 => .gzipV1
  | .snappy, .v2 => .existing ∘ .snappyDictionary
  | .gzip, .v2 => .existing ∘ .gzipDictionary

def planData (codec : Codec) (profile : Profile) (bound : Bound) :
    Parquet.Page.Frame → Except DictionaryPageError Dictionary.DataPage :=
  match codec, profile.version, profile.fallback with
  | .snappy, .v1, false => Dictionary.Snappy.planData bound
  | .snappy, .v1, true => Dictionary.Snappy.planDataWith Fallback.admits bound
  | .snappy, .v2, false => Dictionary.Snappy.V2.planData bound
  | .snappy, .v2, true => Fallback.Snappy.V2.planData bound
  | .gzip, .v1, false => Dictionary.Gzip.planData bound
  | .gzip, .v1, true => Fallback.Gzip.planData bound
  | .gzip, .v2, false => Dictionary.Gzip.V2.planData bound
  | .gzip, .v2, true => Fallback.Gzip.V2.planData bound

def validate (fallback : Bool) : List Dictionary.DataPage → Except Leaf.Error Unit :=
  if fallback then Fallback.checkSequence else fun _ => .ok ()

def readFramed (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (framed : Dictionary.FramedChunk) (profile : Profile) : Except Leaf.Error (Slots bound) :=
  let checked := Dictionary.checkFramedUsing framed (planData codec profile bound)
    (validate profile.fallback) (codec.readEntries limits leafLimits bound)
  let dictionaryLimits := codec.dictionaryLimits limits
  let scalarLimits := codec.scalarLimits limits leafLimits
  if profile.fallback then
    Fallback.Snappy.readGroupUsing dictionaryLimits scalarLimits bound checked
  else
    Dictionary.Snappy.readGroupUsing dictionaryLimits scalarLimits bound checked

def frameGroup (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error Dictionary.FramedChunk :=
  Dictionary.frameGroupUsing codec.encoding (codec.dictionaryLimits limits) leafLimits bound index

def readDictionary (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except GroupError (Slots bound) := do
  let framed ← (frameGroup codec limits leafLimits bound index).mapError (codec.error .v2)
  let profile ← classifyFrames framed
  (readFramed codec limits leafLimits bound framed profile).mapError (codec.error profile.version)

def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError (Slots bound) := do
  let branch ← (ScalarAndDictionary.route bound index).mapError .existing
  match branch with
  | .dictionary .snappy => readDictionary .snappy limits leafLimits bound index
  | .dictionary .gzip => readDictionary .gzip limits leafLimits bound index
  | _ => (ScalarAndDictionary.readSelected limits leafLimits bound index branch).mapError .existing

def trace (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Events.Cell SourceError :=
  MixedCodec.V2.traceUsing bound (readGroup limits leafLimits bound) .groupFailure

def convert (limits : Limits) (inputLimits : Events.ToIpc.Limits) (output : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Error KBytes := do
  let bound ← (Events.ToIpc.openBound inputLimits input ordinal).mapError .openFailure
  MixedCodec.V2.emitUsing output bound (trace limits inputLimits.leaf bound) .source .closed .writer

def Codec.branch : Codec → ScalarAndDictionary.Branch
  | .snappy => .dictionary .snappy
  | .gzip => .dictionary .gzip

/-- The standalone reader that supplies the selected strict profile. -/
def standalone (codec : Codec) (profile : Profile) (limits : Limits) (leafLimits : Leaf.Limits)
    (bound : Bound) (index : Nat) : Except Leaf.Error (Slots bound) :=
  let snappy := limits.dictionary.threeCodec.snappy
  let gzip := limits.dictionary.threeCodec.twoCodec.gzip
  match codec, profile.version, profile.fallback with
  | .snappy, .v1, false => Dictionary.Snappy.readGroup snappy leafLimits bound index
  | .snappy, .v1, true => Fallback.Snappy.readGroup snappy leafLimits bound index
  | .snappy, .v2, false => Dictionary.Snappy.V2.readGroup snappy leafLimits bound index
  | .snappy, .v2, true => Fallback.Snappy.V2.readGroup snappy leafLimits bound index
  | .gzip, .v1, false => Dictionary.Gzip.readGroup gzip leafLimits bound index
  | .gzip, .v1, true => Fallback.Gzip.readGroup gzip leafLimits bound index
  | .gzip, .v2, false => Dictionary.Gzip.V2.readGroup gzip leafLimits bound index
  | .gzip, .v2, true => Fallback.Gzip.V2.readGroup gzip leafLimits bound index

/-- Original PLAIN dictionary words and the codec-specific integrity witness. -/
def EntriesWire (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (frame : Parquet.Page.Frame) (entries : List Int64) : Prop :=
  let dictionaryLimits := codec.dictionaryLimits limits
  let bounds := Dictionary.Snappy.dictionaryBounds dictionaryLimits (codec.scalarLimits limits leafLimits) frame
  ∃ header expanded,
    frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧ header.numValues ≤ dictionaryLimits.maxEntries ∧
    (match codec with
     | .snappy =>
       (∃ status, Parquet.Page.Checksum.verify bounds.compressedLimit bound.snapshot.bytes frame = .ok status) ∧
       Payload.Decodes frame.value.uncompressedSize .snappy (Leaf.Internal.body bound frame).toList expanded ∧
       expanded.length = frame.value.uncompressedSize ∧ expanded.length ≤ bounds.outputLimit
     | .gzip => Dictionary.Gzip.StoredMember bound frame bounds.compressedLimit bounds.outputLimit expanded) ∧
    Plain.decodeInt64 header.numValues (Bytes.ofList expanded) = .ok entries ∧ entries.length = header.numValues

/-- The original dictionary and data headers, plan, stored bodies and ordered signed slots. -/
def DictionaryWire (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) (slots : Slots bound) : Prop :=
  ∃ (framed : Dictionary.FramedChunk) (profile : Profile) (checked : Dictionary.CheckedChunk) (pages : List (List (Option Int64))),
    frameGroup codec limits leafLimits bound index = .ok framed ∧
    classifyFrames framed = .ok profile ∧
    selectChunkWith codec.encoding leafLimits bound index = .ok framed.chunk ∧
    Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes framed.chunk.span = .ok framed.frames ∧
    Parquet.Page.Chain framed.chunk.span framed.chunk.span.start framed.chunk.span.stop framed.frames ∧
    framed.chunk.span.stop - framed.chunk.span.start ≤ (codec.dictionaryLimits limits).maxChunkBytes ∧
    framed.chunk.column.metadata.dictionaryPageOffset = some (framed.dictionary.header.start : Int) ∧
    framed.chunk.column.metadata.dataPageOffset = (framed.firstData.header.start : Int) ∧
    checked.chunk = framed.chunk ∧ checked.dictionary = framed.dictionary ∧
    List.Forall₂ (fun frame page => planData codec profile bound frame = .ok page ∧ page.frame = frame ∧
      (profile.version = .v1 → Timestamp.Page.parameters bound.binding.leaf bound.levels
        codec.payload.id frame.value = .ok page.params)) framed.data checked.data ∧
    validate profile.fallback checked.data = .ok () ∧
    EntriesWire codec limits leafLimits bound framed.dictionary checked.entries ∧
    (profile.fallback = true → Fallback.OrderedWith 8 checked.data) ∧
    List.Forall₂ (if profile.fallback then
      Fallback.Snappy.DataWire (codec.dictionaryLimits limits) (codec.scalarLimits limits leafLimits)
        bound checked.entries.toArray
      else Dictionary.Snappy.DataWire (codec.dictionaryLimits limits) (codec.scalarLimits limits leafLimits)
        bound checked.entries.toArray) checked.data pages ∧
    slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
    slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
    slots.length = framed.chunk.group.numRows.toNat

def GroupWire (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) (slots : Slots bound) : Prop :=
  (∃ codec, ScalarAndDictionary.route bound index = .ok codec.branch ∧
    DictionaryWire codec limits leafLimits bound index slots) ∨
  ScalarAndDictionary.GroupWire limits leafLimits bound index slots

end Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1
