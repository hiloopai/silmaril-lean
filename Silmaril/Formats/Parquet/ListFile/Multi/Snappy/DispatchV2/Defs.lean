module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.Defs

/-! Per-row-group dispatch for the three checked Snappy V2 LIST profiles. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2

open ListPage (Row)

inductive Profile where
  | plain
  | dictionary
  | fallback
  deriving DecidableEq, Repr

def isPlainData (frame : Page.Frame) : Bool :=
  match frame.value.kind with
  | .dataV2 info => info.encoding == 0
  | _ => false

/-- Select a profile from the original headers. The selection checks no body
and reports no error that could overtake an earlier body failure. -/
def classify : List Page.Frame → Profile
  | first :: data =>
    match first.value.kind with
    | .dictionary _ => if data.any isPlainData then .fallback else .dictionary
    | _ => .plain
  | [] => .plain

inductive GroupError where
  | framing (cause : ListFile.ReadError)
  | plain (cause : Snappy.GroupError)
  | dictionary (cause : DictionaryV1.GroupError)
  | fallback (cause : DictionaryV1.GroupError)
  deriving DecidableEq, Repr

inductive SourceError where
  | openFailure (cause : ListFile.OpenError)
  | groupFailure (ordinal : Nat) (cause : GroupError)
  deriving DecidableEq, Repr

inductive Error where
  | source (cause : SourceError)
  | writer (cause : Arrow.ListInt32.Stream.Writer.Error)
  deriving DecidableEq, Repr

def errors : Snappy.ConversionErrors GroupError SourceError Error :=
  ⟨.openFailure, .groupFailure, .source, .writer⟩

def dictionaryWalk (limits : DictionaryV1.Limits) : DictionaryV1.DataWalk :=
  fun checked column entries => DictionaryV1.readFramesUsing (DictionaryV2.dataReader limits checked column entries)

def readDictionaryGroup (limits : DictionaryV1.Limits) (walk : DictionaryV1.DataWalk)
    (checked : ListFile.Checked) (framed : ListFile.FramedGroup) (expanded : Nat) :
    Except DictionaryV1.GroupError (List Row × Nat) := do
  let chunk ← DictionaryV1.selectFramedChunk framed
  DictionaryV1.readSelectedGroupWith limits walk checked chunk expanded

def readFramedGroup (limits : DictionaryV1.Limits) (checked : ListFile.Checked)
    (framed : ListFile.FramedGroup) (expanded : Nat) : Except GroupError (List Row × Nat) :=
  match classify framed.frames with
  | .plain =>
    if framed.chunk.metadata.dictionaryPageOffset.isSome then .error (.framing .unsupportedOffsets)
    else (Snappy.readFramedGroupFor .v2 limits.snappy checked framed expanded).mapError .plain
  | .dictionary => (readDictionaryGroup limits (dictionaryWalk limits) checked framed expanded).mapError .dictionary
  | .fallback =>
    (readDictionaryGroup limits (DictionaryFallbackV2.walk limits) checked framed expanded).mapError .fallback

/-- Frame the immutable source once and invoke only the selected reader. -/
def readGroup (limits : DictionaryV1.Limits) (checked : ListFile.Checked) (ordinal expanded : Nat) :
    Except GroupError (List Row × Nat) := do
  let framed ← (checked.frameGroupWith 1 true ordinal).mapError .framing
  readFramedGroup limits checked framed expanded

def ProfileWire (limits : DictionaryV1.Limits) (checked : ListFile.Checked) (ordinal : Nat)
    (rows : List Row) (spent : Nat) : Profile → Prop
  | .plain => Snappy.GroupWire limits.snappy checked ordinal rows spent .v2
  | .dictionary => DictionaryV2.GroupWire limits checked ordinal rows spent
  | .fallback => DictionaryFallbackV2.GroupWire limits checked ordinal rows spent

structure GroupWire (limits : DictionaryV1.Limits) (checked : ListFile.Checked) (ordinal : Nat)
    (rows : List Row) (spent : Nat) : Prop where
  data : ∃ framed,
    ListFile.ChunkFrameWire checked ordinal framed 1 ∧
    ProfileWire limits checked ordinal rows spent (classify framed.frames)

def convert (limits : DictionaryV1.Limits) (source : Bytes) : Snappy.ResultWith SourceError Error :=
  Snappy.convertWith errors limits.snappy (readGroup limits) source

abbrev Readback (limits : DictionaryV1.Limits) (source : Bytes) (wire : KBytes) :=
  Snappy.ReadbackWith errors limits.snappy (readGroup limits) (GroupWire limits) source wire

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2
