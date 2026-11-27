module

meta import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain (Limits GroupError IpcError)

private meta inductive Profile where
  | plain | dictionary | fallback
  deriving DecidableEq, Repr

private meta def agrees (input : Bytes) (ordinal index : Nat) (choice : Profile)
    (limits : Limits := {}) : Bool := Id.run do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal | return false
  let expected : Except GroupError Date.Leaf.Slots := match choice with
    | .plain => (Date.Leaf.Gzip.V2.readGroup (Date.Leaf.Gzip.Dispatch.V2.WithPlain.plainLimits limits)
        bound index).mapError .plain
    | .dictionary =>
      ((Date.Leaf.Dictionary.Gzip.V2.readGroup limits bound index).mapError
        Date.Leaf.Gzip.Dispatch.V2.dictionaryError).mapError .dictionaryBacked
    | .fallback => (Date.Leaf.Fallback.Gzip.V2.readGroup limits bound index).mapError .dictionaryBacked
  return match Date.Leaf.Gzip.Dispatch.V2.WithPlain.readGroup limits bound index, expected with
  | .ok actual, .ok value => actual == value
  | .error actual, .error cause => actual == cause
  | _, _ => false

private meta def checkedFrames (limits : Limits) (bound : Date.Leaf.Bound) (index : Nat) :
    Except GroupError (Profile × (Nat × Nat) × List Page.Frame) := do
  match ← (Date.Leaf.Gzip.Dispatch.V2.WithPlain.route bound index).mapError .selection with
  | .plain =>
    let group ← (Date.Leaf.Gzip.V2.checkGroup (Date.Leaf.Gzip.Dispatch.V2.WithPlain.plainLimits limits)
      bound index).mapError .plain
    return (.plain, (group.selection.span.start, group.selection.span.stop), group.frames)
  | .dictionaryBacked =>
    let group ← (Date.Leaf.Gzip.Dispatch.V2.checkGroup limits bound index).mapError .dictionaryBacked
    let choice := match Date.Leaf.Gzip.Dispatch.V2.profile (group.data.map (·.frame)) with
      | .dictionary => Profile.dictionary
      | .fallback => Profile.fallback
    return (choice, (group.selection.span.start, group.selection.span.stop), group.frames)

private meta def readBack (input : Bytes) (ordinal : Nat) (name : String) (nullable : Bool)
    (expected : List (List (Option Int))) (bounds : List (Nat × Nat)) (offsets : List (List Nat))
    (crcs : List (List (Option Nat))) (profiles : List Profile) (flags : List (List Bool))
    (storedCap expandedCap : Nat) (path : System.FilePath) : IO Unit := do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal
    | throw (IO.userError "mixed GZIP V2 DATE binding failed")
  unless bound.binding.leaf.name == name && bound.nullable == nullable &&
      bound.binding.annotation == .logicalAndConverted do
    throw (IO.userError "mixed GZIP V2 DATE descriptor differed")
  let indices := List.range bound.snapshot.groupCount
  let limits : Limits := { maxChunkBytes := storedCap, maxExpandedChunkBytes := expandedCap }
  let groups ← match indices.mapM (checkedFrames limits bound) with
    | .ok groups => pure groups
    | .error cause => throw (IO.userError s!"mixed GZIP V2 DATE plan failed: {repr cause}")
  unless groups.map (·.1) == profiles && groups.map (·.2.1) == bounds &&
      groups.map (fun group => group.2.2.map (·.header.start)) == offsets &&
      groups.map (fun group => group.2.2.map (fun frame => frame.value.crc.map UInt32.toNat)) == crcs &&
      groups.map (fun group => group.2.2.filterMap fun frame =>
        match frame.value.kind with
        | .dataV2 header => some header.isCompressed
        | _ => none) == flags do
    throw (IO.userError "mixed GZIP V2 DATE routes, extents, CRCs or flags differed")
  unless (indices.zip profiles).all (fun (index, choice) => agrees input ordinal index choice limits) do
    throw (IO.userError "the corresponding reader's result differed")
  let .ok slots := indices.mapM (Date.Leaf.Gzip.Dispatch.V2.WithPlain.readGroup limits bound)
    | throw (IO.userError "mixed GZIP V2 DATE slots failed")
  unless slots.map (List.map (Option.map Int32.toInt)) == expected do
    throw (IO.userError "mixed GZIP V2 DATE slots differed")
  let .ok ipc := Date.Leaf.Gzip.Dispatch.V2.WithPlain.toIpc {} limits {} ordinal input
    | throw (IO.userError "mixed GZIP V2 DATE IPC emission failed")
  IO.FS.writeBinFile path ipc.toByteArray

private meta def assertRejects (label : String) (input : Bytes) (ordinal : Nat) (expected : IpcError)
    (limits : Limits) (output : Arrow.ObservationLimits) : IO Unit := do
  match Date.Leaf.Gzip.Dispatch.V2.WithPlain.toIpc {} limits output ordinal input with
  | .error actual =>
    unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected success")

private meta def keepsPrefix (input : Bytes) (ordinal index : Nat)
    (expected : List (List (Option Int))) (cause : GroupError) : Bool := Id.run do
  let .ok ⟨schema, trace⟩ := Date.Leaf.Gzip.Dispatch.V2.WithPlain.readAll {} {} ordinal input
    | return false
  let .readError (.groupFailure actualIndex actualCause) := trace.termination | return false
  if width : schema.width = 1 then
    let observed := trace.batches.map fun batch =>
      (batch.values ⟨0, by omega⟩).map (Option.map Int32.toInt)
    return actualIndex == index && actualCause == cause && observed == expected
  return false

#eval assertRejects "short file" (Bytes.ofList []) 1
  (.source (.openFailure (.snapshot (.footer (.framing .shortFile))))) {} {}
