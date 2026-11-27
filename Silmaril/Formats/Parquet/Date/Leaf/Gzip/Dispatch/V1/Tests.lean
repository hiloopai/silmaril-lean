module

meta import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.Defs
meta import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Defs
meta import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1 (Limits GroupError IpcError Profile)

private meta def agrees (input : Bytes) (ordinal index : Nat) (choice : Profile) : Bool := Id.run do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal | return false
  let expected := match choice with
    | .dictionary =>
      (Date.Leaf.Dictionary.Gzip.V1.readGroup {} bound index).mapError Date.Leaf.Gzip.Dispatch.V1.dictionaryError
    | .fallback => Date.Leaf.Fallback.Gzip.readGroup {} bound index
  return match Date.Leaf.Gzip.Dispatch.V1.readGroup {} bound index, expected with
  | .ok actual, .ok value => actual == value
  | .error actual, .error cause => actual == cause
  | _, _ => false

private meta def readBack (input : Bytes) (ordinal : Nat) (name : String) (nullable : Bool)
    (expected : List (List (Option Int))) (bounds : List (Nat × Nat))
    (offsets : List (List Nat)) (crcs : List (List (Option Nat))) (dictionaries : List (List Int))
    (profiles : List Profile) (storedCap expandedCap : Nat)
    (path : System.FilePath) : IO Unit := do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal
    | throw (IO.userError "GZIP V1 DATE dispatch binding failed")
  unless bound.binding.leaf.name == name && bound.nullable == nullable &&
      bound.binding.annotation == .logicalAndConverted do
    throw (IO.userError "GZIP V1 DATE dispatch descriptor differed")
  let indices := List.range bound.snapshot.groupCount
  let groups ← match indices.mapM (Date.Leaf.Gzip.Dispatch.V1.checkGroup {} bound) with
    | .ok groups => pure groups
    | .error cause => throw (IO.userError s!"GZIP V1 DATE dispatch group planning failed: {repr cause}")
  unless groups.map (fun group => (group.selection.span.start, group.selection.span.stop)) == bounds &&
      groups.map (fun group => group.frames.map (·.header.start)) == offsets &&
      groups.map (fun group => group.frames.map (fun frame => frame.value.crc.map UInt32.toNat)) == crcs &&
      groups.map (fun group => group.entries.map Int32.toInt) == dictionaries &&
      groups.map (fun group => Date.Leaf.Gzip.Dispatch.V1.profile (group.data.map (·.frame))) == profiles do
    throw (IO.userError "GZIP V1 DATE dispatch offsets, tags, dictionary entries or CRCs differed")
  unless (indices.zip profiles).all (fun (index, choice) => agrees input ordinal index choice) do
    throw (IO.userError "The selected profile's read differed")
  let .ok slots := indices.mapM (Date.Leaf.Gzip.Dispatch.V1.readGroup {} bound)
    | throw (IO.userError "GZIP V1 DATE dispatch slot decoding failed")
  unless slots.map (List.map (Option.map Int32.toInt)) == expected do
    throw (IO.userError "GZIP V1 DATE dispatch nullable slots differed")
  let .ok ipc := Date.Leaf.Gzip.Dispatch.V1.toIpc {}
    { maxChunkBytes := storedCap, maxExpandedChunkBytes := expandedCap } {} ordinal input
    | throw (IO.userError "GZIP V1 DATE dispatch IPC emission failed")
  IO.FS.writeBinFile path ipc.toByteArray

private meta def assertRejects (label : String) (input : Bytes) (ordinal : Nat) (expected : IpcError)
    (limits : Limits) (output : Arrow.ObservationLimits) : IO Unit := do
  match Date.Leaf.Gzip.Dispatch.V1.toIpc {} limits output ordinal input with
  | .error actual =>
    unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected success")

private meta def keepsPrefix (input : Bytes) (ordinal index : Nat)
    (expected : List (List (Option Int))) (cause : GroupError) : Bool := Id.run do
  let .ok ⟨schema, trace⟩ := Date.Leaf.Gzip.Dispatch.V1.readAll {} {} ordinal input | return false
  let .readError (.groupFailure actualIndex actualCause) := trace.termination | return false
  if width : schema.width = 1 then
    let observed := trace.batches.map fun batch =>
      (batch.values ⟨0, by omega⟩).map (Option.map Int32.toInt)
    return actualIndex == index && actualCause == cause && observed == expected
  return false

private meta def uniformProfilesRefuse (input : Bytes) (ordinal : Nat) (firstPlain : Nat) : Bool :=
  match Date.Leaf.Fallback.Gzip.toIpc {} {} {} ordinal input,
      Date.Leaf.Dictionary.Gzip.V1.toIpc {} {} {} ordinal input with
  | .error (.source (.groupFailure 0 (.sequence .missingPlain))),
      .error (.source (.groupFailure 1 (.header 2 actual (.encoding 0)))) => actual == firstPlain
  | _, _ => false

#eval assertRejects "short file" (Bytes.ofList []) 1
  (.source (.openFailure (.snapshot (.footer (.framing .shortFile))))) {} {}
