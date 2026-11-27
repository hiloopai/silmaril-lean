module

meta import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Defs
meta import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy.Defs
meta import Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2.Defs
meta import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip (Limits GroupError IpcError)

private meta def readBack (input : Bytes) (ordinal : Nat) (name : String) (nullable : Bool)
    (expected : List (List (Option Int))) (bounds : List (Nat × Nat))
    (offsets : List (List Nat)) (crcs : List (List (Option Nat))) (dictionaries : List (List Int))
    (storedCap expandedCap : Nat)
    (path : System.FilePath) : IO Unit := do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal
    | throw (IO.userError "GZIP fallback DATE binding failed")
  unless bound.binding.leaf.name == name && bound.nullable == nullable &&
      bound.binding.annotation == .logicalAndConverted do
    throw (IO.userError "GZIP fallback DATE descriptor differed")
  let indices := List.range bound.snapshot.groupCount
  let groups ← match indices.mapM (Date.Leaf.Fallback.Gzip.checkGroup {} bound) with
    | .ok groups => pure groups
    | .error cause => throw (IO.userError s!"GZIP fallback DATE group planning failed: {repr cause}")
  unless groups.map (fun group => (group.selection.span.start, group.selection.span.stop)) == bounds &&
      groups.map (fun group => group.frames.map (·.header.start)) == offsets &&
      groups.map (fun group => group.frames.map (fun frame => frame.value.crc.map UInt32.toNat)) == crcs &&
      groups.map (fun group => group.entries.map Int32.toInt) == dictionaries &&
      groups.all (fun group => group.data.map (·.params.encoding) == [8, 0, 0, 0]) do
    throw (IO.userError "GZIP fallback DATE offsets, tags, dictionary entries or original CRCs differed")
  let .ok slots := indices.mapM (Date.Leaf.Fallback.Gzip.readGroup {} bound)
    | throw (IO.userError "GZIP fallback DATE slot decoding failed")
  unless slots.map (List.map (Option.map Int32.toInt)) == expected do
    throw (IO.userError "GZIP fallback DATE nullable slots differed")
  let .ok ipc := Date.Leaf.Fallback.Gzip.toIpc {}
    { maxChunkBytes := storedCap, maxExpandedChunkBytes := expandedCap } {} ordinal input
    | throw (IO.userError "GZIP fallback DATE IPC emission failed")
  IO.FS.writeBinFile path ipc.toByteArray

private meta def assertRejects (label : String) (input : Bytes) (ordinal : Nat) (expected : IpcError)
    (limits : Limits) (output : Arrow.ObservationLimits) : IO Unit := do
  match Date.Leaf.Fallback.Gzip.toIpc {} limits output ordinal input with
  | .error actual =>
    unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected success")

private meta def keepsPrefix (input : Bytes) (ordinal index : Nat)
    (expected : List (List (Option Int))) (cause : GroupError) : Bool := Id.run do
  let .ok ⟨schema, trace⟩ := Date.Leaf.Fallback.Gzip.readAll {} {} ordinal input | return false
  let .readError (.groupFailure actualIndex actualCause) := trace.termination | return false
  if width : schema.width = 1 then
    let observed := trace.batches.map fun batch =>
      (batch.values ⟨0, by omega⟩).map (Option.map Int32.toInt)
    return actualIndex == index && actualCause == cause && observed == expected
  return false

private meta def olderProfilesRefuse (input : Bytes) (ordinal : Nat) : Bool :=
  match Date.Leaf.Gzip.toIpc {} {} {} ordinal input, Date.Leaf.Gzip.V2.toIpc {} {} {} ordinal input,
      Date.Leaf.Fallback.Snappy.toIpc {} {} {} ordinal input,
      Date.Leaf.Dictionary.Snappy.toIpc {} {} {} ordinal input with
  | .error (.source (.groupFailure 0 .unsupportedOffsets)),
      .error (.source (.groupFailure 0 (.gzip .unsupportedOffsets))),
      .error (.source (.groupFailure 0 (.snappy (.codec 2)))),
      .error (.source (.groupFailure 0 (.codec 2))) => true
  | _, _, _, _ => false

#eval assertRejects "short file" (Bytes.ofList []) 1
  (.source (.openFailure (.snapshot (.footer (.framing .shortFile))))) {} {}
