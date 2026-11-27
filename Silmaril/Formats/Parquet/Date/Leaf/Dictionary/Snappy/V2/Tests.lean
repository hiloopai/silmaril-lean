module

meta import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy (Limits)
open Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2 (Profile GroupError IpcError)

private meta def readBack (profile : Profile) (input : Bytes) (ordinal : Nat) (name : String)
    (expected : List (List (Option Int))) (bounds : List (Nat × Nat))
    (offsets : List (List Nat)) (crcs : List (List (Option Nat))) (flags : List (List Bool))
    (expansionCap : Nat) (path : System.FilePath) : IO Unit := do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal
    | throw (IO.userError "Snappy DATE binding failed")
  unless bound.binding.leaf.name == name && bound.nullable &&
      bound.binding.annotation == .logicalAndConverted do
    throw (IO.userError "Snappy DATE descriptor differed")
  let indices := List.range bound.snapshot.groupCount
  let limits : Limits := { maxExpandedChunkBytes := expansionCap }
  let .ok groups := indices.mapM (Date.Leaf.Dictionary.Snappy.V2.checkGroup profile limits bound)
    | throw (IO.userError "Snappy DATE V2 group planning failed")
  unless groups.map (fun group => (group.selection.span.start, group.selection.span.stop)) == bounds &&
      groups.map (fun group => group.frames.map (·.header.start)) == offsets &&
      groups.map (fun group => group.frames.map (fun frame => frame.value.crc.map UInt32.toNat)) == crcs &&
      groups.map (fun group => group.data.map fun page =>
        match page.frame.value.kind with | .dataV2 header => header.isCompressed | _ => false) == flags do
    throw (IO.userError "Snappy DATE original frames, CRCs or flags differed")
  let .ok slots := indices.mapM (Date.Leaf.Dictionary.Snappy.V2.readGroup profile limits bound)
    | throw (IO.userError "Snappy DATE V2 decoding failed")
  unless slots.map (List.map (Option.map Int32.toInt)) == expected do
    throw (IO.userError "Snappy DATE signed nullable slots differed")
  let .ok ipc := Date.Leaf.Dictionary.Snappy.V2.toIpc profile {} limits {} ordinal input
    | throw (IO.userError "Snappy DATE V2 IPC emission failed")
  let legacy := match profile with
    | .dictionaryOnly => (Date.Leaf.Dictionary.Snappy.toIpc {} limits {} ordinal input).toOption
    | .fallback => (Date.Leaf.Fallback.Snappy.toIpc {} limits {} ordinal input).toOption
  unless legacy.map KBytes.toByteArray == some ipc.toByteArray do
    throw (IO.userError "Snappy DATE IPC differed from the established profile on V2 data")
  IO.FS.writeBinFile path ipc.toByteArray

private meta def rejects (profile : Profile) (input : Bytes) (ordinal : Nat) (expected : IpcError)
    (limits : Limits) (output : Arrow.ObservationLimits) : Bool :=
  match Date.Leaf.Dictionary.Snappy.V2.toIpc profile {} limits output ordinal input with
  | .error found => found == expected
  | .ok _ => false

private meta def keepsPrefix (profile : Profile) (input : Bytes) (ordinal index : Nat)
    (expected : List (List (Option Int))) (cause : GroupError) : Bool := Id.run do
  let .ok ⟨schema, trace⟩ := Date.Leaf.Dictionary.Snappy.V2.readAll profile {} {} ordinal input
    | return false
  let .readError (.groupFailure actualIndex actualCause) := trace.termination | return false
  if width : schema.width = 1 then
    let observed := trace.batches.map fun batch =>
      (batch.values ⟨0, by omega⟩).map (Option.map Int32.toInt)
    return actualIndex == index && actualCause == cause && observed == expected
  return false

#guard rejects .dictionaryOnly (Bytes.ofList []) 1
  (.source (.openFailure (.snapshot (.footer (.framing .shortFile))))) {} {}
