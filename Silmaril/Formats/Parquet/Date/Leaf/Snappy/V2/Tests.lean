module

meta import Silmaril.Formats.Parquet.Date.Leaf.Snappy.V2.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Date.Leaf.Snappy.V2 (Limits GroupError IpcError)

private meta def readBack (input : Bytes) (ordinal : Nat) (name : String) (nullable : Bool)
    (expected : List (List (Option Int))) (bounds : List (Nat × Nat))
    (offsets : List (List Nat)) (crcs : List (List (Option Nat))) (stored expanded rows : Nat)
    (flags : List (List Bool))
    (path : System.FilePath) : IO Unit := do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal
    | throw (IO.userError "Snappy DATE binding failed")
  unless bound.binding.leaf.name == name && bound.nullable == nullable &&
      bound.binding.annotation == .logicalAndConverted do
    throw (IO.userError "Snappy DATE descriptor differed")
  let indices := List.range bound.snapshot.groupCount
  let inputLimits : Limits := {
    maxStoredChunkBytes := stored, maxExpandedChunkBytes := expanded
    maxRows := rows
  }
  let .ok groups := indices.mapM (Date.Leaf.Snappy.V2.checkGroup inputLimits bound)
    | throw (IO.userError "Snappy DATE group planning failed")
  unless groups.map (fun group => (group.selection.span.start, group.selection.span.stop)) == bounds &&
      groups.map (fun group => group.frames.map (·.header.start)) == offsets &&
      groups.map (fun group => group.frames.map (fun frame => frame.value.crc.map UInt32.toNat)) == crcs &&
      groups.map (fun group => group.frames.map fun frame =>
        match frame.value.kind with | .dataV2 metadata => metadata.isCompressed | _ => false) == flags do
    throw (IO.userError "Snappy DATE original ranges or CRCs differed")
  let .ok slots := indices.mapM (Date.Leaf.Snappy.V2.readGroup inputLimits bound)
    | throw (IO.userError "Snappy DATE slots failed")
  unless slots.map (List.map (Option.map Int32.toInt)) == expected do
    throw (IO.userError "Snappy DATE nullable slots differed")
  let .ok ipc := Date.Leaf.Snappy.V2.toIpc {} inputLimits {} ordinal input
    | throw (IO.userError "Snappy DATE IPC emission failed")
  IO.FS.writeBinFile path ipc.toByteArray

private meta def rejects (input : Bytes) (ordinal : Nat) (expected : IpcError)
    (limits : Limits := {}) (output : Arrow.ObservationLimits := {}) : Bool :=
  match Date.Leaf.Snappy.V2.toIpc {} limits output ordinal input with
  | .error actual => actual == expected
  | .ok _ => false

private meta def keepsPrefix (input : Bytes) (ordinal index : Nat)
    (expected : List (List (Option Int))) (cause : GroupError) : Bool := Id.run do
  let .ok ⟨schema, trace⟩ := Date.Leaf.Snappy.V2.readAll {} {} ordinal input | return false
  let .readError (.groupFailure actualIndex actualCause) := trace.termination | return false
  if width : schema.width = 1 then
    let observed := trace.batches.map fun batch =>
      (batch.values ⟨0, by omega⟩).map (Option.map Int32.toInt)
    return actualIndex == index && actualCause == cause && observed == expected
  return false

#guard rejects (Bytes.ofList []) 1 (.source (.openFailure (.snapshot (.footer (.framing .shortFile)))))
