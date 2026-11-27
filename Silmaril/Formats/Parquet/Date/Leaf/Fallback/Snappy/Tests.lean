module

meta import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy.Defs
meta import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy (Limits GroupError IpcError)

private meta def readBack (input : Bytes) (ordinal : Nat) (name : String)
    (expected : List (List (Option Int))) (bounds : List (Nat × Nat))
    (offsets : List (List Nat)) (crcs : List (List (Option Nat))) (expandedCap : Nat)
    (path : System.FilePath) : IO Unit := do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal
    | throw (IO.userError "Snappy DATE binding failed")
  unless bound.binding.leaf.name == name && bound.nullable &&
      bound.binding.annotation == .logicalAndConverted do
    throw (IO.userError "Snappy DATE descriptor differed")
  let indices := List.range bound.snapshot.groupCount
  let .ok groups := indices.mapM (Date.Leaf.Fallback.Snappy.checkGroup {} bound)
    | throw (IO.userError "Snappy DATE group planning failed")
  unless groups.map (fun group => (group.selection.span.start, group.selection.span.stop)) == bounds &&
      groups.map (fun group => group.frames.map (·.header.start)) == offsets &&
      groups.map (fun group => group.frames.map (fun frame => frame.value.crc.map UInt32.toNat)) == crcs &&
      groups.all (fun group => group.data.map (·.params.encoding) == [8, 0, 0, 0]) do
    throw (IO.userError "Snappy DATE offsets, tags or original CRCs differed")
  let .ok slots := indices.mapM (Date.Leaf.Fallback.Snappy.readGroup {} bound)
    | throw (IO.userError "Snappy DATE slot decoding failed")
  unless slots.map (List.map (Option.map Int32.toInt)) == expected do
    throw (IO.userError "Snappy DATE nullable slots differed")
  let .ok ipc := Date.Leaf.Fallback.Snappy.toIpc {} { maxExpandedChunkBytes := expandedCap } {} ordinal input
    | throw (IO.userError "Snappy DATE IPC emission failed")
  IO.FS.writeBinFile path ipc.toByteArray

private meta def rejects (input : Bytes) (ordinal : Nat) (expected : IpcError)
    (limits : Limits := {}) (output : Arrow.ObservationLimits := {}) : Bool :=
  match Date.Leaf.Fallback.Snappy.toIpc {} limits output ordinal input with
  | .error actual => actual == expected
  | .ok _ => false

private meta def keepsPrefix (input : Bytes) (ordinal index : Nat)
    (expected : List (List (Option Int))) (cause : GroupError) : Bool := Id.run do
  let .ok ⟨schema, trace⟩ := Date.Leaf.Fallback.Snappy.readAll {} {} ordinal input | return false
  let .readError (.groupFailure actualIndex actualCause) := trace.termination | return false
  if width : schema.width = 1 then
    let observed := trace.batches.map fun batch =>
      (batch.values ⟨0, by omega⟩).map (Option.map Int32.toInt)
    return actualIndex == index && actualCause == cause && observed == expected
  return false

private meta def olderProfilesRefuse (input : Bytes) (ordinal : Nat) (label : String) : Bool :=
  match Date.Leaf.Events.toIpc {} {} ordinal input,
      Date.Leaf.Dictionary.Snappy.toIpc {} {} {} ordinal input, Date.Leaf.Fallback.toIpc {} {} {} ordinal input with
  | .error (.source (.groupFailure 0 (.scan (.columnCodec actual)))),
      .error (.source (.groupFailure 0 (.page 2 _ (.encoding 0)))),
      .error (.source (.groupFailure 0 (.dictionary (.chunk .columnCodec)))) => actual == label
  | _, _, _ => false

#guard rejects (Bytes.ofList []) 1 (.source (.openFailure (.snapshot (.footer (.framing .shortFile)))))
