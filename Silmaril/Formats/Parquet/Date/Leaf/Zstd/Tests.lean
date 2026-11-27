module

meta import Silmaril.Formats.Parquet.Date.Leaf.Zstd.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Date.Leaf.Zstd (Limits GroupError IpcError)

private meta def readBack (input : Bytes) (ordinal : Nat) (name : String) (nullable : Bool)
    (expected : List (List (Option Int))) (bounds : List (Nat × Nat))
    (offsets : List (List Nat)) (crcs : List (List (Option Nat))) (stored expanded : Nat)
    (path : System.FilePath) : IO Unit := do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal
    | throw (IO.userError "ZSTD DATE binding failed")
  unless bound.binding.leaf.name == name && bound.nullable == nullable &&
      bound.binding.annotation == .logicalAndConverted do
    throw (IO.userError "ZSTD DATE descriptor differed")
  let indices := List.range bound.snapshot.groupCount
  let inputLimits : Limits := { pages := { maxStoredChunkBytes := stored, maxExpandedChunkBytes := expanded } }
  let .ok groups := indices.mapM (Date.Leaf.Zstd.checkGroup inputLimits bound)
    | throw (IO.userError "ZSTD DATE group planning failed")
  unless groups.map (fun group => (group.selection.span.start, group.selection.span.stop)) == bounds &&
      groups.map (fun group => group.frames.map (·.header.start)) == offsets &&
      groups.map (fun group => group.frames.map (fun frame => frame.value.crc.map UInt32.toNat)) == crcs do
    throw (IO.userError "ZSTD DATE original ranges or CRCs differed")
  let .ok slots := indices.mapM (Date.Leaf.Zstd.readGroup inputLimits bound)
    | throw (IO.userError "ZSTD DATE slots failed")
  unless slots.map (List.map (Option.map Int32.toInt)) == expected do
    throw (IO.userError "ZSTD DATE nullable slots differed")
  let .ok ipc := Date.Leaf.Zstd.toIpc {} inputLimits {} ordinal input
    | throw (IO.userError "ZSTD DATE IPC emission failed")
  IO.FS.writeBinFile path ipc.toByteArray

private meta def assertRejects (label : String) (input : Bytes) (ordinal : Nat) (expected : IpcError)
    (limits : Limits) (output : Arrow.ObservationLimits) : IO Unit := do
  match Date.Leaf.Zstd.toIpc {} limits output ordinal input with
  | .error actual =>
    unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected success")

private meta def keepsPrefix (input : Bytes) (ordinal index : Nat)
    (expected : List (List (Option Int))) (cause : GroupError) : Bool := Id.run do
  let .ok ⟨schema, trace⟩ := Date.Leaf.Zstd.readAll {} {} ordinal input | return false
  let .readError (.groupFailure actualIndex actualCause) := trace.termination | return false
  if width : schema.width = 1 then
    let observed := trace.batches.map fun batch =>
      (batch.values ⟨0, by omega⟩).map (Option.map Int32.toInt)
    return actualIndex == index && actualCause == cause && observed == expected
  return false

private meta def plainRefuses (input : Bytes) (ordinal : Nat) (label : String) : Bool :=
  match Date.Leaf.Events.toIpc {} {} ordinal input with
  | .error (.source (.groupFailure 0 (.scan (.columnCodec actual)))) => actual == label
  | _ => false

#eval assertRejects "short file" (Bytes.ofList []) 1
  (.source (.openFailure (.snapshot (.footer (.framing .shortFile))))) {} {}
