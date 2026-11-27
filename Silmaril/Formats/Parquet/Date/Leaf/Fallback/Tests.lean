module

meta import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet

private meta def readBack (input : Bytes) (ordinal : Nat) (name : String)
    (expected : List (List (Option Int))) (bounds : List (Nat × Nat))
    (offsets : List (List Nat)) (tags : List (List Int))
    (path : System.FilePath) : IO Unit := do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal
    | throw (IO.userError "DATE fallback binding failed")
  unless bound.binding.leaf.name == name && bound.nullable &&
      bound.binding.annotation == .logicalAndConverted do
    throw (IO.userError "DATE fallback descriptor differed")
  let indices := List.range bound.snapshot.groupCount
  let .ok groups := indices.mapM (Date.Leaf.Fallback.checkGroup {} bound)
    | throw (IO.userError "DATE fallback plan failed")
  unless groups.map (fun group => (group.chunk.span.start, group.chunk.span.stop)) == bounds &&
      groups.map (fun group => group.chunk.frames.map (·.header.start)) == offsets &&
      groups.map (fun group => group.chunk.data.map (·.params.encoding)) == tags do
    throw (IO.userError "DATE fallback frame order, bound or encoding differed")
  let .ok slots := indices.mapM (Date.Leaf.Fallback.readGroup {} bound)
    | throw (IO.userError "DATE fallback slots failed")
  unless slots.map (List.map (Option.map Int32.toInt)) == expected do
    throw (IO.userError "DATE fallback nullable slots differed")
  let .ok ipc := Date.Leaf.Fallback.toIpc {} {} {} ordinal input
    | throw (IO.userError "DATE fallback IPC emission failed")
  IO.FS.writeBinFile path ipc.toByteArray

private meta def rejects (input : Bytes) (ordinal : Nat) (expected : Date.Leaf.Fallback.IpcError)
    (output : Arrow.ObservationLimits := {}) : Bool :=
  match Date.Leaf.Fallback.toIpc {} {} output ordinal input with
  | .error actual => actual == expected
  | .ok _ => false

private meta def keepsPrefix (input : Bytes) (ordinal index : Nat)
    (expected : List (List (Option Int))) (cause : Date.Leaf.Fallback.GroupError) : Bool := Id.run do
  let .ok ⟨schema, trace⟩ := Date.Leaf.Fallback.readAll {} {} ordinal input | return false
  let .readError (.groupFailure actualIndex actualCause) := trace.termination | return false
  if width : schema.width = 1 then
    let observed := trace.batches.map fun batch =>
      (batch.values ⟨0, by omega⟩).map (Option.map Int32.toInt)
    return actualIndex == index && actualCause == cause && observed == expected
  return false

private meta def olderProfilesRefuse (input : Bytes) (ordinal plainPage : Nat) (label : String) : Bool :=
  match Date.Leaf.Events.toIpc {} {} ordinal input, Date.Leaf.Dictionary.toIpc {} {} {} ordinal input with
  | .error (.source (.groupFailure 0 (.scan (.columnEncoding actual)))),
      .error (.source (.groupFailure 0 (.dataEncoding page 0))) => actual == label && page == plainPage
  | _, _ => false

#guard Date.Leaf.Fallback.checkSequence [] == .error .missingReferences
#guard rejects (Bytes.ofList []) 1 (.source (.openFailure (.snapshot (.footer (.framing .shortFile)))))
