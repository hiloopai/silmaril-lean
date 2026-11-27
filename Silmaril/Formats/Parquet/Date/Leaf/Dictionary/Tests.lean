module

meta import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet

private meta def readBack (input : Bytes) (ordinal : Nat) (name : String)
    (expected : List (List (Option Int))) (bounds : List (Nat × Nat))
    (entries : List (List Int)) (path : System.FilePath) : IO Unit := do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal
    | throw (IO.userError "DATE dictionary leaf open failed")
  unless bound.binding.leaf.name == name && bound.nullable &&
      bound.binding.annotation == .logicalAndConverted do
    throw (IO.userError "DATE dictionary binding differed")
  let indices := List.range bound.snapshot.groupCount
  let .ok observed := indices.mapM (fun index => do
      let selected ← (Date.Leaf.selectChunk bound index).mapError Date.Leaf.Dictionary.GroupError.selection
      let framed ← (Date.Leaf.Dictionary.frame {} bound selected).mapError Date.Leaf.Dictionary.GroupError.chunk
      let values := framed.dictionary.map fun (dictionary : DictionaryChunk.Dictionary) =>
        dictionary.entries.toList.map Int32.toInt
      return ((framed.span.start, framed.span.stop), values))
    | throw (IO.userError "DATE dictionary framing failed")
  unless observed.map Prod.fst == bounds &&
      observed.map Prod.snd == entries.map some do
    throw (IO.userError "DATE dictionary spans or signed entries differed")
  let .ok groups := indices.mapM (Date.Leaf.Dictionary.readGroup {} bound)
    | throw (IO.userError "DATE dictionary group decoding failed")
  unless groups.map (List.map (Option.map Int32.toInt)) == expected do
    throw (IO.userError "DATE dictionary slots differed")
  let .ok ipc := Date.Leaf.Dictionary.toIpc {} {} {} ordinal input
    | throw (IO.userError "DATE dictionary IPC emission failed")
  IO.FS.writeBinFile path ipc.toByteArray

private meta def rejects (input : Bytes) (ordinal : Nat) (expected : Date.Leaf.Dictionary.IpcError)
    (limits : Date.Leaf.Dictionary.Limits := {}) (out : Arrow.ObservationLimits := {}) : Bool :=
  match Date.Leaf.Dictionary.toIpc {} limits out ordinal input with
  | .error actual => actual == expected
  | .ok _ => false

private meta def keepsPrefix (input : Bytes) (ordinal index : Nat)
    (expected : List (List (Option Int))) (cause : Date.Leaf.Dictionary.GroupError) : Bool := Id.run do
  let .ok ⟨schema, trace⟩ := Date.Leaf.Dictionary.readAll {} {} ordinal input | return false
  let .readError (.groupFailure actualIndex actualCause) := trace.termination | return false
  if width : schema.width = 1 then
    let observed := trace.batches.map fun batch =>
      (batch.values ⟨0, by omega⟩).map (Option.map Int32.toInt)
    return actualIndex == index && actualCause == cause && observed == expected
  return false

private meta def plainRefuses (input : Bytes) (ordinal : Nat) : Bool :=
  match Date.Leaf.Events.toIpc {} {} ordinal input with
  | .error (.source (.groupFailure 0 (.scan (.columnEncoding "日付")))) => true
  | _ => false

#guard rejects (Bytes.ofList []) 1 (.source (.openFailure (.snapshot (.footer (.framing .shortFile)))))
