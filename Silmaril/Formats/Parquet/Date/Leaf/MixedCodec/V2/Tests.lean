module

meta import Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2 (Limits GroupError IpcError)

private meta def agrees (bound : Date.Leaf.Bound) (index : Nat) (codec : Int)
    (limits : Limits) : Bool :=
  let expected : Except GroupError Date.Leaf.Slots := match codec with
    | 2 => (Date.Leaf.Gzip.Dispatch.V2.WithPlain.readGroup limits.gzip bound index).mapError .gzip
    | 6 => (Date.Leaf.Zstd.Dispatch.V2.readGroup limits.zstd bound index).mapError .zstd
    | actual => .error (.unsupportedCodec actual)
  match Date.Leaf.MixedCodec.V2.readGroup limits bound index, expected with
  | .ok actual, .ok slots => actual == slots
  | .error actual, .error expected => actual == expected
  | _, _ => false

private meta def readBack (input : Bytes) (ordinal : Nat) (name : String) (nullable : Bool)
    (expected : List (List (Option Int))) (codecs : List Int) (limits : Limits)
    (path : System.FilePath) : IO Unit := do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal
    | throw (IO.userError "mixed-codec DATE binding failed")
  unless bound.binding.leaf.name == name && bound.nullable == nullable &&
      bound.binding.annotation == .logicalAndConverted do
    throw (IO.userError "mixed-codec DATE descriptor differed")
  let indices := List.range bound.snapshot.groupCount
  let .ok observed := indices.mapM (Date.Leaf.MixedCodec.V2.selectedCodec bound)
    | throw (IO.userError "mixed-codec DATE routing failed")
  unless observed == codecs && (indices.zip codecs).all (fun (index, codec) => agrees bound index codec limits) do
    throw (IO.userError "mixed-codec DATE route or strict result differed")
  let .ok slots := indices.mapM (Date.Leaf.MixedCodec.V2.readGroup limits bound)
    | throw (IO.userError "mixed-codec DATE slots failed")
  unless slots.map (List.map (Option.map Int32.toInt)) == expected do
    throw (IO.userError "mixed-codec DATE signed slots differed")
  let .ok ipc := Date.Leaf.MixedCodec.V2.toIpc {} limits {} ordinal input
    | throw (IO.userError "mixed-codec DATE IPC emission failed")
  IO.FS.writeBinFile path ipc.toByteArray

private meta def assertRejects (label : String) (input : Bytes) (ordinal index : Nat)
    (selected : Int) (cause : GroupError) (limits : Limits) : IO Unit := do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal
    | throw (IO.userError s!"{label}: binding failed")
  let .ok codec := Date.Leaf.MixedCodec.V2.selectedCodec bound index
    | throw (IO.userError s!"{label}: selected codec unavailable")
  unless codec == selected && agrees bound index selected limits do
    throw (IO.userError s!"{label}: differing standalone route or codec")
  let expected := IpcError.source (.groupFailure index cause)
  match Date.Leaf.MixedCodec.V2.toIpc {} limits { ipc := { batches := 0 } } ordinal input with
  | .error actual =>
    unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected success")

private meta def keepsPrefix (input : Bytes) (ordinal index : Nat)
    (expected : List (List (Option Int))) (cause : GroupError) (limits : Limits) : Bool := Id.run do
  let .ok ⟨schema, trace⟩ := Date.Leaf.MixedCodec.V2.readAll {} limits ordinal input
    | return false
  let .readError (.groupFailure actualIndex actualCause) := trace.termination | return false
  if width : schema.width = 1 then
    let observed := trace.batches.map fun batch =>
      (batch.values ⟨0, by omega⟩).map (Option.map Int32.toInt)
    return actualIndex == index && actualCause == cause && observed == expected
  return false

#guard match Date.Leaf.MixedCodec.V2.toIpc {} {} {} 1 (Bytes.ofList []) with
  | .error (.source (.openFailure (.snapshot (.footer (.framing .shortFile))))) => true
  | _ => false
