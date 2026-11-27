module

meta import Silmaril.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2 (Limits GroupError IpcError)

private meta inductive Branch where
  | plain
  | dictionaryOnly
  | fallback
  deriving DecidableEq

private meta def strictRead (branch : Branch) (limits : Limits) (bound : Date.Leaf.Bound) (index : Nat) :
    Except GroupError Date.Leaf.Slots :=
  match branch with
  | .plain =>
    (Date.Leaf.Snappy.V2.readGroup (Date.Leaf.Snappy.Dispatch.V2.plainLimits limits) bound index).mapError .plain
  | .dictionaryOnly =>
    (Date.Leaf.Dictionary.Snappy.V2.readGroup .dictionaryOnly limits bound index).mapError .dictionaryBacked
  | .fallback =>
    (Date.Leaf.Dictionary.Snappy.V2.readGroup .fallback limits bound index).mapError .dictionaryBacked

private meta def agrees (bound : Date.Leaf.Bound) (index : Nat) (branch : Branch) (limits : Limits) : Bool :=
  match Date.Leaf.Snappy.Dispatch.V2.readGroup limits bound index, strictRead branch limits bound index with
  | .ok actual, .ok strict => actual == strict
  | .error actual, .error strict => actual == strict
  | _, _ => false

private meta def originalFrames (bound : Date.Leaf.Bound) (index : Nat) (branch : Branch)
    (limits : Limits) : IO ((Nat × Nat) × List Page.Frame) := do
  let .ok route := Date.Leaf.Snappy.Dispatch.V2.route bound index
    | throw (IO.userError "Snappy dispatch footer selection failed")
  match route with
  | .plain =>
    unless branch == .plain do throw (IO.userError "Expected dictionary-backed Snappy route")
    let .ok group := Date.Leaf.Snappy.V2.checkGroup (Date.Leaf.Snappy.Dispatch.V2.plainLimits limits) bound index
      | throw (IO.userError "Snappy PLAIN group planning failed")
    return ((group.selection.span.start, group.selection.span.stop), group.frames)
  | .dictionaryBacked =>
    let .ok group := Date.Leaf.Snappy.Dispatch.V2.checkDictionaryGroup limits bound index
      | throw (IO.userError "Snappy dictionary-backed group planning failed")
    let actual : Branch := match Date.Leaf.Snappy.Dispatch.V2.profile (group.data.map (·.frame)) with
      | .dictionaryOnly => .dictionaryOnly
      | .fallback => .fallback
    unless branch == actual do throw (IO.userError "Wrong Snappy dictionary-backed profile")
    return ((group.selection.span.start, group.selection.span.stop), group.frames)

private meta def readBack (input : Bytes) (ordinal : Nat) (name : String) (nullable : Bool)
    (expected : List (List (Option Int))) (bounds : List (Nat × Nat))
    (offsets : List (List Nat)) (crcs : List (List (Option Nat))) (branches : List Branch)
    (flags : List (List Bool)) (limits : Limits) (path : System.FilePath) : IO Unit := do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal
    | throw (IO.userError "Snappy dispatch DATE binding failed")
  unless bound.binding.leaf.name == name && bound.nullable == nullable &&
      bound.binding.annotation == .logicalAndConverted do
    throw (IO.userError "Snappy dispatch DATE descriptor differed")
  let indices := List.range bound.snapshot.groupCount
  unless branches.length == indices.length do throw (IO.userError "Snappy dispatch group count differed")
  let groups ← (indices.zip branches).mapM fun (index, branch) => do
    unless agrees bound index branch limits do throw (IO.userError s!"Strict Snappy result differed at {index}")
    originalFrames bound index branch limits
  let frames := groups.map Prod.snd
  unless groups.map Prod.fst == bounds && frames.map (List.map (·.header.start)) == offsets &&
      frames.map (List.map fun frame => frame.value.crc.map UInt32.toNat) == crcs &&
      frames.map (List.filterMap fun frame =>
        match frame.value.kind with | .dataV2 header => some header.isCompressed | _ => none) == flags do
    throw (IO.userError "Snappy dispatch original frames, CRCs or flags differed")
  let .ok slots := indices.mapM (Date.Leaf.Snappy.Dispatch.V2.readGroup limits bound)
    | throw (IO.userError "Snappy dispatch DATE decoding failed")
  unless slots.map (List.map (Option.map Int32.toInt)) == expected do
    throw (IO.userError "Snappy dispatch signed nullable slots differed")
  let .ok ipc := Date.Leaf.Snappy.Dispatch.V2.toIpc {} limits {} ordinal input
    | throw (IO.userError "Snappy dispatch Date32 IPC emission failed")
  IO.FS.writeBinFile path ipc.toByteArray

private meta def assertRejects (label : String) (input : Bytes) (ordinal index : Nat)
    (branch : Branch) (expectedPrefix : List (List (Option Int))) (cause : GroupError) (limits : Limits) :
    IO Unit := do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal | throw (IO.userError s!"{label}: binding failed")
  unless agrees bound index branch limits do throw (IO.userError s!"{label}: strict result differed")
  let expected := IpcError.source (.groupFailure index cause)
  match Date.Leaf.Snappy.Dispatch.V2.toIpc {} limits { ipc := { batches := 0 } } ordinal input with
  | .error actual =>
    unless actual == expected do throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected IPC success")
  let .ok ⟨schema, trace⟩ := Date.Leaf.Snappy.Dispatch.V2.readAll {} limits ordinal input
    | throw (IO.userError s!"{label}: no event trace")
  let .readError (.groupFailure actualIndex actualCause) := trace.termination
    | throw (IO.userError s!"{label}: incorrect terminal event")
  if width : schema.width = 1 then
    let observed := trace.batches.map fun batch => (batch.values ⟨0, by omega⟩).map (Option.map Int32.toInt)
    unless actualIndex == index && actualCause == cause && observed == expectedPrefix do
      throw (IO.userError s!"{label}: completed prefix differed")
  else
    throw (IO.userError s!"{label}: incorrect schema")

#guard match Date.Leaf.Snappy.Dispatch.V2.toIpc {} {} {} 1 (Bytes.ofList []) with
  | .error (.source (.openFailure (.snapshot (.footer (.framing .shortFile))))) => true
  | _ => false
