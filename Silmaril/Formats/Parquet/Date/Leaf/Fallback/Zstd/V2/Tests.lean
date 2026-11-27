module

meta import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.Defs
meta import Silmaril.Formats.Parquet.Date.Leaf.Zstd.V2.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2 (Limits GroupError IpcError)

private meta def usesFlag (bound : Date.Leaf.Bound) (group : Date.Leaf.Fallback.Zstd.V2.CheckedGroup) :
    Bool := (group.data.zipIdx 1).all fun (page, index) => Id.run do
  let .v2 _ _ _ _ (some isCompressed) := page.params.version | return false
  let limits : Limits := {}
  let zero : Limits := { limits with compression := ⟨0, limits.compression.commandsPerBlock⟩ }
  let entries := group.entries.toArray
  let metadata := group.selection.column.metadata
  let .ok expected := Date.Leaf.Fallback.Zstd.V2.decodePage limits bound metadata entries page index | return false
  return match Date.Leaf.Fallback.Zstd.V2.decodePage zero bound metadata entries page index with
  | .ok actual => !isCompressed && actual == expected
  | .error (.dictionary (.preparation _ _ (.frame (.frame .windowLimit)))) =>
    isCompressed && page.params.encoding == 8
  | .error (.plain (.decode _ _ (.frame (.frame .windowLimit)))) => isCompressed && page.params.encoding == 0
  | .error _ => false

private meta def readBack (input : Bytes) (ordinal : Nat) (name : String) (nullable : Bool)
    (expected : List (List (Option Int))) (bounds : List (Nat × Nat))
    (offsets : List (List Nat)) (crcs : List (List (Option Nat))) (dictionaries : List (List Int))
    (flags : List (List Bool)) (tags : List (List Int)) (storedCap expandedCap : Nat)
    (path : System.FilePath) : IO Unit := do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal
    | throw (IO.userError "ZSTD V2 fallback DATE binding failed")
  unless bound.binding.leaf.name == name && bound.nullable == nullable &&
      bound.binding.annotation == .logicalAndConverted do
    throw (IO.userError "ZSTD V2 fallback DATE descriptor differed")
  let indices := List.range bound.snapshot.groupCount
  let groups ← match indices.mapM (Date.Leaf.Fallback.Zstd.V2.checkGroup {} bound) with
    | .ok groups => pure groups
    | .error cause => throw (IO.userError s!"ZSTD V2 fallback DATE group planning failed: {repr cause}")
  unless groups.map (fun group => (group.selection.span.start, group.selection.span.stop)) == bounds &&
      groups.map (fun group => group.frames.map (·.header.start)) == offsets &&
      groups.map (fun group => group.frames.map (fun frame => frame.value.crc.map UInt32.toNat)) == crcs &&
      groups.map (fun group => group.entries.map Int32.toInt) == dictionaries &&
      groups.map (fun group => group.data.filterMap fun page =>
        match page.params.version with
        | .v2 _ _ _ _ flag => flag
        | .v1 .. => none) == flags &&
      groups.map (fun group => group.data.map (·.params.encoding)) == tags do
    throw (IO.userError "ZSTD V2 fallback DATE offsets, tags, flags, dictionary entries or CRCs differed")
  unless groups.all (usesFlag bound) do
    throw (IO.userError "The original V2 flag did not select the expected suffix decoder")
  let .ok slots := indices.mapM (Date.Leaf.Fallback.Zstd.V2.readGroup {} bound)
    | throw (IO.userError "ZSTD V2 fallback DATE slot decoding failed")
  unless slots.map (List.map (Option.map Int32.toInt)) == expected do
    throw (IO.userError "ZSTD V2 fallback DATE nullable slots differed")
  let .ok ipc := Date.Leaf.Fallback.Zstd.V2.toIpc {}
    { maxChunkBytes := storedCap, maxExpandedChunkBytes := expandedCap } {} ordinal input
    | throw (IO.userError "ZSTD V2 fallback DATE IPC emission failed")
  IO.FS.writeBinFile path ipc.toByteArray

private meta def assertRejects (label : String) (input : Bytes) (ordinal : Nat) (expected : IpcError)
    (limits : Limits) (output : Arrow.ObservationLimits) : IO Unit := do
  match Date.Leaf.Fallback.Zstd.V2.toIpc {} limits output ordinal input with
  | .error actual =>
    unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected success")

private meta def keepsPrefix (input : Bytes) (ordinal index : Nat)
    (expected : List (List (Option Int))) (cause : GroupError) : Bool := Id.run do
  let .ok ⟨schema, trace⟩ := Date.Leaf.Fallback.Zstd.V2.readAll {} {} ordinal input | return false
  let .readError (.groupFailure actualIndex actualCause) := trace.termination | return false
  if width : schema.width = 1 then
    let observed := trace.batches.map fun batch =>
      (batch.values ⟨0, by omega⟩).map (Option.map Int32.toInt)
    return actualIndex == index && actualCause == cause && observed == expected
  return false

private meta def strictProfilesRefuse (input : Bytes) (ordinal firstPlain offset : Nat) : Bool :=
  match Date.Leaf.Zstd.toIpc {} {} {} ordinal input, Date.Leaf.Zstd.V2.toIpc {} {} {} ordinal input,
      Date.Leaf.Dictionary.Zstd.V2.toIpc {} {} {} ordinal input with
  | .error (.source (.groupFailure 0 (.plan .unsupportedOffsets))),
      .error (.source (.groupFailure 0 (.zstd (.plan .unsupportedOffsets)))),
      .error (.source (.groupFailure 0 (.header observedIndex observedOffset (.encoding 0)))) =>
    observedIndex == firstPlain && observedOffset == offset
  | _, _, _ => false

#eval assertRejects "short file" (Bytes.ofList []) 1
  (.source (.openFailure (.snapshot (.footer (.framing .shortFile))))) {} {}
