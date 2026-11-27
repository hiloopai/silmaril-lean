module

import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts.Defs
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
meta import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts.Defs
meta import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Parquet.MixedV1Writer.FromIpc
open Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete
open Silmaril.Formats.Relational.NamedTable

private def limits : MixedV1Writer.MultiPage.Limits :=
  ⟨⟨⟨8192, {}, ⟨{}, 32, ⟨256, 256, ⟨32, 64⟩, 0⟩⟩,
    ⟨⟨{}, 32, ⟨256, 256, ⟨32, 64⟩, 0⟩⟩, ⟨256, 64⟩⟩, {}⟩, 3, 8⟩, 3, 10⟩

private def empty : PageCuts.BatchCuts := ⟨[0], [0]⟩

private def accepted (bounded : MixedV1Writer.MultiPage.Limits) (cuts : PageCuts.Policy)
    (input : KBytes) : IO Bytes :=
  match PageCuts.convert {} bounded cuts input with
  | .ok file => pure file
  | .error cause => throw (IO.userError s!"conversion failed: {repr cause}")

private def refused (bounded : MixedV1Writer.MultiPage.Limits) (cuts : PageCuts.Policy)
    (input : KBytes) (expected : PageCuts.Error) : IO Unit := do
  let .error actual := PageCuts.convert {} bounded cuts input
    | throw (IO.userError s!"expected {repr expected}, got a file")
  unless actual == expected do throw (IO.userError s!"expected {repr expected}, got {repr actual}")

private def load (directory : System.FilePath) (name : String) : IO KBytes := do
  let wire ← IO.FS.readBinFile (directory / (name ++ ".arrows"))
  return KBytes.ofChunks 1 wire.size (wire.data.toList.map UInt8.toNat)

private def returnIpc (directory : System.FilePath) (name : String) (file : Bytes)
    (observed : MixedIpc.Prepared) : IO Unit := do
  let .ok returned := ToIpc.convertOrdered {} {} file
      (field observed.descriptor.integer) (field observed.descriptor.binary)
    | throw (IO.userError s!"{name}: reverse conversion failed")
  let .ok actual := MixedIpc.read { inputBytes := returned.len } returned
    | throw (IO.userError s!"{name}: readback failed")
  unless actual.descriptor == observed.descriptor && actual.batches == observed.batches do
    throw (IO.userError s!"{name}: changed descriptor, values or batches")
  IO.FS.writeBinFile (directory / (name ++ ".parquet")) file.data
  IO.FS.writeBinFile (directory / (name ++ "-returned.arrows")) returned.toByteArray

private def verifyDefault (bounded : MixedV1Writer.MultiPage.Limits) (name : String)
    (input : KBytes) (policy : PageCuts.Policy) : IO Bytes := do
  let .ok normal := Complete.convert {} bounded.file input
    | throw (IO.userError s!"{name}: original converter failed")
  let optIn ← accepted bounded policy input
  unless optIn == normal.bytes do throw (IO.userError s!"{name}: default bytes changed")
  return optIn

private def checkOrder (directory : System.FilePath) (name : String) (viewFirst : Bool)
    (first : PageCuts.BatchCuts) : IO Unit := do
  let third : PageCuts.BatchCuts := ⟨[3], [1, 2]⟩
  let cuts := [first, empty, third]
  let input ← load directory name
  let .ok observed := MixedIpc.read {} input
    | throw (IO.userError s!"{name}: input was refused")
  unless observed.descriptor.viewFirst == viewFirst &&
      observed.batches.map List.length == [5, 0, 3] do
    throw (IO.userError s!"{name}: invalid source fixture")
  let output ← accepted limits cuts input
  returnIpc directory name output observed
  let singleton := observed.batches.map fun rows => (⟨[rows.length], [rows.length]⟩ : PageCuts.BatchCuts)
  let _ ← verifyDefault limits name input singleton

  let exact := { limits with file := { limits.file with writer := { limits.file.writer with
    maxFileBytes := output.length } } }
  let atCap ← accepted exact cuts input
  unless output == atCap do throw (IO.userError s!"{name}: exact file cap changed bytes")
  let short := { exact with file := { exact.file with writer := { exact.file.writer with
    maxFileBytes := output.length - 1 } } }
  refused short cuts input (.sink (.footer .byteLimit))
  refused { limits with maxPages := 9 } cuts input (.cuts (.totalPages 9 10))
  refused { limits with maxPagesPerChunk := 2 } cuts input (.cuts (.chunkPages 0 .byteArray 2 3))
  refused limits [first, empty] input (.cuts (.batchCount 3 2))
  refused limits [{ first with integers := [1, 1] }, empty, third] input (.cuts (.extent 0 .int32 5 2))
  refused limits [first, { empty with octets := [] }, third] input (.cuts (.shape 1 .byteArray))
  refused limits [{ first with integers := [0, 5] }, empty, third] input (.cuts (.shape 0 .int32))

  let late ← load directory (name ++ "-late")
  refused { limits with maxPages := 0 } [] late
    (.source (.reader (.batch 2 (.body (.malformed .truncated)))))
  let missingEOS ← load directory (name ++ "-missing-eos")
  refused { limits with maxPages := 0 } [] missingEOS
    (.source (.reader (.batch 3 (.envelope (.malformed .truncated)))))

  for (suffix, policy, counts) in [("schema-only", [], []), ("empty-batch", [empty], [0])] do
    let fixture := name ++ "-" ++ suffix
    let input ← load directory fixture
    let .ok source := MixedIpc.read {} input
      | throw (IO.userError s!"{fixture}: input was refused")
    unless source.descriptor == observed.descriptor && source.batches.map List.length == counts do
      throw (IO.userError s!"{fixture}: wrong zero-row case")
    let emptyFile := { limits.file with maxGroups := 0, maxTotalRows := 0 }
    let bounded := if policy.isEmpty then
      { limits with maxPages := 0, maxPagesPerChunk := 0, file := emptyFile }
      else limits
    let file ← verifyDefault bounded fixture input policy
    returnIpc directory fixture file source
    if policy.isEmpty then
      refused limits [empty] input (.cuts (.batchCount 0 1))
    else
      refused limits [] input (.cuts (.batchCount 1 0))

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected one fixture directory")
  let directory := System.FilePath.mk path
  checkOrder directory "int-first" false ⟨[2, 3], [1, 1, 3]⟩
  checkOrder directory "byte-first" true ⟨[1, 4], [2, 1, 2]⟩
  IO.println "Six exact round trips, six default-byte comparisons, two exact file caps and twenty-two typed failures."
