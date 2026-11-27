module

import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete.Defs
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
meta import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete.Defs
meta import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Parquet.MixedV1Writer.FromIpc
open Silmaril.Formats.Relational.NamedTable

private def sink : MixedV1Writer.Multi.Limits :=
  ⟨⟨4096, {}, ⟨{}, 32, ⟨128, 128, ⟨16, 32⟩, 0⟩⟩,
    ⟨⟨{}, 32, ⟨128, 128, ⟨16, 32⟩, 0⟩⟩, ⟨128, 32⟩⟩, {}⟩, 5, 3⟩

private def pack (bytes : ByteArray) : KBytes :=
  KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)

private def returnIpc (directory : System.FilePath) (name : String)
    (file : Bytes) (source : MixedIpc.Prepared) : IO Unit := do
  let .ok wire := ToIpc.convertOrdered {} {} file
      (field source.descriptor.integer) (field source.descriptor.binary)
    | throw (IO.userError s!"{name}: reverse failed")
  let .ok read := MixedIpc.read { inputBytes := wire.len } wire
    | throw (IO.userError s!"{name}: native readback failed")
  unless read.descriptor == source.descriptor && read.batches == source.batches do
    throw (IO.userError s!"{name}: expected the exact descriptor and batch list")
  IO.FS.writeBinFile (directory / (name ++ "-returned.arrows")) wire.toByteArray

private def checkOrder (directory : System.FilePath) (name : String) (viewFirst : Bool) : IO Unit := do
  let bytes ← IO.FS.readBinFile (directory / (name ++ ".arrows"))
  let input := pack bytes
  let .ok observation := MixedIpc.read {} input
    | throw (IO.userError s!"{name}: input failed")
  unless observation.descriptor.viewFirst == viewFirst && observation.batches.isEmpty do
    throw (IO.userError s!"{name}: invalid schema-only fixture")
  let .ok output := SchemaOnly.convert {} { sink with maxGroups := 0 } input
    | throw (IO.userError s!"{name}: opt-in converter failed")
  let .ok unified := Complete.convert {} { sink with maxGroups := 0, maxTotalRows := 0 } input
    | throw (IO.userError s!"{name}: unified zero-batch branch failed")
  unless unified.bytes == output.bytes do
    throw (IO.userError s!"{name}: unified zero-batch bytes changed")
  let .ok exactCap := SchemaOnly.convert {} { sink with writer := { sink.writer with maxFileBytes := output.bytes.length } } input
    | throw (IO.userError s!"{name}: exact file cap refused")
  unless output.footer.start == 4 && output.groups.isEmpty && output.bytes == exactCap.bytes do
    throw (IO.userError s!"{name}: expected footer immediately after PAR1")
  let capped := { sink with writer := { sink.writer with maxFileBytes := output.bytes.length - 1 } }
  let .error (.sink cause) := SchemaOnly.convert {} capped input
    | throw (IO.userError s!"{name}: one byte short cap accepted")
  let .error (.sink unifiedCause) := Complete.convert {} capped input
    | throw (IO.userError s!"{name}: unified zero-batch cap accepted")
  unless unifiedCause == cause do
    throw (IO.userError s!"{name}: unified zero-batch cap changed cause")
  let .error (.plan .noBatches) := convertOrdered {} sink input
    | throw (IO.userError s!"{name}: regular ordered converter's refusal changed")
  let missingEOS := pack (bytes.extract 0 (bytes.size - 8))
  let .error (.source (.reader (.batch 0 (.envelope (.malformed .truncated))))) :=
      SchemaOnly.convert {} { sink with writer := { sink.writer with maxFileBytes := 0 } } missingEOS
    | throw (IO.userError s!"{name}: exact EOS error did not precede the sink cap")
  IO.FS.writeBinFile (directory / (name ++ "-lean.parquet")) output.bytes.data
  returnIpc directory (name ++ "-lean") output.bytes observation

  let external ← IO.FS.readBinFile (directory / (name ++ "-pyarrow.parquet"))
  returnIpc directory (name ++ "-pyarrow") ⟨external⟩ observation

  let emptyName := name ++ "-empty"
  let emptyInput := pack (← IO.FS.readBinFile (directory / (emptyName ++ ".arrows")))
  let .error (.batchCount 1) := SchemaOnly.convert {} sink emptyInput
    | throw (IO.userError s!"{name}: explicit empty batch was accepted as schema-only")
  let .ok empty := MixedIpc.read {} emptyInput
    | throw (IO.userError s!"{name}: empty batch admission failed")
  unless empty.descriptor == observation.descriptor && empty.batches == [[]] do
    throw (IO.userError s!"{name}: wrong empty-batch fixture")
  let .ok file := convertOrdered {} sink emptyInput
    | throw (IO.userError s!"{name}: regular one-group converter refused the empty batch")
  let .ok unifiedEmpty := Complete.convert {} sink emptyInput
    | throw (IO.userError s!"{name}: unified converter refused the explicit empty batch")
  unless unifiedEmpty.bytes == file.bytes do
    throw (IO.userError s!"{name}: one-empty-batch bytes changed")
  IO.FS.writeBinFile (directory / (emptyName ++ ".parquet")) file.bytes.data
  returnIpc directory emptyName file.bytes empty

private def checkAlternating (directory : System.FilePath) (name : String) (viewFirst : Bool) : IO Unit := do
  let fixture := name ++ "-alternating"
  let input := pack (← IO.FS.readBinFile (directory / (fixture ++ ".arrows")))
  let .ok observation := MixedIpc.read {} input
    | throw (IO.userError s!"{name}: alternating input failed")
  unless observation.descriptor.viewFirst == viewFirst &&
      observation.batches.map List.length == [0, 2, 0, 1, 0] do
    throw (IO.userError s!"{name}: wrong order or empty batch positions")
  let .ok explicit := convertOrdered {} sink input
    | throw (IO.userError s!"{name}: explicit ordered adapter failed")
  let .ok unified := Complete.convert {} sink input
    | throw (IO.userError s!"{name}: unified nonempty branch failed")
  unless unified.bytes == explicit.bytes do
    throw (IO.userError s!"{name}: unified nonempty bytes changed")
  IO.FS.writeBinFile (directory / (fixture ++ ".parquet")) unified.bytes.data
  returnIpc directory fixture unified.bytes observation

  let groupCap := { sink with maxGroups := 4 }
  let .error (.sink .groupLimit) := Complete.convert {} groupCap input
    | throw (IO.userError s!"{name}: unified group cap ignored an explicit empty batch")
  let .error (.sink .groupLimit) := convertOrdered {} groupCap input
    | throw (IO.userError s!"{name}: explicit ordered branch changed group cap")

  for (kind, cause) in [
      ("body", MixedIpc.Error.reader (.batch 3 (.body (.malformed .truncated)))),
      ("eos", MixedIpc.Error.reader (.batch 5 (.envelope (.malformed .truncated))))] do
    let damaged := pack (← IO.FS.readBinFile (directory / (fixture ++ "-late-" ++ kind ++ ".arrows")))
    let .error (.source actual) := Complete.convert {} { sink with maxGroups := 0 } damaged
      | throw (IO.userError s!"{name}: late {kind} failure did not precede sink work")
    let .error (.source explicitCause) := convertOrdered {} sink damaged
      | throw (IO.userError s!"{name}: explicit ordered branch lost late {kind} failure")
    let .error (.source schemaOnlyCause) := SchemaOnly.convert {} sink damaged
      | throw (IO.userError s!"{name}: explicit zero-batch branch lost late {kind} failure")
    unless actual == cause && explicitCause == cause && schemaOnlyCause == cause do
      throw (IO.userError s!"{name}: wrong late {kind} failure: {repr actual}")

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected one fixture directory")
  let directory := System.FilePath.mk path
  checkOrder directory "int-first" false
  checkOrder directory "byte-first" true
  checkAlternating directory "int-first" false
  checkAlternating directory "byte-first" true
  IO.println "Both unified branches match explicit bytes and caps, and preserve late indexed IPC errors."
