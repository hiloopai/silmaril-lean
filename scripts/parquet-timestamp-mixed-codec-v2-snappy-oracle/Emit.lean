module

import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc
open Silmaril.Numeric.Timestamp (Ticks)

private abbrev MixedLimits := Leaf.MixedCodec.V2.WithSnappy.Limits

private abbrev GroupError := Leaf.MixedCodec.V2.WithSnappy.GroupError

private def require {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

private def expectError {ε : Type} [DecidableEq ε] [Repr ε] (label : String) (expected : ε)
    (result : Except ε KBytes) : IO Unit :=
  match result with
  | .error actual => unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected IPC output")

private def observations (directory : System.FilePath) (name : String) :
    IO (List (Int × List (Option Int))) := do
  let text ← IO.FS.readFile (directory / (name ++ ".txt"))
  (text.splitOn "\n").mapM fun line => do
    let code :: words := line.splitOn "," | throw (IO.userError "missing original codec")
    let some codec := code.toInt? | throw (IO.userError s!"invalid original codec {code}")
    let ticks ← words.mapM fun word =>
      if word == "null" then pure none
      else match word.toInt? with
        | some tick => pure (some tick)
        | none => throw (IO.userError s!"invalid signed tick {word}")
    return (codec, ticks)

private def strictRead (limits : MixedLimits) (codec : Int) (bound : Leaf.Bound) (index : Nat) :
    Except GroupError (Leaf.Slots bound) :=
  match codec with
  | 1 => (Leaf.Snappy.Dispatch.V2.readGroup limits.snappy {} bound index).mapError .snappy
  | 2 => (Leaf.Gzip.Dispatch.V2.readGroup limits.twoCodec.gzip {} bound index).mapError (.twoCodec ∘ .gzip)
  | 6 => (Leaf.Zstd.Dispatch.V2.readGroup limits.twoCodec.zstd {} bound index).mapError (.twoCodec ∘ .zstd)
  | other => .error (.twoCodec (.unsupportedCodec other))

private def readSuccess (directory : System.FilePath) (name : String) : IO Unit := do
  let wire ← input directory name
  let expected ← observations directory name
  let bound ← require (openBound {} wire 2)
  unless bound.snapshot.groupCount == expected.length do
    throw (IO.userError s!"{name}: original footer group count differed")
  for ((codec, counts), index) in expected.zipIdx do
    let selected ← require (Leaf.MixedCodec.V2.selectedCodec bound index)
    let slots ← require (Leaf.MixedCodec.V2.WithSnappy.readGroup {} {} bound index)
    let strict ← require (strictRead {} codec bound index)
    unless selected == codec && slots.map (Option.map Ticks.ticks) == counts &&
        strict.map (Option.map Ticks.ticks) == counts do
      throw (IO.userError s!"{name} group {index}: source codec or exact slots differed")
  let emitted ← require (Leaf.MixedCodec.V2.WithSnappy.convert {} {} {} wire 2)
  if expected.all (fun group => group.1 != 1) then
    let previous ← require (Leaf.MixedCodec.V2.convert {} {} {} wire 2)
    unless emitted.toByteArray == previous.toByteArray do
      throw (IO.userError s!"{name}: two-codec IPC bytes differed")
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) emitted.toByteArray

private def checkLate (directory : System.FilePath) (label : String) (limits : MixedLimits)
    (earlier : List (Int × List (Option Int))) (index : Nat) (codec : Int) (cause : GroupError) : IO Unit := do
  let wire ← input directory label
  let bound ← require (openBound {} wire 2)
  unless (← require (Leaf.MixedCodec.V2.selectedCodec bound index)) == codec do
    throw (IO.userError s!"{label}: wrong original codec")
  match strictRead limits codec bound index with
  | .error strict =>
    unless strict == cause do throw (IO.userError s!"{label}: strict cause {repr strict}")
  | .ok _ => throw (IO.userError s!"{label}: strict reader admitted the source group")
  let events := Leaf.MixedCodec.V2.WithSnappy.trace limits {} bound
  let batches := events.batches.map fun batch =>
    Arrow.TimestampBatch.Writer.tickCounts (binding := selectedBinding bound) (batch.values ⟨0, Nat.zero_lt_one⟩)
  unless batches == (earlier.take index).map Prod.snd do
    throw (IO.userError s!"{label}: first failure lost an earlier complete group")
  match events.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{label}: original indexed cause {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected a source group failure")
  expectError label (Leaf.MixedCodec.V2.WithSnappy.Error.source (.groupFailure index cause))
    (Leaf.MixedCodec.V2.WithSnappy.convert limits {} {ipc.batches := 0} wire 2)

private def checkPreviousError (label : String) (wire : Bytes) (inputs : Limits) (output : Arrow.ObservationLimits)
    (expected : Leaf.MixedCodec.V2.Error) : IO Unit := do
  expectError label expected (Leaf.MixedCodec.V2.convert {} inputs output wire 2)
  expectError label (Leaf.MixedCodec.V2.WithSnappy.Error.ofTwoCodec expected)
    (Leaf.MixedCodec.V2.WithSnappy.convert {} inputs output wire 2)

private def crc (declared actual : Nat) : Parquet.Page.Checksum.Error :=
  .mismatch declared.toUInt32 actual.toUInt32

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected fixture folder and original offsets")
  let [some snappyOffset, some snappyDeclared, some snappyActual, some gzipOffset, some gzipDeclared,
       some gzipActual, some zstdOffset, some zstdDeclared, some zstdActual, some priorGzipOffset,
       some priorGzipDeclared, some priorGzipActual, some priorZstdOffset, some priorZstdDeclared,
       some priorZstdActual] := evidence.map String.toNat? |
    throw (IO.userError "bad independent Thrift offsets")
  let directory : System.FilePath := folder
  for label in ["assembled_three_utc", "assembled_three_local", "prior_utc", "prior_local",
                "snappy_native_utc", "snappy_native_local"] do
    readSuccess directory label

  let utc ← observations directory "assembled_three_utc"
  let prior ← observations directory "prior_utc"
  let snappyFailure := Leaf.Error.dictionaryPage 2 snappyOffset
    (.checksumFailure (crc snappyDeclared snappyActual))
  checkLate directory "mutated_snappy_crc" {} utc 6 1 (.snappy snappyFailure)
  checkLate directory "mutated_gzip_crc" {} utc 7 2
    (.twoCodec (.gzip (.pageChecksum 0 gzipOffset (crc gzipDeclared gzipActual))))
  checkLate directory "mutated_zstd_crc" {} utc 8 6
    (.twoCodec (.zstd (.checksum 0 zstdOffset (crc zstdDeclared zstdActual))))
  checkLate directory "mutated_competing_crc" {} utc 6 1 (.snappy snappyFailure)
  checkLate directory "assembled_late_snappy_v1" {} utc 6 1 (.snappy (.page 0 .unsupportedPage))
  checkLate directory "assembled_three_utc" {snappy.maxChunkBytes := 0} utc 3 1 (.snappy .dictionaryChunkLimit)

  let gzipPrior : Leaf.MixedCodec.V2.GroupError := .gzip (.dictionaryPage 1 priorGzipOffset
    (.checksumFailure (crc priorGzipDeclared priorGzipActual)))
  let zstdPrior : Leaf.MixedCodec.V2.GroupError := .zstd (.checksum 0 priorZstdOffset
    (crc priorZstdDeclared priorZstdActual))
  let unknown : Leaf.MixedCodec.V2.GroupError := .unsupportedCodec 0
  let priorFailures := [("prior_bad_gzip_crc", 2, 2, gzipPrior), ("prior_bad_zstd_crc", 3, 6, zstdPrior),
                        ("prior_unsupported", 2, 0, unknown)]
  for (label, index, codec, cause) in priorFailures do
    checkLate directory label {} prior index codec (.twoCodec cause)
    checkPreviousError label (← input directory label) {} {ipc.batches := 0} (.source (.groupFailure index cause))

  let previous ← input directory "prior_utc"
  checkPreviousError "source cap" previous {maxFileBytes := 0} {ipc.batches := 0}
    (.openFailure (.fileByteLimit 0 previous.length))
  checkPreviousError "writer cap" previous {} {ipc.batches := 0} (.writer (.writer (.limit .batches)))
  expectError "two-codec entry point rejects selected Snappy" (.source (.groupFailure 1 (.unsupportedCodec 1)))
    (Leaf.MixedCodec.V2.convert {} {} {} (← input directory "assembled_three_utc") 2)
  IO.println "Thirty-eight selected group reads, twelve typed refusal controls and nine complete prefixes passed"
