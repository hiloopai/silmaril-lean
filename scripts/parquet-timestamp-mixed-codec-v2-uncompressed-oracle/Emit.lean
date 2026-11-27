module

import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc
open Silmaril.Numeric.Timestamp (Ticks)

private abbrev MixedLimits := Leaf.MixedCodec.V2.WithUncompressed.Limits

private abbrev GroupError := Leaf.MixedCodec.V2.WithUncompressed.GroupError

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
  | 0 => (Leaf.Uncompressed.Dispatch.V2.readGroup limits.uncompressed {} bound index).mapError .uncompressed
  | 1 => (Leaf.Snappy.Dispatch.V2.readGroup limits.threeCodec.snappy {} bound index).mapError
      (.threeCodec ∘ .snappy)
  | 2 => (Leaf.Gzip.Dispatch.V2.readGroup limits.threeCodec.twoCodec.gzip {} bound index).mapError
      (.threeCodec ∘ .twoCodec ∘ .gzip)
  | 6 => (Leaf.Zstd.Dispatch.V2.readGroup limits.threeCodec.twoCodec.zstd {} bound index).mapError
      (.threeCodec ∘ .twoCodec ∘ .zstd)
  | other => .error (.threeCodec (.twoCodec (.unsupportedCodec other)))

private def readSuccess (directory : System.FilePath) (name : String) : IO Unit := do
  let wire ← input directory name
  let expected ← observations directory name
  let bound ← require (openBound {} wire 2)
  unless bound.snapshot.groupCount == expected.length do
    throw (IO.userError s!"{name}: original footer group count differed")
  for ((codec, counts), index) in expected.zipIdx do
    let selected ← require (Leaf.MixedCodec.V2.selectedCodec bound index)
    let slots ← require (Leaf.MixedCodec.V2.WithUncompressed.readGroup {} {} bound index)
    let strict ← require (strictRead {} codec bound index)
    unless selected == codec && slots.map (Option.map Ticks.ticks) == counts &&
        strict.map (Option.map Ticks.ticks) == counts do
      throw (IO.userError s!"{name} group {index}: source codec or exact slots differed")
  let emitted ← require (Leaf.MixedCodec.V2.WithUncompressed.convert {} {} {} wire 2)
  if expected.all (fun group => group.1 != 0) then
    let previous ← require (Leaf.MixedCodec.V2.WithSnappy.convert {} {} {} wire 2)
    unless emitted.toByteArray == previous.toByteArray do
      throw (IO.userError s!"{name}: three-codec IPC bytes differed")
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
  let events := Leaf.MixedCodec.V2.WithUncompressed.trace limits {} bound
  let batches := events.batches.map fun batch =>
    Arrow.TimestampBatch.Writer.tickCounts (binding := selectedBinding bound) (batch.values ⟨0, Nat.zero_lt_one⟩)
  unless batches == (earlier.take index).map Prod.snd do
    throw (IO.userError s!"{label}: first failure lost an earlier complete group")
  match events.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{label}: original indexed cause {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected a source group failure")
  expectError label (Leaf.MixedCodec.V2.WithUncompressed.Error.source (.groupFailure index cause))
    (Leaf.MixedCodec.V2.WithUncompressed.convert limits {} {ipc.batches := 0} wire 2)

private def checkPreviousError (label : String) (wire : Bytes) (inputs : Limits) (output : Arrow.ObservationLimits)
    (expected : Leaf.MixedCodec.V2.WithSnappy.Error) : IO Unit := do
  expectError label expected (Leaf.MixedCodec.V2.WithSnappy.convert {} inputs output wire 2)
  expectError label (Leaf.MixedCodec.V2.WithUncompressed.Error.ofThreeCodec expected)
    (Leaf.MixedCodec.V2.WithUncompressed.convert {} inputs output wire 2)

private def crc (declared actual : Nat) : Parquet.Page.Checksum.Error :=
  .mismatch declared.toUInt32 actual.toUInt32

private def pageCRC (ordinal offset declared actual : Nat) : Leaf.Error :=
  .dictionaryPage ordinal offset (.checksumFailure (crc declared actual))

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected fixture folder and original offsets")
  let [some snappyOffset, some snappyDeclared, some snappyActual, some zeroOffset, some zeroDeclared,
       some zeroActual, some gzipOffset, some gzipDeclared, some gzipActual, some zstdOffset,
       some zstdDeclared, some zstdActual, some priorSnappyOffset, some priorSnappyDeclared,
       some priorSnappyActual, some priorGzipOffset, some priorGzipDeclared, some priorGzipActual,
       some priorZstdOffset, some priorZstdDeclared, some priorZstdActual] := evidence.map String.toNat? |
    throw (IO.userError "bad independent Thrift offsets")
  let directory : System.FilePath := folder
  for label in ["assembled_four_utc", "assembled_four_local", "previous_utc", "previous_local",
                "native_utc_plain", "native_utc_references", "native_utc_fallback",
                "native_local_plain", "native_local_references", "native_local_fallback"] do
    readSuccess directory label

  let utc ← observations directory "assembled_four_utc"
  let prior ← observations directory "previous_utc"
  let snappyFailure := pageCRC 2 snappyOffset snappyDeclared snappyActual
  checkLate directory "mutated_snappy_crc" {} utc 8 1 (.threeCodec (.snappy snappyFailure))
  checkLate directory "mutated_uncompressed_crc" {} utc 9 0
    (.uncompressed (pageCRC 2 zeroOffset zeroDeclared zeroActual))
  checkLate directory "mutated_gzip_crc" {} utc 10 2
    (.threeCodec (.twoCodec (.gzip (.pageChecksum 0 gzipOffset (crc gzipDeclared gzipActual)))))
  checkLate directory "mutated_zstd_crc" {} utc 11 6
    (.threeCodec (.twoCodec (.zstd (.checksum 0 zstdOffset (crc zstdDeclared zstdActual)))))
  checkLate directory "mutated_competing_crc" {} utc 8 1 (.threeCodec (.snappy snappyFailure))
  checkLate directory "assembled_four_utc" {uncompressed.maxChunkBytes := 0} utc 6 0
    (.uncompressed .dictionaryChunkLimit)

  let previousFailures : List (String × Nat × Int × Leaf.MixedCodec.V2.WithSnappy.GroupError) :=
    [("previous_bad_snappy_crc", 6, 1, .snappy (pageCRC 2 priorSnappyOffset priorSnappyDeclared priorSnappyActual)),
     ("previous_bad_gzip_crc", 7, 2, .twoCodec (.gzip
       (.pageChecksum 0 priorGzipOffset (crc priorGzipDeclared priorGzipActual)))),
     ("previous_bad_zstd_crc", 8, 6, .twoCodec (.zstd
       (.checksum 0 priorZstdOffset (crc priorZstdDeclared priorZstdActual)))),
     ("previous_late_snappy_v1", 6, 1, .snappy (.page 0 .unsupportedPage)),
     ("previous_unknown_codec", 6, 7, .twoCodec (.unsupportedCodec 7))]
  for (label, index, codec, cause) in previousFailures do
    checkLate directory label {} prior index codec (.threeCodec cause)
    checkPreviousError label (← input directory label) {} {ipc.batches := 0} (.source (.groupFailure index cause))

  let previous ← input directory "previous_utc"
  checkPreviousError "source cap" previous {maxFileBytes := 0} {ipc.batches := 0}
    (.openFailure (.fileByteLimit 0 previous.length))
  checkPreviousError "writer cap" previous {} {ipc.batches := 0} (.writer (.writer (.limit .batches)))
  expectError "three-codec entry point rejects selected codec 0"
    (.source (.groupFailure 2 (.twoCodec (.unsupportedCodec 0))))
    (Leaf.MixedCodec.V2.WithSnappy.convert {} {} {} (← input directory "assembled_four_utc") 2)
  let bound ← require (openBound {} previous 2)
  let absent := bound.snapshot.groupCount
  match Leaf.MixedCodec.V2.WithSnappy.readGroup {} {} bound absent,
      Leaf.MixedCodec.V2.WithUncompressed.readGroup {} {} bound absent with
  | .error earlier, .error actual =>
    unless earlier == .twoCodec (.selection (.groupIndex absent)) && actual == .threeCodec earlier do
      throw (IO.userError "group lookup did not preserve the original typed error")
  | _, _ => throw (IO.userError "group lookup unexpectedly decoded a group")
  IO.println "Sixty selected group reads, fifteen typed refusal controls and eleven complete prefixes passed"
