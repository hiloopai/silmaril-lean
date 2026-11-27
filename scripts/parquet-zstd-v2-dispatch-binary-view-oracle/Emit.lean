module

import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2.Defs
meta import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.ByteArrayFallback
open Arrow.BinaryView

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

private def bindBlob (input : Bytes) : IO (Snappy.Checked "blob") := do
  let .ok checked := Snappy.openFile {} input "blob" | throw (IO.userError "opaque leaf binding failed")
  return checked

private def groupProfile (checked : Snappy.Checked "blob") (index : Nat) : IO Zstd.Dispatch.V2.Profile := do
  let snapshot := checked.physical.snapshot
  let some group := snapshot.groupAt index | throw (IO.userError "missing original group")
  let some chunk := group.columns[checked.physical.binding.columnOrdinal]? |
    throw (IO.userError "missing selected column")
  let some span := Page.columnSpan snapshot.footer.start chunk.metadata |
    throw (IO.userError "missing selected span")
  let .ok frames := Page.readChunk {} snapshot.bytes span |
    throw (IO.userError "could not frame original selected chunk")
  return Zstd.Dispatch.V2.profile frames

private def strictRead (limits : Zstd.Dispatch.V2.Limits) (checked : Snappy.Checked "blob")
    (index : Nat) (profile : Zstd.Dispatch.V2.Profile) :
    Except Zstd.Dispatch.V2.GroupError (List (Option Bytes)) :=
  match profile with
  | .plain =>
    (Zstd.Plain.V2.readGroup (Zstd.Fallback.V2.plainLimits limits) checked index)
      |>.mapError (Zstd.Dispatch.V2.liftGroupError .plain)
  | .dictionary =>
    (Zstd.Dictionary.V2.readGroup limits checked index)
      |>.mapError (Zstd.Dispatch.V2.liftGroupError .dictionary)
  | .fallback =>
    (Zstd.Fallback.V2.readGroup limits checked index)
      |>.mapError (Zstd.Dispatch.V2.liftGroupError .fallback)

private def sameResult (actual expected : Except Zstd.Dispatch.V2.GroupError (List (Option Bytes))) :
    IO Unit :=
  match actual, expected with
  | .ok observed, .ok wanted =>
    unless observed == wanted do throw (IO.userError "selected strict slots differ")
  | .error observed, .error wanted =>
    unless observed == wanted do throw (IO.userError "selected strict typed cause differs")
  | _, _ => throw (IO.userError "selected strict acceptance differs")

private def checkStrict (checked : Snappy.Checked "blob") (index : Nat) (profile : Zstd.Dispatch.V2.Profile) :
    IO Unit := do
  let original ← groupProfile checked index
  unless original == profile do throw (IO.userError "unexpected original header route")
  sameResult (Zstd.Dispatch.V2.readGroup {} checked index) (strictRead {} checked index profile)

private def traceSlots (checked : Snappy.Checked "blob") (expected : Option Zstd.Dispatch.V2.GroupError) :
    IO (List (List (Option Bytes))) := do
  let .ok ⟨selected, trace⟩ := Zstd.Dispatch.V2.readAll {} checked |
    throw (IO.userError "expected a checked source trace")
  unless selected.width == 1 && List.ofFn selected.kind == [("blob", .optional)] do
    throw (IO.userError "unexpected selected descriptor")
  match trace.termination, expected with
  | .eos, none => pure ()
  | .readError actual, some wanted =>
    unless actual == wanted do throw (IO.userError s!"wrong original source termination {repr actual}")
  | _, _ => throw (IO.userError "unexpected source termination")
  if valid : 0 < selected.width then
    return trace.batches.map (·.values ⟨0, valid⟩)
  else
    throw (IO.userError "missing selected column")

private def rejectLate (directory : System.FilePath) (file : String) (index : Nat)
    (profile : Zstd.Dispatch.V2.Profile) (earlier : List (List (Option Bytes)))
    (expected : Zstd.Dispatch.V2.GroupError) : IO Unit := do
  let input ← load directory file
  let checked ← bindBlob input
  checkStrict checked index profile
  let slots ← traceSlots checked (some expected)
  unless slots == earlier.take index do throw (IO.userError s!"completed group prefix differs for {file}")
  let .error (.column actual) := Zstd.Dispatch.V2.convert {} { fields := 0 } {} input "blob" |
    throw (IO.userError s!"expected source refusal before IPC admission for {file}")
  unless actual == expected do throw (IO.userError s!"wrong indexed cause for {file}: {repr actual}")

public def main (args : List String) : IO Unit := do
  let path :: fields := args | throw (IO.userError "expected fixture directory and coordinates")
  let some [plainOffset, dictOffset, revivalOffset, plainWant, plainGot, dictWant, dictGot] :=
    fields.mapM String.toNat? | throw (IO.userError "invalid indexed fixture evidence")
  let directory := System.FilePath.mk path
  let profiles : List (String × List Zstd.Dispatch.V2.Profile × List Nat) :=
    [("native-plain", [.plain, .plain], [65, 33]),
     ("native-dictionary", [.dictionary, .dictionary, .dictionary], [257, 129, 128]),
     ("native-fallback", [.fallback, .fallback], [1025, 1026]),
     ("assembled-mixed", [.dictionary, .plain, .fallback, .dictionary], [257, 65, 1026, 128])]
  for (file, order, counts) in profiles do
    let input ← load directory file
    let checked ← bindBlob input
    for (profile, index) in order.zipIdx do checkStrict checked index profile
    let observed ← traceSlots checked none
    let .ok wire := Zstd.Dispatch.V2.convert {} {} {} input "blob" |
      throw (IO.userError s!"conversion failed for {file}")
    let .ok ⟨⟨"blob", true, .binary⟩, batches⟩ := Stream.read {} {} wire |
      throw (IO.userError "native BinaryView descriptor or EOS failed")
    unless batches.map List.length == counts &&
        batches.map (List.map (Option.map KBytes.toList)) == observed.map (List.map (Option.map Bytes.toList)) do
      throw (IO.userError "Events and BinaryView slots differ")
    IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray

  let mixed ← load directory "assembled-mixed"
  let checked ← bindBlob mixed
  let earlier ← traceSlots checked none
  let crcError (want got : Nat) : Page.Checksum.Error := .mismatch (UInt32.ofNat want) (UInt32.ofNat got)
  let plain := FlatColumn.Error.page 1 1 "blob" 0 plainOffset (.checksum (crcError plainWant plainGot))
  rejectLate directory "assembled-bad-plain-crc" 1 .plain earlier plain
  rejectLate directory "assembled-double-crc" 1 .plain earlier plain
  rejectLate directory "assembled-bad-dictionary-crc" 3 .dictionary earlier
    (.page 3 1 "blob" 0 dictOffset (.checksum (crcError dictWant dictGot)))
  rejectLate directory "assembled-revival" 2 .fallback earlier
    (.page 2 1 "blob" 4 revivalOffset (.decode (.fallback .dictionaryAfterPlain)))

  let limits : Zstd.Dispatch.V2.Limits := { toPhysical := { file := { column := { maxChunkBytes := 0 } } } }
  let actual := Zstd.Dispatch.V2.readGroup limits checked 0
  let .error (.column 0 1 "blob" .chunkLimit) := actual |
    throw (IO.userError "expected shared stored-chunk cap before framing")
  for profile in [Zstd.Dispatch.V2.Profile.plain, .dictionary, .fallback] do
    sameResult actual (strictRead limits checked 0 profile)
  let .error (.writer _) := Zstd.Dispatch.V2.convert {} { fields := 0 } {} mixed "blob" |
    throw (IO.userError "IPC did not refuse the successful source at the configured cap")
  IO.println "Lean checked exact selected strict results, original error coordinates, complete prefix and BinaryView EOS"
