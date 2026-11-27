module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.Defs

open Silmaril Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Projection
open Silmaril.Numeric.Timestamp (TickUnit Ticks)

private abbrev SourceError := Leaf.Projection.Error

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun bytes => ⟨bytes⟩

private def require {α : Type} (result : Except SourceError α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def unitName : TickUnit → String
  | .second => "s"
  | .millisecond => "ms"
  | .microsecond => "us"
  | .nanosecond => "ns"

private def describe {schema : Scan.Schema String Leaf.Events.Kind}
    (trace : Arrow.Events.Trace schema Leaf.Events.Cell SourceError) : String :=
  let fields := List.ofFn fun i =>
    let (name, kind) := schema.kind i
    s!"{name},{unitName kind.metadata.unit},{kind.metadata.timezone.getD ""},{kind.nullable}"
  let batches := trace.batches.map fun batch =>
    let cols := List.ofFn fun i => ",".intercalate ((batch.values i).map fun value =>
      value.elim "null" (fun tick => toString tick.ticks))
    "|".intercalate (toString batch.rowCount :: cols)
  "\n".intercalate (("schema|" ++ "|".intercalate fields) :: batches)

private def expectTrace (directory : System.FilePath) (name : String)
    {schema : Scan.Schema String Leaf.Events.Kind}
    (trace : Arrow.Events.Trace schema Leaf.Events.Cell SourceError)
    (termination : Arrow.Events.Termination SourceError := .eos) : IO Unit := do
  let expected ← IO.FS.readFile (directory / (name ++ ".txt"))
  unless trace.termination = termination do
    throw (IO.userError s!"{name}: terminal outcome differed")
  unless describe trace == expected do
    throw (IO.userError s!"{name}: descriptors, row counts or signed values differed")

private def select (schema : Scan.Schema String Leaf.Events.Kind) (positions : Array Nat) :
    IO (Scan.Projection schema) := do
  let indices ← positions.mapM fun position =>
    if valid : position < schema.width then pure (⟨position, valid⟩ : Fin schema.width)
    else throw (IO.userError s!"invalid selected position {position}")
  return Scan.Projection.ofArray indices

private def expectBind (wire : Bytes) (request : Array Nat) (index ordinal : Nat) : IO Unit := do
  match readAll {} wire request with
  | .error (.bind actualPos actualOrd _) =>
    unless actualPos == index && actualOrd == ordinal do
      throw (IO.userError "incorrect projected binding position")
  | .error cause => throw (IO.userError s!"expected binding refusal, got {repr cause}")
  | .ok _ => throw (IO.userError "unexpectedly opened invalid projection")

public def main (args : List String) : IO Unit := do
  let [folder, offset, declared, actual] := args | throw (IO.userError "expected fixture folder and CRC evidence")
  let [some offset, some declared, some actual] := [offset, declared, actual].map String.toNat? |
    throw (IO.userError "invalid independent CRC evidence")
  let directory : System.FilePath := folder

  for name in ["native_v1", "native_v2", "native_schema_only"] do
    let wire ← input directory name
    let ⟨_, trace⟩ ← require (readAll {} wire #[4, 2, 3, 2])
    expectTrace directory name trace

  let wire ← input directory "native_v1"
  let checked ← require (openFile {} wire #[4, 2, 3, 2])
  let reorder ← select checked.schema #[2, 0]
  expectTrace directory "v1_subset" ((checked.trace {}).scan reorder (fun _ => some true))
  expectTrace directory "v1_subset" ((checked.project reorder).trace {})
  let ⟨_, direct⟩ ← require (readAll {} wire #[3, 4])
  expectTrace directory "v1_subset" direct
  let ⟨_, empty⟩ ← require (readAll {} wire #[])
  expectTrace directory "v1_empty" empty
  let emptyProjection ← select checked.schema #[]
  expectTrace directory "v1_empty" ((checked.trace {}).scan emptyProjection (fun _ => some true))

  let bad ← input directory "mutated_late_local_dictionary_crc"
  let cause : SourceError := .read 1 1 3 (.v1 .zstd (.checksum 0 offset (.mismatch declared.toUInt32 actual.toUInt32)))
  let wide ← require (openFile {} bad #[4, 3, 2])
  let wideTrace := wide.trace {}
  expectTrace directory "late_wide" wideTrace (.readError cause)
  let ⟨_, reorderedFault⟩ ← require (readAll {} bad #[3, 4, 2])
  expectTrace directory "late_reordered" reorderedFault
    (.readError (.read 1 0 3 (.v1 .zstd (.checksum 0 offset (.mismatch declared.toUInt32 actual.toUInt32)))))
  let projected ← select wide.schema #[0, 2]
  expectTrace directory "late_filtered" (wideTrace.scan projected (fun _ => some true)) (.readError cause)
  expectTrace directory "late_direct" ((wide.project projected).trace {})
  let ⟨_, surviving⟩ ← require (readAll {} bad #[4, 2])
  expectTrace directory "late_direct" surviving
  let ⟨_, emptyBad⟩ ← require (readAll {} bad #[])
  expectTrace directory "v1_empty" emptyBad

  expectBind wire #[2, 0, 99] 1 0
  expectBind wire #[3, 1, 0] 1 1
  expectBind wire #[4, 9] 1 9
  match readAll {maxFields := 1} wire #[2, 2] with
  | .error (.fieldLimit 1 2) => pure ()
  | _ => throw (IO.userError "duplicate field count cap differed")
  let ⟨_, capped⟩ ← require (readAll {input.leaf.maxRows := 0} wire #[])
  unless capped.batches.isEmpty && decide (capped.termination = .readError (.groupRowLimit 0 0 512)) do
    throw (IO.userError "empty projection skipped the footer row cap")
  IO.println "Verified native V1/V2 and schema-only Events, reordering, duplicates, empty counts, and late CRC selection"
