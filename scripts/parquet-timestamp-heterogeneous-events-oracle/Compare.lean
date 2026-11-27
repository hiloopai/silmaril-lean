module

import Silmaril.Formats.Parquet.FlatProjection.Events.Defs
meta import Silmaril.Formats.Parquet.FlatProjection.Events.Defs

open Silmaril Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Parquet.FlatProjection.Events
open Silmaril.Numeric.Timestamp (TickUnit)

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun bytes => ⟨bytes⟩

private def require {α : Type} (result : Except Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def unitName : TickUnit → String
  | .second => "s"
  | .millisecond => "ms"
  | .microsecond => "us"
  | .nanosecond => "ns"

private def describeKind : Kind → String
  | .int32 nullable => s!"int32,{nullable}"
  | .utf8 nullable => s!"utf8,{nullable}"
  | .timestamp kind =>
    s!"{unitName kind.metadata.unit},{kind.metadata.timezone.getD ""},{kind.nullable}"

private def describeCell : (kind : Kind) → Cell kind → String
  | .int32 _, value => toString value.toInt
  | .utf8 _, value => "text:" ++ (show String from value)
  | .timestamp _, value => toString value.ticks

private def describe {schema : Scan.Schema String Kind}
    (trace : Arrow.Events.Trace schema Cell Error) : String :=
  let fields := List.ofFn fun i =>
    let (name, kind) := schema.kind i
    s!"{name},{describeKind kind}"
  let batches := trace.batches.map fun batch =>
    let cols := List.ofFn fun i => ",".intercalate ((batch.values i).map fun value =>
      value.elim "null" (describeCell (schema.kind i).2))
    "|".intercalate (toString batch.rowCount :: cols)
  "\n".intercalate (("schema|" ++ "|".intercalate fields) :: batches)

private def expectTrace (directory : System.FilePath) (name : String)
    {schema : Scan.Schema String Kind} (trace : Arrow.Events.Trace schema Cell Error)
    (termination : Arrow.Events.Termination Error := .eos) : IO Unit := do
  let expected ← IO.FS.readFile (directory / (name ++ ".txt"))
  unless trace.termination = termination do
    match trace.termination with
    | .readError cause | .closeError cause => throw (IO.userError s!"{name}: {repr cause}")
    | .eos | .closed => throw (IO.userError s!"{name}: terminal outcome differed")
  unless describe trace == expected do
    throw (IO.userError s!"{name}: descriptors, counts or typed cells differed\n{describe trace}")

private def select (schema : Scan.Schema String Kind) (positions : Array Nat) :
    IO (Scan.Projection schema) := do
  let indices ← positions.mapM fun position =>
    if valid : position < schema.width then pure (⟨position, valid⟩ : Fin schema.width)
    else throw (IO.userError s!"invalid selected position {position}")
  return Scan.Projection.ofArray indices

public def main (args : List String) : IO Unit := do
  let [folder, offset] := args | throw (IO.userError "expected fixture folder and dictionary header offset")
  let some offset := offset.toNat? | throw (IO.userError "invalid dictionary header offset")
  let directory : System.FilePath := folder
  let wideOrdinals := #[3, 0, 1, 2, 1]
  let narrowOrdinals := #[1, 3, 0]
  for name in ["native_v1", "native_v2", "native_schema_only"] do
    let wire ← input directory name
    let ⟨_, trace⟩ ← require (readAll {} wire wideOrdinals)
    expectTrace directory name trace
  let wire ← input directory "native_v1"
  let checked ← require (openFile {} wire wideOrdinals)
  let reorder ← select checked.schema #[2, 0, 1]
  expectTrace directory "reordered" ((checked.trace {}).scan reorder (fun _ => some true))
  expectTrace directory "reordered" ((checked.project reorder).trace {})
  let ⟨_, direct⟩ ← require (readAll {} wire narrowOrdinals)
  expectTrace directory "reordered" direct
  let ⟨_, empty⟩ ← require (readAll {} wire #[])
  expectTrace directory "empty" empty
  let emptyProjection ← select checked.schema #[]
  expectTrace directory "empty" ((checked.trace {}).scan emptyProjection (fun _ => some true))

  let bad ← input directory "mutated_late_timestamp_dictionary_magic"
  let cause : ColumnError := .timestamp (.v1 .zstd
    (.decode 0 offset (.frame (.frame .badMagic))))
  let wide ← require (openFile {} bad wideOrdinals)
  let failed := Arrow.Events.Termination.readError (.column 1 3 2 cause)
  expectTrace directory "late_wide" (wide.trace {}) failed
  let ⟨_, reorderedFault⟩ ← require (readAll {} bad #[2, 1, 0])
  expectTrace directory "late_reordered" reorderedFault (.readError (.column 1 0 2 cause))
  let narrow ← select wide.schema #[2, 0, 1]
  expectTrace directory "late_logical" ((wide.trace {}).scan narrow (fun _ => some true)) failed
  expectTrace directory "reordered" ((wide.project narrow).trace {})
  let ⟨_, surviving⟩ ← require (readAll {} bad narrowOrdinals)
  expectTrace directory "reordered" surviving
  let ⟨_, emptyBad⟩ ← require (readAll {} bad #[])
  expectTrace directory "empty" emptyBad

  let checksummed ← input directory "native_checksummed_v1"
  let ⟨_, refused⟩ ← require (readAll {} checksummed #[0, 2])
  unless refused.batches.isEmpty &&
      decide (refused.termination = .readError (.column 0 0 0 (.int32 (.page 0 0 "code" 0 4 .crcUnsupported)))) do
    throw (IO.userError "existing primitive CRC refusal differed")

  let unannotated ← input directory "native_unannotated_binary"
  match readAll {} unannotated #[0, 1] with
  | .error (.bind 1 1 (.utf8 .missingAnnotation)) => pure ()
  | _ => throw (IO.userError "opaque BYTE_ARRAY was not refused as UTF8")
  match readAll {} wire #[0, 5] with
  | .error (.bind 1 5 (.primitive .missingLeaf)) => pure ()
  | _ => throw (IO.userError "out-of-range binding did not retain its position")
  match readAll {primitive.maxFields := 1} wire #[0, 0] with
  | .error (.fieldLimit 1 2) => pure ()
  | _ => throw (IO.userError "repeated fields did not count against the field cap")
  let ⟨_, capped⟩ ← require (readAll {primitive.column.column.maxRows := 0} wire #[])
  unless capped.batches.isEmpty && decide (capped.termination = .readError (.groupRowLimit 0 0 5)) do
    throw (IO.userError "empty selection did not preserve the shared row cap")
  IO.println "Verified heterogeneous typed Events, reordered and empty selections, and indexed late Zstandard failure and complete prefix"
