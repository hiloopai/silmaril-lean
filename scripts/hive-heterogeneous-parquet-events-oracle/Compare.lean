module

import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.Defs

open Silmaril Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Hive.Manifest.Heterogeneous
open Silmaril.Formats.Parquet.FlatProjection.Events (Kind Cell)
open Silmaril.Numeric.Timestamp (TickUnit)

private def declared : Schema :=
  { fields := #[
      ⟨3, "local_us", .timestamp ⟨⟨.microsecond, none⟩, false⟩⟩,
      ⟨0, "code", .int32 false⟩,
      ⟨1, "label", .utf8 true⟩,
      ⟨2, "utc_ns", .timestamp ⟨⟨.nanosecond, some "UTC"⟩, true⟩⟩,
      ⟨1, "label", .utf8 true⟩]
    partitions := ⟨#[⟨"region", .utf8 true, .asNull⟩, ⟨"rank", .int32 false, .reject⟩]⟩ }

private def load (root : System.FilePath) (paths : List String) : IO (List Entry) :=
  paths.mapM fun (path : String) => do
    let bytes ← IO.FS.readBinFile (root / path)
    return ⟨path, ⟨bytes⟩⟩

private def require {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
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

private def compare (directory : System.FilePath) (name : String)
    {schema : Scan.Schema String Kind} (trace : Arrow.Events.Trace schema Cell Error) : IO Unit := do
  let expected ← IO.FS.readFile (directory / (name ++ ".txt"))
  unless describe trace == expected do
    throw (IO.userError s!"{name}: schema, order, counts or cells differed\n{describe trace}")

private def requireEos {schema : Scan.Schema String Kind} (trace : Arrow.Events.Trace schema Cell Error) : IO Unit :=
  match trace.termination with
  | .eos => pure ()
  | .readError cause | .closeError cause => throw (IO.userError s!"{repr cause}")
  | .closed => throw (IO.userError "unexpected early close")

private def expectLate {schema : Scan.Schema String Kind} (trace : Arrow.Events.Trace schema Cell Error)
    (path : String) (offset : Nat) : IO Unit :=
  match trace.termination with
  | .readError (.file 1 found (.readParquet (.column 1 3 2 (.timestamp
      (.v1 .zstd (.decode 0 start (.frame (.frame .badMagic)))))))) =>
    unless found == path && offset == start do
      throw (IO.userError "late error path or dictionary offset differed")
  | .readError cause | .closeError cause => throw (IO.userError s!"wrong late cause {repr cause}")
  | .closed | .eos => throw (IO.userError "selected late failure was lost")

private def select (schema : Scan.Schema String Kind) (positions : Array Nat) :
    IO (Scan.Projection schema) := do
  let indices ← positions.mapM fun position =>
    if valid : position < schema.width then pure (⟨position, valid⟩ : Fin schema.width)
    else throw (IO.userError s!"invalid projected position {position}")
  return Scan.Projection.ofArray indices

private def controls (entry : Entry) : IO Unit := do
  let file ← require (prepareFile declared.partitions {} entry.path)
  unless file.path.declared == entry.path && file.path.filename == "z%41.parquet" do
    throw (IO.userError "literal filename changed")
  let failPath (path : String) : Except Error (Arrow.Events.Termination Error) :=
    (Hive.Manifest.Heterogeneous.read declared {} {} [{entry with path}]).map (·.termination)
  match failPath "region=a/part.parquet" with
  | .ok (.readError (.file 0 "region=a/part.parquet" (.path (.binding _ (.missingKey "rank"))))) => pure ()
  | _ => throw (IO.userError "missing partition key was accepted")
  match failPath "rank=__HIVE_DEFAULT_PARTITION__/part.parquet" with
  | .ok (.readError (.file 0 _ (.requiredNull "rank"))) => pure ()
  | _ => throw (IO.userError "required null partition was accepted")
  match failPath "rank=2147483648/part.parquet" with
  | .ok (.readError (.file 0 _ (.path (.binding _ (.conversion "rank" (.int32 (.int32OutOfRange 2147483648))))))) =>
    pure ()
  | _ => throw (IO.userError "out-of-range Int32 partition was accepted")

  let reserved : Schema := ⟨#[], ⟨#[⟨"code", .int32 false, .reject⟩]⟩⟩
  let collision ← require (Hive.Manifest.Heterogeneous.read reserved {} {} [{entry with path := "code=1/part.parquet"}])
  match collision.termination with
  | .readError (.file 0 _ (.reservedPartition "code")) => pure ()
  | _ => throw (IO.userError "unselected reserved column was accepted")

  let wrongField : PhysicalField := ⟨3, "local_us", .timestamp ⟨⟨.microsecond, some "UTC"⟩, false⟩⟩
  let wrong : Schema := {declared with fields := declared.fields.set! 0 wrongField}
  let mismatch ← require (Hive.Manifest.Heterogeneous.read wrong {} {} [entry])
  match mismatch.termination with
  | .readError (.file 0 _ .physicalSchema) => pure ()
  | _ => throw (IO.userError "inconsistent declared timezone was accepted")

  let unsupported : Schema := ⟨#[], ⟨#[⟨"time", .timestamp ⟨⟨.millisecond, none⟩, true⟩, .asNull⟩]⟩⟩
  match Hive.Manifest.Heterogeneous.read unsupported {} {} [] with
  | .error (.unsupportedPartition "time") => pure ()
  | _ => throw (IO.userError "timestamp partition declaration was accepted")

public def main (args : List String) : IO Unit := do
  let [folder, offset] := args | throw (IO.userError "expected fixture folder and dictionary offset")
  let some offset := offset.toNat? | throw (IO.userError "invalid dictionary offset")
  let directory : System.FilePath := folder
  let paths := (← IO.FS.readFile (directory / "manifest.txt")).splitOn "\n"
  let [first, second, _, _] := paths | throw (IO.userError "expected four manifest occurrences")
  let good ← load (directory / "native") paths
  let bad ← load (directory / "late") paths
  let ⟨_, wide⟩ ← require (readAll declared {} {} good)
  requireEos wide
  compare directory "wide" wide
  let reorder ← select declared.output #[5, 3, 6, 0, 5]
  let reordered ← require (project declared {} {} good reorder)
  requireEos reordered
  compare directory "reordered" reordered
  let empty ← select declared.output #[]
  let zeroWidth ← require (project declared {} {} good empty)
  requireEos zeroWidth
  compare directory "zero_width" zeroWidth
  let virtualOnly ← require (Hive.Manifest.Heterogeneous.read {declared with fields := #[]} {} {} good)
  requireEos virtualOnly
  compare directory "virtual_only" virtualOnly
  let ⟨emptySchema, noFiles⟩ ← require (readAll declared {} {} [])
  requireEos noFiles
  unless emptySchema.width == 7 && noFiles.batches.isEmpty do
    throw (IO.userError "empty manifest did not retain its declared schema")

  let late ← require (Hive.Manifest.Heterogeneous.read declared {} {} bad)
  expectLate late second offset
  compare directory "late" late
  let selected ← select declared.output #[5, 6, 2]
  let projected ← require (project declared {} {} bad selected)
  expectLate projected second offset
  compare directory "late_projected" projected
  let narrow := {declared with fields := declared.fields.extract 0 3 ++ declared.fields.extract 4 5}
  let narrower ← require (Hive.Manifest.Heterogeneous.read narrow {} {} bad)
  requireEos narrower
  compare directory "late_narrow" narrower
  let [entry, _, _, _] := good | throw (IO.userError "unexpected fixture count")
  unless entry.path == first do throw (IO.userError "manifest order lost")
  controls entry
  IO.println "Verified ordered Hive typed Events, projections and original late Parquet prefix"
