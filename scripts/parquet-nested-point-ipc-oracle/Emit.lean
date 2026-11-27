module

import Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc.Defs
meta import Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Relational
open Parquet.NestedPoint.Multi.ToIpc
open Arrow.StructInt32 (Field)

private def field : Field := ⟨"座標", ⟨"signed", false⟩, ⟨"広い", true⟩⟩

private def require {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def load (folder : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (folder / (name ++ ".parquet"))⟩

private def emitCase (folder : System.FilePath) (name : String) (expected : List Nat) : IO Unit := do
  let file ← load folder name
  let result := convert {} file
  let ⟨_, trace⟩ ← require result.trace
  unless trace.termination = .eos do throw (IO.userError s!"{name}: no source EOS")
  unless trace.batches.map (·.rowCount) = expected do throw (IO.userError s!"{name}: wrong group counts")
  let wire ← require result.wire
  let native ← require (Arrow.StructInt32.Stream.readFor .int64 {} wire)
  unless native.field = field ∧ native.batches.map (·.rows.length) = expected do
    throw (IO.userError s!"{name}: output schema or batch counts changed")
  IO.FS.writeBinFile (folder / (name ++ ".arrow")) wire.toByteArray

private def expectError (label : String) (cause : Error) (result : Result) : IO Unit :=
  match result.wire with
  | .error actual =>
    unless actual = cause do throw (IO.userError s!"{label}: expected {repr cause}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: a failing source returned IPC")

public def main (args : List String) : IO Unit := do
  let [dir, pageOffset] := args | throw (IO.userError "expected fixture folder and late page offset")
  let some pageOffset := pageOffset.toNat? | throw (IO.userError "invalid page offset")
  let folder : System.FilePath := dir
  emitCase folder "native" [12, 12, 2]
  emitCase folder "schema_only" []
  emitCase folder "assembled_empty" [12, 0, 12, 2]
  let clean := convert {} (← load folder "native")
  let ⟨cleanSchema, cleanTrace⟩ ← require clean.trace
  let damaged ← load folder "edited_late"
  let blocked : Limits := {ipc.ipc.fields := 0, ipc.ipc.batches := 0}
  let failure : SourceError :=
    .groupFailure 1 (.column 1 (.page pageOffset (.plain .truncated)))
  expectError "late original column and page" (.source failure) (convert {} damaged)
  let result := convert blocked damaged
  expectError "source precedes writer caps" (.source failure) result
  let ⟨schema, trace⟩ ← require result.trace
  unless trace.termination = .readError failure do throw (IO.userError "wrong Events terminal result")
  let [original, _, _] := cleanTrace.batches | throw (IO.userError "missing clean groups")
  let [retained] := trace.batches | throw (IO.userError "wrong prefix")
  let retainedColumn : Fin schema.width ←
    if width : schema.width = 1 then pure ⟨0, by omega⟩
    else throw (IO.userError "retained schema width changed")
  let originalColumn : Fin cleanSchema.width ←
    if width : cleanSchema.width = 1 then pure ⟨0, by omega⟩
    else throw (IO.userError "clean schema width changed")
  unless retained.rowCount == 12 && (schema.kind retainedColumn).2 == field do
    throw (IO.userError "completed group's descriptor or row count differed")
  unless decide (retained.values retainedColumn = original.values originalColumn) do
    throw (IO.userError "completed group's nested rows differed")


  expectError "clean source reaches writer admission" (.writer (.ipc (.limit .batches)))
    (convert blocked (← load folder "native"))
  expectError "no TIMESTAMP annotation reinterpretation" (.source (.openFailure (.leafAnnotation 1)))
    (convert blocked (← load folder "annotated_wide"))
  expectError "reject requiredness mismatch" (.source (.openFailure (.profile 0)))
    (convert blocked (← load folder "optional_left"))
  IO.println "Verified three native IPC readbacks, five typed refusals, and one exact late prefix"
