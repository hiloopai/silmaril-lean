module

import Silmaril.Formats.Parquet.ListFile.Writer.Defs
meta import Silmaril.Formats.Parquet.ListFile.Writer.Defs

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Writer

private def first : List ListPage.Row :=
  [none, some [], some [none], some [some (-7), none, some 0], some [some 9, none]]

private def second : List ListPage.Row :=
  [some [some (-2147483648), none, some 2147483647], none, some []]

private def write (path : String) (groups : List (List ListPage.Row)) : IO Unit := do
  match emit {} ⟨"résultats", "element", groups⟩ with
  | .ok file => IO.FS.writeBinFile path file.bytes.data
  | .error cause => throw (IO.userError (reprStr cause))

public def main (args : List String) : IO Unit := do
  let [mixed, schemaOnly, emptyGroup] := args
    | throw (IO.userError "usage: Emit.lean MIXED SCHEMA_ONLY EMPTY_GROUP")
  write mixed [first, [], second]
  write schemaOnly []
  write emptyGroup [[]]
