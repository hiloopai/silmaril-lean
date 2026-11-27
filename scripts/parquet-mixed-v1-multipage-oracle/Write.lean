module

import Silmaril.Formats.Parquet.MixedV1Writer.MultiPage.Defs
meta import Silmaril.Formats.Parquet.MixedV1Writer.MultiPage.Defs

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.MixedV1Writer (Order)
open Silmaril.Formats.Parquet.MixedV1Writer.MultiPage

private def limits : Limits :=
  ⟨⟨⟨8192, {}, ⟨{}, 32, ⟨256, 256, ⟨32, 64⟩, 0⟩⟩,
    ⟨⟨{}, 32, ⟨256, 256, ⟨32, 64⟩, 0⟩⟩, ⟨256, 64⟩⟩, {}⟩, 3, 8⟩, 3, 10⟩

private def rawValue : Bytes := Bytes.ofList [255, 0, 128]

private def long : Bytes := Bytes.ofList (128 :: List.replicate 23 42 ++ [0, 255])

private def group1 : Group :=
  ⟨[.optional [some (-2147483648), none], .optional [some 0, some (-7), some 2147483647]],
    [.optional [none], .optional [some Bytes.empty], .optional [some rawValue, none, some long]]⟩

private def group1Recut : Group :=
  ⟨[.optional [some (-2147483648)], .optional [none, some 0, some (-7), some 2147483647]],
    [.optional [none, some Bytes.empty], .optional [some rawValue], .optional [none, some long]]⟩

private def empty : Group := ⟨[.optional []], [.optional []]⟩

private def group3 : Group :=
  ⟨[.optional [none, some 6, some (-5)]], [.optional [some long], .optional [none, some Bytes.empty]]⟩

private def input : Input := ⟨⟨"count", .optional⟩, ⟨"opaque", .optional⟩, [group1, empty, group3]⟩

private def written (order : Order) (bounded : Limits) (data : Input) : IO Encoded :=
  match emit order bounded data with
  | .ok file => pure file
  | .error cause => throw (IO.userError s!"unexpected writer refusal: {repr cause}")

private def refused (bounded : Limits) (data : Input) (expected : Error) : IO Unit := do
  match emit .intFirst bounded data with
  | .ok _ => throw (IO.userError s!"expected {repr expected}, got a file")
  | .error cause =>
    unless cause == expected do
      throw (IO.userError s!"expected {repr expected}, got {repr cause}")

private def readGroups (file : Encoded) : IO (List (List Int32ByteArrayGroup.Row)) := do
  let policy := limits.file.writer.readback
  let .ok checked := Int32ByteArrayGroup.openFile policy file.bytes input.intField input.byteField
    | throw (IO.userError "readback open failed")
  let .ok rows := (List.range checked.snapshot.groupCount).mapM (checked.readGroup policy)
    | throw (IO.userError "group readback failed")
  return rows

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected one output directory")
  let directory := System.FilePath.mk path
  let first ← written .intFirst limits input
  let recut := { input with groups := [group1Recut, empty, group3] }
  let second ← written .byteFirst limits recut
  let expected := input.groups.map Group.rows
  unless (← readGroups first) == expected && (← readGroups second) == expected do
    throw (IO.userError "independent cuts or order changed the logical groups")
  IO.FS.writeBinFile (directory / "int-first.parquet") first.bytes.data
  IO.FS.writeBinFile (directory / "byte-first-recut.parquet") second.bytes.data

  let exact := { limits with file := { limits.file with writer := { limits.file.writer with
    maxFileBytes := first.bytes.length } } }
  let atCap ← written .intFirst exact input
  unless atCap.bytes == first.bytes do throw (IO.userError "exact byte cap changed the file")
  let short := { exact with file := { exact.file with writer := { exact.file.writer with
    maxFileBytes := first.bytes.length - 1 } } }
  refused short input (.footer .byteLimit)
  refused { limits with file := { limits.file with writer := { limits.file.writer with maxFileBytes := 11 } } }
    input .fileLimit
  refused { limits with file := { limits.file with maxGroups := 2 } } input .groupLimit
  refused limits { input with groups := [] } .groupLimit
  refused { limits with file := { limits.file with maxTotalRows := 7 } } input .rowLimit
  refused { limits with maxPagesPerChunk := 2 } input .chunkPageLimit
  refused { limits with maxPages := 9 } input .pageLimit
  refused limits { input with groups := [⟨[.optional []], []⟩] } .schemaOrCuts
  refused limits { input with groups := [{ group1 with integers := group1.integers ++ [.optional []] }] } .schemaOrCuts
  refused limits { input with groups := [{ group1 with octets := group1.octets.take 2 }] } .schemaOrCuts
  refused limits { input with groups := [{ empty with integers := [.required []] }] } .schemaOrCuts

  let writer := limits.file.writer
  let intPage := writer.intPage
  let intCaps := { intPage with scalar := { intPage.scalar with levels := { intPage.scalar.levels with values := 2 } } }
  refused { limits with file := { limits.file with writer := { writer with intPage := intCaps } } } input
    (.measure 0 .int32 1 .intBudget)
  let bytePage := writer.bytePage
  let byteCaps := { bytePage with plain := { bytePage.plain with valueBytes := 12 } }
  refused { limits with file := { limits.file with writer := { writer with bytePage := byteCaps } } } input
    (.emitPage 0 .byteArray 2 (.bytePage (.plain .valueByteLimit)))
  let bodyCaps := { bytePage with page := { bytePage.page with
    scalar := { bytePage.page.scalar with uncompressedBytes := 16 } } }
  refused { limits with file := { limits.file with writer := { writer with bytePage := bodyCaps } } } input
    (.measure 0 .byteArray 2 .byteBudget)
  let reader := writer.readback
  let column := { reader.column with framing := { reader.column.framing with maxPages := 2 } }
  refused { limits with file := { limits.file with writer := { writer with readback := { reader with column } } } }
    input (.readback (.groupReadback 0 (.byteArray (.column 0 1 "opaque" (.framing .pageLimit)))))

  let single := { input with groups := [⟨[.optional group1.intSlots], [.optional group1.byteSlots]⟩, empty] }
  for order in [Order.intFirst, Order.byteFirst] do
    let modern ← written order limits single
    let originalPlan : MixedV1Writer.Multi.Input :=
      ⟨single.intField, single.byteField, single.groups.map Group.observation⟩
    let .ok original := MixedV1Writer.Multi.emitOrdered order limits.file originalPlan
      | throw (IO.userError "original singleton-page writer failed")
    unless modern.bytes == original.bytes do
      throw (IO.userError "singleton page plans changed predecessor bytes")
  IO.println "Two exact native readbacks, two singleton-byte comparisons, and fifteen typed refusals."
