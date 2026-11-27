module

import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Defs
meta import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.FlatProjection
open Silmaril.Formats.Parquet.FlatProjection.Composition
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

private def original : List Nat := [3, 0, 1, 2]
private def repeatPositions : List Nat := [2, 1, 2, 3, 0]

private def sourceLimits (input : Bytes) (width rows : Nat) : Limits :=
  { maxFields := width, maxFileRows := rows, column := { maxFileBytes := input.length } }

private def ipcLimits (width : Nat) (counts : List Nat) : Arrow.MixedFlat.Limits :=
  { observation := {
      ipc := { fields := width, batches := counts.length }
      totalRows := counts.sum, totalCells := width * counts.sum } }

private def emit (path : System.FilePath) (input : Bytes) (ordinals counts : List Nat) :
    IO (KBytes × EventObservation) := do
  let ipc := ipcLimits ordinals.length counts
  let .ok wire := convert (sourceLimits input ordinals.length counts.sum) ipc input ordinals
    | throw (IO.userError s!"conversion failed for {path}")
  let some observed := readEvents ipc wire
    | throw (IO.userError s!"native events did not reach exact EOS for {path}")
  unless observed.batches.map Prod.fst == counts do
    throw (IO.userError s!"wrong batch row counts for {path}")
  IO.FS.writeBinFile path wire.toByteArray
  return (wire, observed)

private def checkProjection (directory : System.FilePath) (input : Bytes) (name : String)
    (counts positions : List Nat) (wide : EventObservation) : IO KBytes := do
  let some ordinals := composeOrdinals original positions
    | throw (IO.userError "valid composition refused")
  let (wire, direct) ← emit (directory / (name ++ ".arrows")) input ordinals counts
  unless projectEvents positions wide == some direct do
    throw (IO.userError s!"native positional projection disagrees for {name}")
  return wire

public def main (args : List String) : IO Unit := do
  let [root] := args | throw (IO.userError "expected fixture directory")
  let directory := System.FilePath.mk root
  for (name, counts) in [("wide", [12, 6]), ("empty-middle", [12, 0, 6]), ("schema-only", [])] do
    let input := Bytes.mk (← IO.FS.readBinFile (directory / (name ++ ".parquet")))
    let (_, wide) ← emit (directory / (name ++ "-wide.arrows")) input original counts
    let repeated ← checkProjection directory input (name ++ "-repeat") counts repeatPositions wide
    if name == "empty-middle" then
      let _ ← checkProjection directory input (name ++ "-zero-width") counts [] wide
      unless (projectEvents [4] wide).isNone do
        throw (IO.userError "out-of-range event position accepted")
      let some ordinals := composeOrdinals original repeatPositions
        | throw (IO.userError "repeated source composition failed")
      let source := sourceLimits input ordinals.length counts.sum
      let .ok checked := openFile source input ordinals
        | throw (IO.userError "repeated source did not open")
      let .ok _ := checked.readAll source
        | throw (IO.userError "repeated source was not exhausted")
      let refusedProfile : Arrow.MixedFlat.Limits :=
        { observation := {
            ipc := { fields := original.length, batches := counts.length }
            totalRows := counts.sum, totalCells := ordinals.length * counts.sum } }
      let .error error := convert source refusedProfile input ordinals
        | throw (IO.userError "direct IPC field cap admitted the repeated projection")
      unless error == .writer (.ipc (.limit .fields)) do
        throw (IO.userError s!"wrong direct IPC refusal: {repr error}")
      let readerProfile := ipcLimits ordinals.length counts
      let trailing := repeated ++ (repeated.slice 0 1)
      let truncated := repeated.slice 0 (repeated.len - 1)
      unless (readEvents readerProfile trailing).isNone && (readEvents readerProfile truncated).isNone do
        throw (IO.userError "an incomplete native event trace was accepted")
  IO.println "Four positional event comparisons; direct repeated-field limit, invalid position and two exact-EOS controls."
