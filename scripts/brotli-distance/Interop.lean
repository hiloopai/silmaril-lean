module

import Lean
import Silmaril.Formats.Compression.Brotli.Distance.Defs
meta import Silmaril.Formats.Compression.Brotli.Distance.Defs

open Lean Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli

private def requireIO {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .error error => throw (IO.userError (reprStr error))
  | .ok value => pure value

private def seek (reader : LSBReader) (position : Nat) : IO LSBReader := do
  unless reader.totalRead ≤ position do throw (IO.userError "trace cursor moved backwards")
  let some (_, after) := reader.readBits (position - reader.totalRead)
    | throw (IO.userError "trace cursor exceeds original bytes")
  pure after

private def sameCursor (a b : LSBReader) : Bool :=
  a.totalRead == b.totalRead && a.count == b.count && a.buffer == b.buffer && a.input == b.input

private def windowBits (first : UInt8) : Nat :=
  let byte := first.toNat
  let short := byte / 2 % 8
  let long := byte / 16 % 8
  if byte % 2 = 0 then 16 else if short ≠ 0 then 17 + short else if long = 0 then 17 else 8 + long

private def showRing (ring : Distance.Ring) : List Nat :=
  [ring.latest, ring.second, ring.third, ring.fourth]

public def main (args : List String) : IO UInt32 := do
  let [file, requests, startArg, payloadArg] := args | return 2
  let (some start, some payload) := (startArg.toNat?, payloadArg.toNat?) | return 2
  let raw ← IO.FS.readBinFile file
  let some firstByte := raw[0]? | return 2
  let reader := LSBReader.ofByteArray raw
  let (header, first) ← requireIO (CompressedHeader.read ⟨17408, 768, payload - start⟩ (← seek reader start))
  unless first.totalRead == payload && header.initial.controls.distance.typeCount == 1 do
    throw (IO.userError "native header boundary or distance type count differs")
  let mut cursor := first
  let mut ring := Distance.Ring.start
  for line in (← IO.FS.readFile requests).splitOn "\n" do
    if line.isEmpty then continue
    let some [commandType, commandStart, distanceStart, stop, produced] :=
      (line.splitOn " ").mapM String.toNat? | return 2
    let some commandTree := header.insertCopyTrees[commandType]? | return 2
    let (command, afterCommand) ← requireIO (Command.read commandTree 63 (← seek cursor commandStart))
    let before ← seek afterCommand distanceStart
    let expected ← seek before stop
    let cap := stop - distanceStart
    let bounds : Distance.Bounds := ⟨windowBits firstByte, produced⟩
    let decode := fun limit => Distance.read header command bounds ring limit before
    if cap > 0 then
      match decode (cap - 1) with
      | .error (.symbol .bitLimit) | .error .extraBitLimit => pure ()
      | _ => throw (IO.userError s!"one-bit-short distance cap at {distanceStart}")
    let (result, after) ← requireIO (decode cap)
    unless sameCursor after expected do throw (IO.userError s!"distance suffix at {distanceStart}")
    let selection ← match command.distance with
      | .implicitZero => pure []
      | .explicit =>
        let some tree := Distance.treeIndex? header.distanceMap command.copyLength
          | throw (IO.userError "missing explicit context tree")
        pure [Distance.contextId command.copyLength, tree]
    let target := match result.target with
      | .backReference distance => [distance]
      | .staticDictionary distance length wordId => [distance, length, wordId]
    IO.println (toJson [[command.symbol.val, command.copyLength, bounds.maxBackward,
      result.code, result.extra, distanceStart, after.totalRead],
      selection, target, showRing ring, showRing result.ring]).compress
    cursor := after
    ring := result.ring
  return 0
