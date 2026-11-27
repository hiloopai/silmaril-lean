module

import Lean
import Silmaril.Formats.Compression.Brotli.StaticDictionary.Defs
meta import Silmaril.Formats.Compression.Brotli.StaticDictionary.Defs

open Lean Silmaril.Formats.Compression.Brotli.StaticDictionary

private def errorName : Error → String
  | .wordLength => "wordLength"
  | .wordId => "wordId"
  | .wordIndex => "wordIndex"

private def query (line : String) : IO Json := do
  let [operation, length, ordinal] := (line.splitOn " ") |
    throw (IO.userError "expected operation, length and ordinal")
  let some length := length.toNat? | throw (IO.userError "invalid length")
  let some ordinal := ordinal.toNat? | throw (IO.userError "invalid ordinal")
  match operation with
  | "split" =>
    return match splitAddress length ordinal with
      | .ok address => toJson [address.length, address.index, address.transform]
      | .error error => toJson (errorName error)
  | "lookup" =>
    return match lookup length ordinal with
      | .ok word => toJson (word.toList.map UInt8.toNat)
      | .error error => toJson (errorName error)
  | _ => throw (IO.userError "invalid operation")

public def main (args : List String) : IO UInt32 := do
  let [embedded, words, queries] := args | return 2
  IO.FS.writeBinFile embedded canonicalBytes
  let mut lookedUp := ByteArray.emptyWithCapacity canonicalBytes.size
  for length in [4:25] do
    for index in [:wordCount length] do
      let .ok word := lookup length index | throw (IO.userError "valid dictionary index rejected")
      lookedUp := lookedUp ++ word
  IO.FS.writeBinFile words lookedUp
  let lines := (← IO.FS.readFile queries).splitOn "\n"
  let answers ← (lines.filter (· != "")).mapM query
  IO.println (Json.mkObj [
    ("offsets", toJson ((List.range 26).map bucketOffset)),
    ("counts", toJson ((List.range 26).map wordCount)),
    ("queries", toJson answers)]).compress
  return 0
