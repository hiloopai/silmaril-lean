module

import Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform.Defs
meta import Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform.Defs

open Silmaril.Formats.Compression.Brotli.StaticDictionary
open Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform

private def appendWord (buffer word : ByteArray) : ByteArray :=
  (buffer.push (UInt8.ofNat word.size)) ++ word

private def checked {α : Type} (result : Except Transform.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error reason => throw (IO.userError (reprStr reason))

public def main (args : List String) : IO Unit := do
  let [edgePath, outPath] := args | throw (IO.userError "expected edge input and output paths")
  let edges ← IO.FS.readBinFile edgePath
  let out ← IO.FS.Handle.mk outPath .write
  let mut serialized := ByteArray.empty
  for row in table.toArray do
    serialized := (serialized ++ ⟨row.leading.toArray⟩).push 0
    serialized := serialized.push row.action.code
    serialized := (serialized ++ ⟨row.trailing.toArray⟩).push 0
  out.write serialized
  for length in [4:25] do
    let count := wordCount length
    let mut buffer := ByteArray.emptyWithCapacity (count * transformCount * (length + 14))
    for index in [0:count] do
      for ordinal in [0:transformCount] do
        let word ← checked (materialize length (ordinal * count + index))
        buffer := appendWord buffer word
    out.write buffer
  let mut offset := 0
  while offset < edges.size do
    let some lengthByte := edges[offset]? | throw (IO.userError "missing edge length")
    let length := lengthByte.toNat
    offset := offset + 1
    if edges.size < offset + length then throw (IO.userError "short edge input")
    let word := edges.extract offset (offset + length)
    offset := offset + length
    let mut buffer := ByteArray.empty
    for ordinal in [0:transformCount] do
      buffer := appendWord buffer (← checked (applyTransform ordinal word))
    out.write buffer
