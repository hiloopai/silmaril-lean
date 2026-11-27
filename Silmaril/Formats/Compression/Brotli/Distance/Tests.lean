module

import Silmaril.Formats.Compression.Brotli.Distance.Thms
meta import Silmaril.Formats.Compression.Brotli.Distance.Defs

namespace Silmaril.Formats.Compression.Brotli.Distance

open Silmaril.Formats.Compression
open Huffman.Description (Table)
open ContextMap.Decode (Map)

private def cursor (bits : List Bool) : LSBReader :=
  let width := bits.length % 8
  let lead := LSBWriter.empty.writeBits (bits.take width)
  let bytes := LSBWriter.empty.writeBits (bits.drop width)
  ⟨lead.buffer, lead.count, bytes.bytes.data.toList, 17⟩

private def header (fields : ContextHeader.Fields) (map : Map) (trees : List Table) :
    CompressedHeader.Header :=
  ⟨⟨⟨.single, .single, .single⟩, fields⟩, .implicit 64, map, [], [], trees⟩

private def standard : ContextHeader.Fields := ⟨0, 0, [.lsb6]⟩
private def direct : ContextHeader.Fields := ⟨0, 15, [.lsb6]⟩
private def maxPostfix : ContextHeader.Fields := ⟨3, 15, [.lsb6]⟩

private def chosen (fields : ContextHeader.Fields) (code : Nat)
    (fits : code < fields.distanceAlphabet := by decide) : CompressedHeader.Header :=
  header fields (.implicit 4) [.singleton fields.distanceAlphabet code fits]

private def copy4 : Command.Value := Command.value 130 0 0
private def implicit4 : Command.Value := Command.value 2 0 0

private def observed (result : Except Error (Result × LSBReader)) :
    Option (Result × Nat × Option Bool) := do
  let (resolved, after) ← result.toOption
  pure (resolved, after.totalRead, after.readBit |>.map Prod.fst)

private def errorOf (result : Except Error (Result × LSBReader)) : Option Error :=
  match result with
  | .error reason => some reason
  | .ok _ => none

#guard Ring.start = ⟨4, 11, 15, 16⟩
#guard [2, 3, 4, 5, 4096].map contextId = [0, 1, 2, 3, 3]
#guard (List.range 16).map (fun code => interpret standard Ring.start code 0) =
  [4, 11, 15, 16, 3, 5, 2, 6, 1, 7, 10, 12, 9, 13, 8, 14]
#guard interpret maxPostfix Ring.start 151 1 = 152
#guard extraWidth maxPostfix 519 = 24
#guard interpret maxPostfix Ring.start 519 16777215 = 536871000

#guard observed (read (chosen standard 16) implicit4 ⟨18, 4⟩ Ring.start 0 (cursor [true])) =
  some (⟨0, 0, .backReference 4, Ring.start⟩, 17, some true)
#guard observed (read (chosen standard 16) implicit4 ⟨18, 3⟩ Ring.start 0 (cursor [])) =
  some (⟨0, 0, .staticDictionary 4 4 0, Ring.start⟩, 17, none)
#guard observed (read (chosen standard 0) copy4 ⟨18, 100⟩ Ring.start 0 (cursor [false])) =
  some (⟨0, 0, .backReference 4, Ring.start⟩, 17, some false)
#guard observed (read (chosen direct 20) copy4 ⟨18, 5⟩ Ring.start 0 (cursor [])) =
  some (⟨20, 0, .backReference 5, ⟨5, 4, 11, 15⟩⟩, 17, none)

private def mapped : CompressedHeader.Header :=
  header standard (.coded 2 [0, 0, 1, 0]) [.singleton 64 0 (by decide), .singleton 64 1 (by decide)]

#guard observed (read mapped copy4 ⟨18, 100⟩ Ring.start 0 (cursor [true])) =
  some (⟨1, 0, .backReference 11, ⟨11, 4, 11, 15⟩⟩, 17, some true)
#guard observed (read (chosen standard 31) copy4 ⟨10, 4000⟩ Ring.start 8
    (cursor (natBits 243 8 ++ [true]))) =
  some (⟨31, 243, .backReference 1008, ⟨1008, 4, 11, 15⟩⟩, 25, some true)
#guard observed (read (chosen standard 31) copy4 ⟨10, 4000⟩ Ring.start 8
    (cursor (natBits 244 8 ++ [false]))) =
  some (⟨31, 244, .staticDictionary 1009 4 0, Ring.start⟩, 25, some false)

#guard errorOf (read (chosen standard 4) copy4 ⟨18, 100⟩ ⟨1, 2, 3, 4⟩ 0 (cursor [])) = some .nonpositive
#guard errorOf (read (chosen standard 8) copy4 ⟨18, 100⟩ ⟨1, 2, 3, 4⟩ 0 (cursor [])) = some .nonpositive
#guard errorOf (read (chosen standard 16) copy4 ⟨18, 100⟩ Ring.start 0 (cursor [false])) = some .extraBitLimit
#guard errorOf (read (chosen standard 16) copy4 ⟨18, 100⟩ Ring.start 1 (cursor [])) = some .truncatedExtra
#guard errorOf (read (chosen standard 16) (Command.value 128 0 0) ⟨18, 0⟩ Ring.start 1
    (cursor [false])) = some .dictionaryLength
#guard errorOf (read (chosen maxPostfix 519) copy4 ⟨18, 0⟩ Ring.start 24
    (cursor (natBits 16777215 24))) = some .dictionaryWord
#guard errorOf (read mapped copy4 ⟨25, 1000⟩ Ring.start 0 (cursor [])) = some .window

#guard errorOf (read (header standard (.implicit 4) [.singleton 79 0 (by decide)])
    copy4 ⟨18, 100⟩ Ring.start 0 (cursor [])) = some .alphabet
#guard (
  let initial := mapped.initial
  let block : BlockTypes.Control := .multiple 2 (.singleton 4 0 (by decide)) (.singleton 26 0 (by decide)) 1
  let controls := { initial.controls with distance := block }
  let multi := { mapped with initial := { initial with controls := controls } }
  errorOf (read multi copy4 ⟨18, 100⟩ Ring.start 0 (cursor []))) = some .distanceBlockTypes

end Silmaril.Formats.Compression.Brotli.Distance
