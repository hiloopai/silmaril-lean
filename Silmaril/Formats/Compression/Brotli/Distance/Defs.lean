module

public import Silmaril.Formats.Compression.Brotli.Defs
public import Silmaril.Formats.Compression.Brotli.Command.Defs

/-! RFC 7932 distance interpretation after a command's literals, with
one distance block type and the standard window. Static dictionary
addresses are handed off as a separate result form. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Distance

open ContextHeader (Fields)
open ContextMap.Decode (Map)
open Huffman.Description (Table)

structure Ring where
  latest : Nat
  second : Nat
  third : Nat
  fourth : Nat
  deriving DecidableEq, Repr

def Ring.start : Ring := ⟨4, 11, 15, 16⟩

def Ring.push (ring : Ring) (distance : Nat) : Ring :=
  ⟨distance, ring.latest, ring.second, ring.third⟩

def Ring.get (ring : Ring) (age : Fin 4) : Nat :=
  match age.val with
  | 0 => ring.latest
  | 1 => ring.second
  | 2 => ring.third
  | _ => ring.fourth

def Ring.Positive (ring : Ring) : Prop :=
  0 < ring.latest ∧ 0 < ring.second ∧ 0 < ring.third ∧ 0 < ring.fourth

structure Bounds where
  /-- Standard stream window field as checked by framing. -/
  windowBits : Nat
  /-- Total stream output through the command's literals. -/
  produced : Nat
  deriving Repr

def Bounds.Valid (bounds : Bounds) : Prop :=
  10 ≤ bounds.windowBits ∧ bounds.windowBits ≤ 24

def Bounds.maxBackward (bounds : Bounds) : Nat :=
  min (windowSize bounds.windowBits) bounds.produced

def contextId (copyLength : Nat) : Nat := min (copyLength - 2) 3

def treeIndex? (map : Map) (copyLength : Nat) : Option Nat :=
  let index := contextId copyLength
  match map with
  | .implicit entries => if index < entries then some 0 else none
  | .coded _ values => values[index]?

/-- (Recent-distance age, signed delta), in RFC §4 symbol order. -/
def shortCodes : Vector (Fin 4 × Int) 16 :=
  #v[(0, 0), (1, 0), (2, 0), (3, 0), (0, -1), (0, 1), (0, -2), (0, 2),
    (0, -3), (0, 3), (1, -1), (1, 1), (1, -2), (1, 2), (1, -3), (1, 3)]

def scale (fields : Fields) : Nat := 2 ^ fields.postfixBits.val

def extraWidth (fields : Fields) (code : Nat) : Nat :=
  if code < 16 + fields.direct then 0
  else 1 + (code - 16 - fields.direct) / (2 * scale fields)

/-- RFC §4 distance formula. Signed arithmetic retains invalid short
    code results until the nonpositive-distance check. -/
def interpret (fields : Fields) (ring : Ring) (code extra : Nat) : Int :=
  if short : code < 16 then
    let (age, delta) := shortCodes[code]
    Int.ofNat (ring.get age) + delta
  else if code < 16 + fields.direct then Int.ofNat (code - 15)
  else
    let adjusted := code - 16 - fields.direct
    let high := adjusted / scale fields
    let low := adjusted % scale fields
    let offset := (2 + high % 2) * 2 ^ extraWidth fields code - 4
    Int.ofNat ((offset + extra) * scale fields + low + fields.direct + 1)

/-- RFC Appendix A's NDBITS array. Only lengths 4 through 24 use it. -/
def dictionaryDepths : Vector Nat 25 :=
  #v[0, 0, 0, 0, 10, 10, 11, 11, 10, 10, 10, 10, 10, 9, 9, 8, 7, 7, 8, 7, 7, 6, 6, 5, 5]

def dictionaryWordCount (length : Nat) : Nat :=
  if fits : length < 25 then 2 ^ dictionaryDepths[length] else 0

inductive Target where
  | backReference (distance : Nat)
  | staticDictionary (distance wordLength wordId : Nat)
  deriving DecidableEq, Repr

def Target.distance : Target → Nat
  | .backReference distance | .staticDictionary distance .. => distance

structure Result where
  code : Nat
  extra : Nat
  target : Target
  ring : Ring
  deriving DecidableEq, Repr

inductive Error where
  | distanceBlockTypes
  | window
  | copyLength
  | contextEntry
  | treeIndex
  | alphabet
  | symbol (reason : Huffman.Description.SymbolError)
  | symbolRange
  | extraBitLimit
  | truncatedExtra
  | nonpositive
  | dictionaryLength
  | dictionaryWord
  deriving DecidableEq, Repr

def nextRing (ring : Ring) (code distance : Nat) : Ring :=
  if code = 0 then ring else ring.push distance

/-- Classification and the exact recent-distance rule. Dictionary
    word IDs already fit the 121 transforms for the given word length. -/
inductive Resolved (bounds : Bounds) (ring : Ring) (copyLength code : Nat) :
    Nat → Target → Ring → Prop where
  | back {distance : Nat} :
      0 < distance → distance ≤ bounds.maxBackward →
      Resolved bounds ring copyLength code distance (.backReference distance) (nextRing ring code distance)
  | dictionary {distance : Nat} :
      bounds.maxBackward < distance → 4 ≤ copyLength → copyLength ≤ 24 →
      distance - (bounds.maxBackward + 1) < 121 * dictionaryWordCount copyLength →
      Resolved bounds ring copyLength code distance
        (.staticDictionary distance copyLength (distance - (bounds.maxBackward + 1))) ring

inductive Wire (header : CompressedHeader.Header) (command : Command.Value) (bounds : Bounds)
    (ring : Ring) : List Bool → Result → Prop where
  | implicit {target : Target} {after : Ring} :
      command.distance = .implicitZero →
      Resolved bounds ring command.copyLength 0 ring.latest target after →
      Wire header command bounds ring [] ⟨0, 0, target, after⟩
  | explicit {tree code prefixCode prefixWidth extra : Nat} {table : Table} {target : Target} {after : Ring} :
      command.distance = .explicit →
      treeIndex? header.distanceMap command.copyLength = some tree →
      header.distanceTrees[tree]? = some table →
      table.alphabetSize = header.initial.fields.distanceAlphabet →
      table.codeFor code = some (prefixCode, prefixWidth) →
      prefixWidth ≤ 15 →
      code < header.initial.fields.distanceAlphabet →
      extra < 2 ^ extraWidth header.initial.fields code →
      Resolved bounds ring command.copyLength code (interpret header.initial.fields ring code extra).toNat
        target after →
      Wire header command bounds ring
        (msbBits prefixCode prefixWidth ++ natBits extra (extraWidth header.initial.fields code))
        ⟨code, extra, target, after⟩

namespace Internal

def route (bounds : Bounds) (ring : Ring) (copyLength code extra distance : Nat) :
    Except Error Result :=
  if distance = 0 then .error .nonpositive
  else if distance ≤ bounds.maxBackward then
    .ok ⟨code, extra, .backReference distance, nextRing ring code distance⟩
  else if copyLength < 4 ∨ 24 < copyLength then .error .dictionaryLength
  else
    let wordId := distance - (bounds.maxBackward + 1)
    if 121 * dictionaryWordCount copyLength ≤ wordId then .error .dictionaryWord
    else .ok ⟨code, extra, .staticDictionary distance copyLength wordId, ring⟩

def take (limit width : Nat) (before : LSBReader) : Except Error (Nat × LSBReader) :=
  if limit < width then .error .extraBitLimit
  else
    match before.readBits width with
    | none => .error .truncatedExtra
    | some result => .ok result

def readExplicit (header : CompressedHeader.Header) (copyLength : Nat) (bounds : Bounds)
    (ring : Ring) (bitLimit : Nat) (before : LSBReader) : Except Error (Result × LSBReader) :=
  match treeIndex? header.distanceMap copyLength with
  | none => .error .contextEntry
  | some tree =>
    match header.distanceTrees[tree]? with
    | none => .error .treeIndex
    | some table =>
      let fields := header.initial.fields
      if table.alphabetSize ≠ fields.distanceAlphabet then .error .alphabet
      else do
        let (code, cursor) ← (table.readBounded bitLimit before).mapError Error.symbol
        if fields.distanceAlphabet ≤ code then .error .symbolRange
        else
          let remaining := bitLimit - (cursor.totalRead - before.totalRead)
          let (extra, after) ← take remaining (extraWidth fields code) cursor
          let result ← route bounds ring copyLength code extra (interpret fields ring code extra).toNat
          pure (result, after)

end Internal

/-- Resolve a pending copy after an insertion. A literal-only ending
    has no pending copy and does not call this reader. -/
def read (header : CompressedHeader.Header) (command : Command.Value) (bounds : Bounds)
    (ring : Ring) (bitLimit : Nat) (before : LSBReader) : Except Error (Result × LSBReader) :=
  match header.initial.controls.distance with
  | .multiple .. => .error .distanceBlockTypes
  | .single =>
    if bounds.windowBits < 10 ∨ 24 < bounds.windowBits then .error .window
    else if command.copyLength < 2 then .error .copyLength
    else match command.distance with
      | .implicitZero => do
        let result ← Internal.route bounds ring command.copyLength 0 0 ring.latest
        pure (result, before)
      | .explicit => Internal.readExplicit header command.copyLength bounds ring bitLimit before

end Silmaril.Formats.Compression.Brotli.Distance
