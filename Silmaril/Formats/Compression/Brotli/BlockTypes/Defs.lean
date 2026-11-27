module

public import Silmaril.Formats.Compression.Brotli.Huffman.Description.Defs

/-! The first three controls in the compressed meta-block header (RFC
7932 §§6, 9.2), starting at NBLTYPESL and ending before NPOSTFIX. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.BlockTypes

open Huffman.Description (Table)

inductive Error where
  | bitLimit
  | truncated
  | description (reason : Huffman.Description.Error)
  | invalidCountCode
  deriving DecidableEq, Repr

/-- The shared NBLTYPES and NTREES field from §9.2. A zero width
    yields a count of two
    with no extra bits. -/
inductive CountWire : List Bool → Nat → Prop where
  | one : CountWire [false] 1
  | many {width extra : Nat} : width < 8 → extra < 2 ^ width →
      CountWire ([true] ++ natBits width 3 ++ natBits extra width) (1 + 2 ^ width + extra)

/-- Section 6's block count code table, as (base, extra width). -/
def countCodes : List (Nat × Nat) :=
  [(1, 2), (5, 2), (9, 2), (13, 2), (17, 3), (25, 3), (33, 3), (41, 3),
   (49, 4), (65, 4), (81, 4), (97, 4), (113, 5), (145, 5), (177, 5), (209, 5),
   (241, 6), (305, 6), (369, 7), (497, 8), (753, 9), (1265, 10), (2289, 11),
   (4337, 12), (8433, 13), (16625, 24)]

def countCode (code : Nat) : Option (Nat × Nat) := countCodes[code]?

/-- A block count symbol and its little-endian extra field. The same
    encoding is used by initial counts and payload switches. -/
inductive LengthWire (table : Table) : List Bool → Nat → Prop where
  | fields {symbol code size base width extra : Nat} :
      table.codeFor symbol = some (code, size) → size ≤ 15 →
      countCode symbol = some (base, width) → extra < 2 ^ width →
      LengthWire table (msbBits code size ++ natBits extra width) (base + extra)

inductive Control where
  | single
  | multiple (types : Nat) (typeTable countTable : Table) (initialCount : Nat)

def Control.typeCount : Control → Nat
  | .single => 1
  | .multiple types .. => types

structure Controls where
  literal : Control
  insertCopy : Control
  distance : Control

/-- For a multi-type category the initial type is implicitly zero. Only
    the count symbol and its extra bits occur after the descriptions. -/
inductive ControlWire : List Bool → Control → Prop where
  | single : ControlWire [false] .single
  | multiple {types base width symbol code size extra : Nat}
      {typeTable countTable : Table} {countBits typeBits tableBits : List Bool} :
      2 ≤ types → CountWire countBits types →
      Huffman.Description.Wire (types + 2) typeBits typeTable →
      Huffman.Description.Wire 26 tableBits countTable →
      countTable.codeFor symbol = some (code, size) → size ≤ 15 →
      countCode symbol = some (base, width) → extra < 2 ^ width →
      ControlWire (countBits ++ typeBits ++ tableBits ++ msbBits code size ++ natBits extra width)
        (.multiple types typeTable countTable (base + extra))

def Wire (bits : List Bool) (controls : Controls) : Prop :=
  ∃ literal insertCopy distance,
    bits = literal ++ insertCopy ++ distance ∧ ControlWire literal controls.literal ∧
      ControlWire insertCopy controls.insertCopy ∧ ControlWire distance controls.distance

namespace Internal

structure Cursor where
  reader : LSBReader
  remaining : Nat

def Cursor.advance (cursor : Cursor) (after : LSBReader) : Cursor :=
  ⟨after, cursor.remaining - (after.totalRead - cursor.reader.totalRead)⟩

def take (cursor : Cursor) (width : Nat) : Except Error (Nat × Cursor) :=
  if cursor.remaining < width then .error .bitLimit
  else
    match cursor.reader.readBits width with
    | none => .error .truncated
    | some (value, after) => .ok (value, ⟨after, cursor.remaining - width⟩)

def readCount (cursor : Cursor) : Except Error (Nat × Cursor) := do
  let (lead, next) ← take cursor 1
  if lead = 0 then pure (1, next)
  else
    let (width, next) ← take next 3
    let (extra, after) ← take next width
    pure (1 + 2 ^ width + extra, after)

def readTable (alphabet : Nat) (cursor : Cursor) : Except Error (Table × Cursor) := do
  let (table, after) ←
    (Huffman.Description.read ⟨alphabet, cursor.remaining⟩ alphabet cursor.reader).mapError Error.description
  pure (table, cursor.advance after)

def codeError : Huffman.Description.SymbolError → Error
  | .bitLimit => .bitLimit
  | .truncated => .truncated
  | .invalidCode => .invalidCountCode

def readCode (table : Table) (cursor : Cursor) : Except Error (Nat × Cursor) := do
  let (symbol, after) ← (table.readBounded cursor.remaining cursor.reader).mapError codeError
  pure (symbol, cursor.advance after)

def readInitial (table : Table) (cursor : Cursor) : Except Error (Nat × Cursor) := do
  let (symbol, next) ← readCode table cursor
  let some (base, width) := countCode symbol | throw .invalidCountCode
  let (extra, after) ← take next width
  pure (base + extra, after)

def readControl (cursor : Cursor) : Except Error (Control × Cursor) := do
  let (types, next) ← readCount cursor
  if types = 1 then pure (.single, next)
  else
    let (typeTable, next) ← readTable (types + 2) next
    let (countTable, next) ← readTable 26 next
    let (initial, after) ← readInitial countTable next
    pure (.multiple types typeTable countTable initial, after)

end Internal

/-- Read the §9.2 variable-length positive count used by NBLTYPES and NTREES. -/
def readCount (bitLimit : Nat) (before : LSBReader) : Except Error (Nat × LSBReader) := do
  let (count, after) ← Internal.readCount ⟨before, bitLimit⟩
  pure (count, after.reader)

/-- Read a block run length using the previously decoded count tree. -/
def readLength (table : Table) (bitLimit : Nat) (before : LSBReader) : Except Error (Nat × LSBReader) := do
  let (length, after) ← Internal.readInitial table ⟨before, bitLimit⟩
  pure (length, after.reader)

/-- Read literal, insert-and-copy, then distance controls under one
    budget. No block switching or command execution is performed here. -/
def read (bitLimit : Nat) (before : LSBReader) : Except Error (Controls × LSBReader) := do
  let (literal, next) ← Internal.readControl ⟨before, bitLimit⟩
  let (insertCopy, next) ← Internal.readControl next
  let (distance, after) ← Internal.readControl next
  pure (⟨literal, insertCopy, distance⟩, after.reader)

end Silmaril.Formats.Compression.Brotli.BlockTypes
