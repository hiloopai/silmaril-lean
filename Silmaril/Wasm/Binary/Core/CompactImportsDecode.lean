module

public import Silmaril.Wasm.Binary.Core.CompactImports
public import Silmaril.Wasm.Binary.Core.Decode

@[expose] public section

namespace Silmaril.Wasm.Binary.Core.CompactImports.Decode

open Core.Decode

/-- Existing ordinary descriptor kinds only. Grouping introduces no new types. -/
def readExternType : DecodeM Wasm.ExternType := do
  match (← readByte).toNat with
  | 0x00 => pure (.func (← readIdx))
  | 0x01 => pure (.table (← readTableType))
  | 0x02 => pure (.memory (← readMemType))
  | 0x03 =>
    let t ← readValType
    let m ← match (← readByte).toNat with
      | 0x00 => pure Mutability.const
      | 0x01 => pure Mutability.var
      | _ => decodeError "bad global mutability"
    pure (.global ⟨m, t⟩)
  | 0x04 => pure (.tag (← readTag))
  | _ => decodeError "unsupported import descriptor"

def readItem : DecodeM (String × Wasm.ExternType) := do
  let n ← readName
  pure (n, ← readExternType)

def readTail (m n : String) : DecodeM (List Wasm.Import) := do
  if n == "" then
    match (← peekByte).map UInt8.toNat with
    | some 0x7f =>
      let _ ← readByte
      pure (expandItems m (← readVec readItem))
    | some 0x7e =>
      let _ ← readByte
      let t ← readExternType
      pure (expandNames m t (← readVec readName))
    | _ => pure [⟨m, n, ← readExternType⟩]
  else pure [⟨m, n, ← readExternType⟩]

def readGroup : DecodeM (List Wasm.Import) := do
  let m ← readName
  let n ← readName
  readTail m n

/-- The outer vector counts groups. Flattening preserves every input position. -/
def readImports : DecodeM (List Wasm.Import) := do
  pure (← readVec readGroup).flatten

def readSectionBody (id : Nat) (s : Sections) : DecodeM Sections := do
  match id with
  | 1 => pure { s with types := ← readVec readRecType }
  | 2 => pure { s with imports := ← readImports }
  | 3 => pure { s with funcTypes := ← readVec readIdx }
  | 4 => pure { s with tables := ← readVec readTable }
  | 5 => pure { s with memories := ← readVec readMemType }
  | 6 => pure { s with globals := ← readVec readGlobal }
  | 7 => pure { s with exports := ← readVec readExport }
  | 8 => pure { s with start := some (← readIdx) }
  | 9 => pure { s with elems := ← readVec readElem }
  | 10 => pure { s with code := ← readVec readCode }
  | 11 => pure { s with data := ← readVec readData }
  | 12 => pure { s with dataCount := some (← readU 32) }
  | 13 => pure { s with tags := ← readVec readTag }
  | _ => decodeError s!"section {id} outside the fragment"

def readModule : DecodeM Wasm.Module := do
  readHeader
  let s ← readModule.go (← get).bytes.size 0 {}
  unless (← remaining) == 0 do decodeError "trailing bytes"
  unless s.funcTypes.length == s.code.length do
    decodeError s!"{s.funcTypes.length} function declarations but {s.code.length} bodies"
  unless s.dataCount.all (· == s.data.length) do decodeError "data count mismatch"
  unless s.dataCount.isSome || (codesDataIdxs s.code).isEmpty do
    decodeError "data index in code without a data count section"
  pure {
    types := s.types
    imports := s.imports
    tags := s.tags
    globals := s.globals
    tables := s.tables
    memories := s.memories
    elems := s.elems
    funcs := zipFuncs s.funcTypes s.code
    data := s.data
    start := s.start
    exports := s.exports }

where
  /-- At most `fuel` sections after the section of rank `last`; structural on `fuel`. -/
  go (fuel last : Nat) (s : Sections) : DecodeM Sections :=
    match fuel with
    | 0 => pure s
    | fuel + 1 => do
      if (← remaining) == 0 then return s
      let id := (← readByte).toNat
      let size ← readU 32
      let r₀ ← remaining
      unless size ≤ r₀ do decodeError s!"section {id} past the end"
      if id == 0 then
        readCustom size
        go fuel last s
      else
        unless last < sectionRank id do decodeError s!"section {id} out of order or repeated"
        let s ← readSectionBody id s
        unless r₀ - (← remaining) == size do decodeError s!"section {id} size mismatch"
        go fuel (sectionRank id) s

/-- The decoder with its error message. -/
def decodeModule (b : ByteArray) : Except String Wasm.Module :=
  readModule.run' ⟨b, 0⟩


end Silmaril.Wasm.Binary.Core.CompactImports.Decode
