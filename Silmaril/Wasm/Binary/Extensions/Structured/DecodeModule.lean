module

public import Silmaril.Wasm.Binary.Extensions.Structured.Modules
public import Silmaril.Wasm.Binary.Extensions.SharedMemory.Decode

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.Structured.DecodeModule

open Core Core.Decode

def readCode {Body : Type} (reader : DecodeM Body) : DecodeM (List Wasm.ValType × Body) := do
  let size ← readU 32
  let r₀ ← remaining
  unless size ≤ r₀ do decodeError "code entry past the end"
  let groups ← readVec do
    let n ← readU 32
    let t ← readValType
    pure (n, t)
  let total := groups.foldl (fun s p => s + p.1) 0
  unless total ≤ maxLocals do decodeError s!"{total} locals exceed the limit {maxLocals}"
  let locals := groups.flatMap fun p => List.replicate p.1 p.2
  let body ← reader
  unless r₀ - (← remaining) == size do decodeError "code entry size mismatch"
  pure (locals, body)

structure Sections (Body : Type) where
  types : List Wasm.RecType := []
  imports : List Wasm.Extensions.SharedMemory.Import := []
  funcTypes : List TypeIdx := []
  tables : List Wasm.Table := []
  memories : List Wasm.Extensions.SharedMemory.MemoryType := []
  tags : List Wasm.TagType := []
  globals : List Wasm.Global := []
  exports : List Wasm.Export := []
  start : Option FuncIdx := none
  elems : List Wasm.Elem := []
  dataCount : Option Nat := none
  code : List (List Wasm.ValType × Body) := []
  data : List Wasm.Data := []

/-- The contents of a supported non-custom section. -/
def readSectionBody {Body : Type} (reader : DecodeM Body) (id : Nat) (s : Sections Body) : DecodeM (Sections Body) := do
  match id with
  | 1 => pure { s with types := ← readVec readRecType }
  | 2 => pure { s with imports := ← SharedMemory.Decode.readImports }
  | 3 => pure { s with funcTypes := ← readVec readIdx }
  | 4 => pure { s with tables := ← readVec readTable }
  | 5 => pure { s with memories := ← readVec SharedMemory.Decode.readMemType }
  | 6 => pure { s with globals := ← readVec readGlobal }
  | 7 => pure { s with exports := ← readVec readExport }
  | 8 => pure { s with start := some (← readIdx) }
  | 9 => pure { s with elems := ← readVec readElem }
  | 10 => pure { s with code := ← readVec (readCode reader) }
  | 11 => pure { s with data := ← readVec readData }
  | 12 => pure { s with dataCount := some (← readU 32) }
  | 13 => pure { s with tags := ← readVec readTag }
  | _ => decodeError s!"section {id} outside the fragment"

def readModule {Body : Type} (reader : DecodeM Body) (dataIdxs : Body → List DataIdx) :
    DecodeM (Wasm.Extensions.Structured.FunctionModule Body) := do
  readHeader
  let s ← readModule.go (← get).bytes.size 0 {}
  unless (← remaining) == 0 do decodeError "trailing bytes"
  unless s.funcTypes.length == s.code.length do
    decodeError s!"{s.funcTypes.length} function declarations but {s.code.length} bodies"
  unless s.dataCount.all (· == s.data.length) do decodeError "data count mismatch"
  unless s.dataCount.isSome || (codesDataIdxs dataIdxs s.code).isEmpty do
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
  go (fuel last : Nat) (s : Sections Body) : DecodeM (Sections Body) :=
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
        let s ← readSectionBody reader id s
        unless r₀ - (← remaining) == size do decodeError s!"section {id} size mismatch"
        go fuel (sectionRank id) s

/-- The original-byte decoder with its diagnostic. -/
def decodeModule {Body : Type} (reader : DecodeM Body) (dataIdxs : Body → List DataIdx)
    (b : ByteArray) : Except String (Wasm.Extensions.Structured.FunctionModule Body) :=
  (readModule reader dataIdxs).run' ⟨b, 0⟩

end Silmaril.Wasm.Binary.Extensions.Structured.DecodeModule
