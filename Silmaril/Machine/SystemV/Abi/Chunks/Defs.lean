module

public import Silmaril.Machine.SystemV.Abi.Defs

@[expose] public section
namespace Silmaril.Machine.SystemV.Abi.Chunks
open Silmaril.Machine.SystemV.Abi

/-- The four mutable components of the actual ABI chunk loop. -/
abbrev Cursor := List Chunk × Nat × Nat × Nat

def advance (size : Nat) (registers : List Silmaril.X86.Reg)
    (cursor : Cursor) (item : Class × Nat) : Except String Cursor := do
  let (result, gp, fp, vectorOffset) := cursor
  let (cls, index) := item
  let offset := 8 * index
  let bytes := min 8 (size - offset)
  match cls with
  | .noClass => return cursor
  | .integer =>
      let some register := registers[gp]? | throw "INTEGER register capacity exceeded"
      return (result ++ [⟨offset, bytes, .gp register⟩], gp + 1, fp, 0)
  | .sse => return (result ++ [⟨offset, bytes, .vector fp 0⟩], gp, fp + 1, 8)
  | .sseUp =>
      if fp == 0 then throw "orphan SSEUP class"
      else return (result ++ [⟨offset, bytes, .vector (fp - 1) vectorOffset⟩], gp, fp, vectorOffset + 8)
  | _ => throw "non-register class in ordinary register chunks"

def walk (size : Nat) (registers : List Silmaril.X86.Reg) :
    List (Class × Nat) → Cursor → Except String Cursor
  | [], cursor => .ok cursor
  | item :: rest, cursor => do
      let next ← advance size registers cursor item
      walk size registers rest next

def demand : List (Class × Nat) → Nat
  | [] => 0
  | (cls, _) :: rest => (if cls == .integer then 1 else 0) + demand rest

/-- Total for proof convenience; capacity proofs ensure the fallback is never
used for any actual successful shifted INTEGER assignment. -/
def shiftChunk (gp fp : Nat) (chunk : Chunk) : Chunk :=
  { chunk with location := match chunk.location with
      | .gp register => .gp ((gpArguments[gp + gpArguments.idxOf register]?).getD .rdi)
      | .vector index offset => .vector (fp + index) offset
      | .x87 index => .x87 index }

def shiftCursor (gp fp : Nat) (cursor : Cursor) : Cursor :=
  (cursor.1.map (shiftChunk gp fp), gp + cursor.2.1, fp + cursor.2.2.1, cursor.2.2.2)

end Silmaril.Machine.SystemV.Abi.Chunks
