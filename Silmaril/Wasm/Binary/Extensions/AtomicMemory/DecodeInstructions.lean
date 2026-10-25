module

public import Silmaril.Wasm.Binary.Extensions.AtomicMemory.Instructions
public import Silmaril.Wasm.Binary.Extensions.Structured.Decode

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.AtomicMemory.Decode

open Core Core.Decode
open Wasm.Extensions.AtomicMemory

/-- The atomic prefix was consumed by the structured leaf reader. -/
def readAtomic : DecodeM AtomicInstr := do
  match ← readU 32 with
  | 3 =>
    unless (← readByte) == 0 do decodeError "unsupported atomic fence flags"
    pure .fence
  | 4 => pure .pause
  | n =>
    match Access.ofOpcode? n with
    | none => decodeError s!"atomic opcode {n} outside the supported memory table"
    | some op => do
      let (m, arg) ← readMemArg
      pure (.access op m arg)

def readLeaf (op : Nat) : DecodeM Wasm.Extensions.AtomicMemory.Leaf := do
  if op ∈ [0x02, 0x03, 0x04, 0x1f] then decodeError "structured opcode used as leaf"
  else if op == 0xfe then pure (.atomic (← readAtomic))
  else pure (.core (← Core.Decode.readPlain op))

def readExpr := Structured.Decode.readExpr readLeaf

end Silmaril.Wasm.Binary.Extensions.AtomicMemory.Decode
