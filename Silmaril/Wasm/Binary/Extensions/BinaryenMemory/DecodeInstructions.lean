module

public import Silmaril.Wasm.Binary.Extensions.BinaryenMemory.Instructions
public import Silmaril.Wasm.Binary.Extensions.AtomicMemory.DecodeInstructions

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.BinaryenMemory.Decode

open Core Core.Decode Wasm.Extensions.BinaryenMemory

/-- Retry the second grammar at the original cursor, never after a consumed prefix. -/
def alternative {α : Type} (p q : DecodeM α) : DecodeM α := fun c =>
  match p.run c with
  | .ok result => .ok result
  | .error _ => q.run c

def readArrayAccess (op : Nat) : DecodeM Wasm.Extensions.BinaryenMemory.Leaf := do
  if h : 0x28 ≤ op ∧ op < 0x3f then
    let flags ← readU 32
    if hf : 32 ≤ flags ∧ flags < 48 then
      let offset ← readU 32
      if ho : offset < 2 ^ 32 then
        let type ← readIdx
        pure (.arrayAccess ⟨⟨op - 0x28, by omega⟩⟩ type
          ⟨⟨flags - 32, by omega⟩, ⟨offset, by omega⟩⟩)
      else decodeError "array-backed offset out of range"
    else decodeError "not an array-backed memory argument"
  else decodeError "not a scalar array-backed access opcode"

def readVectorArrayAccess : DecodeM Wasm.Extensions.BinaryenMemory.Leaf := do
  let subop ← readU 32
  if hs : subop = 0 ∨ subop = 11 then
    let flags ← readU 32
    if hf : 32 ≤ flags ∧ flags < 48 then
      let offset ← readU 32
      if ho : offset < 2 ^ 32 then
        let type ← readIdx
        pure (.vectorArrayAccess (subop == 11) type
          ⟨⟨flags - 32, by omega⟩, ⟨offset, by omega⟩⟩)
      else decodeError "array-backed vector offset out of range"
    else decodeError "not an array-backed vector memory argument"
  else decodeError "not a full-width array-backed vector access"

def readOrder (op : Wasm.Extensions.AtomicMemory.Access) : DecodeM MemoryOrder := do
  let byte ← readByte
  match (if isRMW op then MemoryOrder.ofRMWCode? byte else MemoryOrder.ofCode? byte) with
  | some order => pure order
  | none => decodeError "unknown or mismatched atomic memory order"

def readOrderedMemarg (op : Wasm.Extensions.AtomicMemory.Access) : DecodeM (MemIdx × MemArg × MemoryOrder) := do
  let flags ← readU 32
  if hf : 16 ≤ flags ∧ flags < 32 then
    let order ← readOrder op
    let offset ← readU 64
    if ho : offset < 2 ^ 64 then
      pure (⟨0⟩, ⟨⟨flags - 16, by omega⟩, ⟨offset, ho⟩⟩, order)
    else decodeError "ordered atomic offset out of range"
  else if hf : 80 ≤ flags ∧ flags < 96 then
    let memory ← readIdx
    let order ← readOrder op
    let offset ← readU 64
    if ho : offset < 2 ^ 64 then
      pure (memory, ⟨⟨flags - 80, by omega⟩, ⟨offset, ho⟩⟩, order)
    else decodeError "ordered atomic offset out of range"
  else decodeError "not an explicitly ordered atomic memory argument"

def readOrderedAtomic : DecodeM Wasm.Extensions.BinaryenMemory.Leaf := do
  let subop ← readU 32
  if subop == 3 then
    let byte ← readByte
    match MemoryOrder.ofCode? byte with
    | some order => pure (.orderedFence order)
    | none => decodeError "unknown atomic fence memory order"
  else
    match Wasm.Extensions.AtomicMemory.Access.ofOpcode? subop with
    | none => decodeError "not a supported ordered atomic access"
    | some op =>
      if orderable op then
        let (memory, arg, order) ← readOrderedMemarg op
        pure (.orderedAccess op memory arg order)
      else decodeError "wait/notify do not retain an explicit order in this profile"

def readLeaf (op : Nat) : DecodeM Wasm.Extensions.BinaryenMemory.Leaf :=
  let old := (AtomicMemory.Decode.readLeaf op).map Wasm.Extensions.BinaryenMemory.Leaf.base
  if op == 0xfe then alternative readOrderedAtomic old
  else if op == 0xfd then alternative readVectorArrayAccess old
  else alternative (readArrayAccess op) old

def readExpr : DecodeM Wasm.Extensions.BinaryenMemory.Expr := Structured.Decode.readExpr readLeaf

end Silmaril.Wasm.Binary.Extensions.BinaryenMemory.Decode
