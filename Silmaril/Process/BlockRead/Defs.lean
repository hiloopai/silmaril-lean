module

public import Silmaril.Process.Memory
public import Silmaril.Semantics.MemoryRefinement.Defs

/-! # Reading live objects before choosing addresses

A snapshot has block identities and entire byte strings, not machine addresses.
There is no integer-to-pointer operation. Absent blocks, zero-width and
out-of-bounds reads are UB in this deliberately small read-only fragment.
-/

@[expose] public section

namespace Silmaril.Process.BlockRead

open Silmaril.Semantics.MemoryRefinement

structure Request (Block : Type) where
  heap : Block → Option (List Byte)
  block : Block
  offset : Nat
  width : Nat

def Request.read {Block} (req : Request Block) : Option (List Byte) := do
  let bytes ← req.heap req.block
  if 0 < req.width ∧ req.offset + req.width ≤ bytes.length then
    some ((bytes.drop req.offset).take req.width)
  else none

structure FlatRequest where
  memory : Memory
  address : Nat
  width : Nat

def FlatRequest.read (req : FlatRequest) := req.memory.readBytes req.address req.width

def objects (Block : Type) := ofEval (Request.read (Block := Block))
def flat := ofEval FlatRequest.read

/-- Evidence about whole allocations, independent of the pointer or read being checked. -/
structure Realizes {Block : Type} (base : Block → Nat) (heap : Block → Option (List Byte))
    (memory : Memory) : Prop where
  contents : ∀ block bytes, heap block = some bytes → memory.readBytes (base block) bytes.length = some bytes
  disjoint : ∀ left right xs ys, left ≠ right → heap left = some xs → heap right = some ys →
    base left + xs.length ≤ base right ∨ base right + ys.length ≤ base left

def Placed {Block} (base : Block → Nat) (obj : Request Block) (bytes : FlatRequest) : Prop :=
  Realizes base obj.heap bytes.memory ∧ bytes.address = base obj.block + obj.offset ∧ bytes.width = obj.width

end Silmaril.Process.BlockRead
