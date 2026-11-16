module

public import Silmaril.Wasm.Execution.Core.GrowImpl
public import Silmaril.Wasm.Execution.MemRep.Defs

@[expose] public section

/-! # Core memory instances over a memory representation

`MemInst R` holds its bytes in a representation `R` (`Execution.MemRep`); `MemInst` is
`MemInst ByteArray`. This module gives the memory-instance operations of `Store.lean` over any
`[MemRep R]`:

* `MemInst.pagesR`: `MemInst.pages`, from `MemRep.size`;
* `MemInst.growR?`: `$growmem` (`MemInst.grow?`), appending zero pages with `MemRep.extend`.

At `R = ByteArray` they are the specification functions (`MemInst.pagesR_byteArray`,
`MemInst.growR?_byteArray`); the `MemRep ByteArray` operations reduce to the
`Execution.Memory` ones by `rfl` (`MemRep.load_byteArray`, …).
-/

namespace Silmaril.Wasm.Execution

namespace MemRep

/-! ## The `ByteArray` representation is the specification -/

@[simp] theorem size_byteArray (m : ByteArray) : MemRep.size m = m.size := rfl
@[simp] theorem load_byteArray (m : ByteArray) (a count : Nat) :
    MemRep.load m a count = Memory.load m a count := rfl
@[simp] theorem store_byteArray (m : ByteArray) (a : Nat) {count : Nat} (w : BitVec (8 * count)) :
    MemRep.store m a w = Memory.store m a w := rfl
@[simp] theorem extend_byteArray (m : ByteArray) (n : Nat) :
    MemRep.extend m n = m ++ ⟨Array.replicate n 0⟩ := rfl

end MemRep

namespace Core

variable {R : Type} [MemRep R]

/-- `MemInst.pages` over a representation. -/
def MemInst.pagesR (mi : MemInst R) : Nat := MemRep.size mi.bytes / Memory.pageSize

/-- `$growmem(mi, n)` (`MemInst.grow?`) over a representation, with the executable check of
the optional maximum (`MemInst.growImpl?`). -/
def MemInst.growR? (mi : MemInst R) (n : Nat) : Option (MemInst R) :=
  let i' := MemRep.size mi.bytes / Memory.pageSize + n
  if i' ≤ 2 ^ (mi.type.address.width - 16) ∧ mi.type.limits.max.all (fun j => i' ≤ j.val) then
    some ⟨{ mi.type with limits := { mi.type.limits with min := Fin.ofNat _ i' } },
      MemRep.extend mi.bytes (n * Memory.pageSize)⟩
  else none

@[simp] theorem MemInst.pagesR_byteArray (mi : MemInst) : mi.pagesR = mi.pages := rfl

@[simp] theorem MemInst.growR?_byteArray (mi : MemInst) (n : Nat) : mi.growR? n = mi.grow? n := by
  rw [MemInst.grow?_eq_growImpl?]; rfl

end Core

end Silmaril.Wasm.Execution
