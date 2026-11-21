module

public import Silmaril.Wasm.Execution.Memory
public import Silmaril.Prelude.Bytes.Write.Thms
public import Silmaril.Prelude.Bytes.Thms

/-! # Memory representations behind laws

Core's linear memory is specified as a `ByteArray` (`Silmaril.Wasm.Execution.Memory`). To run
Core on another representation without restating Core, a representation `R` provides the
memory operations Core uses, and `LawfulMemRep R` relates each one to the `ByteArray`
specification through `toBytes : R → ByteArray`:

| operation | law (`LawfulMemRep`) |
|---|---|
| `size m` | `= (toBytes m).size` |
| `load m a count` | `= Memory.load (toBytes m) a count` |
| `store m a w` | `.map toBytes = Memory.store (toBytes m) a w` |
| `readBytes m a count` | `= Memory.readBytes (toBytes m) a count` |
| `writeBytes m a bs` | `.map toBytes = Memory.writeBytes (toBytes m) a bs` |
| `grow? m max d` | `.map toBytes = Memory.grow? (toBytes m) max d` |
| `zeros n` | `toBytes (zeros n)` is `n` zero bytes |

Instances:

* `ByteArray`: the specification itself (`toBytes = id`; every law is `rfl`).
* `KMem`: a well-formed `Silmaril.KBytes` tree (`Prelude.Bytes`). Loads are `readLE`; stores
  and bulk writes are the path-copying `KBytes.write`, which rewrites only the leaves it
  touches; growth appends a canonical tree of zero leaves. These are the `KBytes`
  representation and writes of `Prelude.Bytes` and `Prelude.Bytes.Write`. The KernelEval
  memory benchmarks (#133, `KPath`) measured them in the kernel against packed, page-tree and
  `ByteArray` memories. The laws are proved from `KBytes.readLE_eq`, `KBytes.toList_write`,
  `KBytes.unpack_leVal` and two digit lemmas relating `Memory.decodeLE`/`Memory.encodeLE` to
  `KBytes.leVal`/`KBytes.unpack` (`Thms`).

This module defines the interface and its instances. Running Core's interpreter over a
lawful `R` is a separate step.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution

/-- A representation of linear memory: the operations Core performs on memories. -/
class MemRep (R : Type) where
  /-- The bytes the representation stands for. -/
  toBytes : R → ByteArray
  size : R → Nat
  load : R → Nat → (count : Nat) → Option (BitVec (8 * count))
  store : R → Nat → {count : Nat} → BitVec (8 * count) → Option R
  readBytes : R → Nat → Nat → Option ByteArray
  writeBytes : R → Nat → ByteArray → Option R
  grow? : R → Option Nat → Nat → Option R
  zeros : Nat → R

/-- **The laws**: every operation agrees with the `ByteArray` specification through `toBytes`. -/
class LawfulMemRep (R : Type) [MemRep R] : Prop where
  size_eq : ∀ m : R, MemRep.size m = (MemRep.toBytes m).size
  load_eq : ∀ (m : R) a count, MemRep.load m a count = Memory.load (MemRep.toBytes m) a count
  store_eq : ∀ (m : R) a {count} (w : BitVec (8 * count)),
    (MemRep.store m a w).map MemRep.toBytes = Memory.store (MemRep.toBytes m) a w
  readBytes_eq : ∀ (m : R) a count,
    MemRep.readBytes m a count = Memory.readBytes (MemRep.toBytes m) a count
  writeBytes_eq : ∀ (m : R) a bs,
    (MemRep.writeBytes m a bs).map MemRep.toBytes = Memory.writeBytes (MemRep.toBytes m) a bs
  grow_eq : ∀ (m : R) max d,
    (MemRep.grow? (R := R) m max d).map MemRep.toBytes = Memory.grow? (MemRep.toBytes m) max d
  zeros_eq : ∀ n, (MemRep.toBytes (MemRep.zeros (R := R) n)).data.toList = List.replicate n 0

/-! ## The specification -/

instance : MemRep ByteArray where
  toBytes := id
  size := ByteArray.size
  load := Memory.load
  store := Memory.store
  readBytes := Memory.readBytes
  writeBytes := Memory.writeBytes
  grow? := Memory.grow?
  zeros n := ⟨Array.replicate n 0⟩

/-! ## Trees of bytes -/

/-- A well-formed `KBytes` tree as linear memory. -/
structure KMem where
  /-- The tree. -/
  t : Silmaril.KBytes
  /-- It is well formed. -/
  wf : t.wf = true

namespace KMem

open Silmaril.KBytes

/-- The leaf size of fresh and grown memory: 4 KiB, as in the KernelEval measurements. -/
def leafBytes : Nat := 4096

def toBytes (m : KMem) : ByteArray := m.t.toByteArray

def load (m : KMem) (a count : Nat) : Option (BitVec (8 * count)) :=
  (m.t.readLE a count).map (BitVec.ofNat (8 * count))

def writeBytes (m : KMem) (a : Nat) (bs : ByteArray) : Option KMem :=
  if h : a + bs.size ≤ m.t.len then
    some ⟨m.t.write a bs.size (leVal bs.data.toList), Silmaril.KBytes.wf_write _ _ _ _ m.wf h⟩
  else none

def store (m : KMem) (a : Nat) {count : Nat} (w : BitVec (8 * count)) : Option KMem :=
  writeBytes m a (Memory.encodeLE count w.toNat)

def readBytes (m : KMem) (a count : Nat) : Option ByteArray :=
  if a + count ≤ m.t.len then some ⟨⟨(m.t.toList.drop a).take count⟩⟩ else none

/-- `n` zero bytes in `leafBytes` leaves. -/
def zeros (n : Nat) : KMem := ⟨zerosCanon leafBytes n, Silmaril.KBytes.wf_zerosCanon _ _⟩

def grow? (m : KMem) (maximum : Option Nat) (delta : Nat) : Option KMem :=
  if m.t.len % Memory.pageSize = 0 ∧ m.t.len / Memory.pageSize + delta ≤ Memory.maxPages ∧
      (maximum.isNone ∨ m.t.len / Memory.pageSize + delta ≤ maximum.getD 0) then
    some ⟨m.t ++ (zeros (delta * Memory.pageSize)).t,
      Silmaril.KBytes.wf_append m.wf (zeros _).wf⟩
  else none

end KMem

instance : MemRep KMem where
  toBytes := KMem.toBytes
  size m := m.t.len
  load := KMem.load
  store := KMem.store
  readBytes := KMem.readBytes
  writeBytes := KMem.writeBytes
  grow? := KMem.grow?
  zeros := KMem.zeros

end Silmaril.Wasm.Execution
