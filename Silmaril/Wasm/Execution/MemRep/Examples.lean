module

public import Silmaril.Wasm.Execution.MemRep.Thms

/-! # Memory representations: kernel tests (`decide +kernel`)

* A 1 MiB `KMem` takes 64 scattered 4-byte stores across its whole range and reads one back
  (`kmem_scatter`). With Core's `ByteArray` memory the same check hits the kernel's
  deterministic timeout after about 3 minutes and 25 GB (`docs/projects/wasm-memrep.md`).
* Small agreement checks against the `ByteArray` specification through `toBytes`: a store, a
  bulk write, an out-of-range store, and growth by a page.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.MemRepExamples

/-- Store `i + 1` at a scattered address, for `i < n`, then read the 7th one back. -/
def scatter (R : Type) [MemRep R] (size n : Nat) : Option Nat := Id.run do
  let mut m : Option R := some (MemRep.zeros size)
  for i in List.range n do
    m := m.bind fun m => MemRep.store m ((i * 16411) % (size - 4)) (count := 4)
      (BitVec.ofNat 32 (i + 1))
  return m.bind fun m => (MemRep.load m ((7 * 16411) % (size - 4)) 4).map BitVec.toNat

theorem kmem_scatter : scatter KMem 1048576 64 = some 8 := by decide +kernel

/-- Small memories: the same results through either representation. -/
example : scatter KMem 256 16 = scatter ByteArray 256 16 := by decide +kernel

example : ((MemRep.store (MemRep.zeros 16 : KMem) 3 (count := 2) (BitVec.ofNat 16 0x0102)).map
    fun m => (MemRep.toBytes m).data.toList) =
    some [0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel

example : ((MemRep.writeBytes (MemRep.zeros 8 : KMem) 6 ⟨#[7, 8]⟩).map
    fun m => (MemRep.toBytes m).data.toList) = some [0, 0, 0, 0, 0, 0, 7, 8] := by decide +kernel

example : (MemRep.store (MemRep.zeros 8 : KMem) 6 (count := 4) 0).isNone = true := by
  decide +kernel

example : ((MemRep.grow? (MemRep.zeros 0 : KMem) none 1).map MemRep.size) = some 65536 := by
  decide +kernel

/-- A bulk read across two 4 KiB leaves observes exactly the bytes written there. -/
example : (do
    let memory ← MemRep.writeBytes (MemRep.zeros 8192 : KMem) 4095 ⟨#[17, 34]⟩
    let bytes ← MemRep.readBytes memory 4094 4
    pure bytes.data.toList) = some [0, 17, 34, 0] := by decide +kernel

example : (MemRep.readBytes (MemRep.zeros 8192 : KMem) 8192 0).map ByteArray.size =
    some 0 := by decide +kernel

example : (MemRep.readBytes (MemRep.zeros 8192 : KMem) 8193 0).isNone = true := by
  decide +kernel

/-- The `ByteArray` instance exercises the existing Core operations through the public interface. -/
example : (do
    let memory ← MemRep.store (MemRep.zeros 2 : ByteArray) 0 (count := 2) 0x2211
    let memory := MemRep.extend memory 1
    let bytes ← MemRep.readBytes memory 0 3
    pure bytes.data.toList) = some [17, 34, 0] := by decide +kernel

example : (MemRep.grow? ByteArray.empty (some 0) 1).isNone = true := by decide +kernel

end Silmaril.Wasm.Execution.MemRepExamples
