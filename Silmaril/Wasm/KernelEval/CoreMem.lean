module

public import Silmaril.Wasm.KernelEval.Memories
public import Silmaril.Wasm.Verify.Kernel.Thms

@[expose] public section

/-!
# Kernel evaluation of a small Wasm subset: Core's memory

Core's own memory type, `Silmaril.Wasm.Execution.Memory.Bytes` (Lean's `ByteArray`), as an
implementation of the subset's memory interface, in two ways that are proved equal:

* `CoreMem`: the specification accesses `Memory.load`/`Memory.store` (`ByteArray.extract` and
  `copySlice`), which Core 3.0 execution and the verified interpreter `runInvoke?` use;
* `KMem`: the accesses of the existing kernel evaluator `Silmaril.Wasm.Verify.Kernel`
  (`fload`/`fstore`: the bytes as a list, by `List.rec`), used by `runInvokeK`; with the
  zero memory as `⟨⟨List.replicate n 0⟩⟩` its unwritten tail stays lazy, as in
  `Silmaril.Wasm.Auto2.Kernel`.

Results (`Silmaril.Wasm.KernelEval.CoreMemThms`):

* `kmem_load_eq`, `kmem_store_eq`: the kernel path is the specification (from `fload_eq`,
  `fstore_eq`);
* **`memSim_coreMem`**, `memSim_kMem`: both simulate the list reference `ListMem` under the
  byte bijection `toListMem`, so every representation of `Silmaril.Wasm.KernelEval.MemThms`
  (packed, overlay, page tree) computes the same loads and stores as Core's
  `Memory.load`/`Memory.store` on the corresponding `ByteArray`.

This is where the subset meets Core's memory functions; a kernel-byte representation of the
core work plugs in the same way (a `MemOps` instance and a `MemSim` to `ListMem`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.KernelEval

open Silmaril.Wasm.Execution

/-- Core's memory with the specification accesses. -/
structure CoreMem where
  bytes : Memory.Bytes

/-- Core's memory with the accesses of the kernel evaluator. -/
structure KMem where
  bytes : Memory.Bytes

instance : MemOps CoreMem where
  load m a k := (Memory.load m.bytes a k).map BitVec.toNat
  store m a k v := (Memory.store m.bytes a (BitVec.ofNat (8 * k) v)).map CoreMem.mk

noncomputable instance : MemOps KMem where
  load m a k := (Verify.Kernel.fload m.bytes a k).map BitVec.toNat
  store m a k v := (Verify.Kernel.fstore m.bytes a (BitVec.ofNat (8 * k) v)).map KMem.mk

/-- The list memory of a byte array. -/
def toListMem (b : Memory.Bytes) : ListMem := ⟨b.data.toList.map UInt8.toBitVec⟩

/-- `n` zero bytes, as a list under the byte array (lazy in the kernel). -/
def KMem.zeros (n : Nat) : KMem := ⟨⟨⟨List.replicate n 0⟩⟩⟩

end Silmaril.Wasm.KernelEval
