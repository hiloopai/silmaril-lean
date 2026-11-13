module

public import Silmaril.Wasm.KernelEval.CoreMem
import Silmaril.Proofs.Wasm.KernelEval.CoreMem

@[expose] public section

/-!
# Kernel evaluation of a small Wasm subset: Core's memory, results

Proofs in `Silmaril.Proofs.Wasm.KernelEval.CoreMem`; see `Silmaril.Wasm.KernelEval.CoreMem`.
-/

namespace Silmaril.Wasm.KernelEval

open Silmaril.Wasm.Execution

theorem kmem_load_eq (m : Memory.Bytes) (a k : Nat) :
    MemOps.load (KMem.mk m) a k = MemOps.load (CoreMem.mk m) a k :=
  Proofs.Wasm.KernelEval.kmem_load_eq m a k

theorem kmem_store_eq (m : Memory.Bytes) (a k v : Nat) :
    (MemOps.store (KMem.mk m) a k v).map KMem.bytes =
      (MemOps.store (CoreMem.mk m) a k v).map CoreMem.bytes :=
  Proofs.Wasm.KernelEval.kmem_store_eq m a k v

theorem memSim_coreMem : MemSim (fun m : CoreMem => toListMem m.bytes) :=
  Proofs.Wasm.KernelEval.memSim_coreMem

theorem memSim_kMem : MemSim (fun m : KMem => toListMem m.bytes) :=
  Proofs.Wasm.KernelEval.memSim_kMem

end Silmaril.Wasm.KernelEval
