module

public import Silmaril.Wasm.KernelEval.KBytesMem
public import Silmaril.Wasm.KernelEval.MemThms
import Silmaril.Proofs.Wasm.KernelEval.KBytesMem

@[expose] public section

/-!
# Kernel evaluation of a small Wasm subset: `KBytes` as Wasm memory, results

Proofs in `Silmaril.Proofs.Wasm.KernelEval.KBytesMem`, from the `KBytes` interface
(`readLE_eq`, `toList_slice`, `toList_append`, `wf_slice`, `wf_append`, `toList_ofChunks`).

* **`memSimOn_kRope`**, **`memSimOn_kPath`**: both stores on `Silmaril.KBytes` simulate the
  list reference under `kToListMem`, for trees with correct cached lengths (`wf`), which
  stores preserve;
* `kwrite_spec`: the path-copying write keeps `wf` and splices the written bytes in;
* `wf_kzeros`, `kzeros_toListMem`: the zero memory.
-/

namespace Silmaril.Wasm.KernelEval

open Silmaril

theorem kwrite_spec (t : KBytes) (off w v : Nat) (ht : t.wf = true) (h : off + w ≤ t.len) :
    (kwrite t off w v).wf = true ∧ (kwrite t off w v).toList =
      t.toList.take off ++ KBytes.unpack w v ++ t.toList.drop (off + w) :=
  Proofs.Wasm.KernelEval.kwrite_spec t off w v ht h

theorem memSimOn_kRope : MemSimOn (fun m : KRope => m.t.wf = true) (fun m => kToListMem m.t) :=
  Proofs.Wasm.KernelEval.memSimOn_kRope

theorem memSimOn_kPath : MemSimOn (fun m : KPath => m.t.wf = true) (fun m => kToListMem m.t) :=
  Proofs.Wasm.KernelEval.memSimOn_kPath

theorem wf_kzeros (n : Nat) : (kzeros n).wf = true := Proofs.Wasm.KernelEval.wf_kzeros n

theorem kzeros_toListMem (n : Nat) : kToListMem (kzeros n) = ⟨List.replicate n 0⟩ :=
  Proofs.Wasm.KernelEval.kzeros_toListMem n

end Silmaril.Wasm.KernelEval
