module

public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Proofs.Wasm.Verify.Kernel.Basic

@[expose] public section

/-!
# Kernel-reducible runs of the verified interpreter: results

Proofs in `Silmaril.Proofs.Wasm.Verify.Kernel.Basic`.

* `fload_eq : fload = Memory.load`, `fstore_eq : fstore = Memory.store` (the list-recursive
  memory accesses are the specification's);
* `headF_eq : headF o = interpHead o`;
* **`runIF_eq : runIF o = runI o`** and **`runInvokeF_eq : runInvokeF o = runInvoke? o`**: a
  statement about silmaril-lean's verified interpreter (`runInvoke?`, whose runs are Core runs,
  `runInvoke?_sound`) can be proved by kernel evaluation of `runInvokeF` (`kernel_rfl`);
* `stepK_eq : stepK head d = step? head`, **`runIK_eq : runIK o = runI o`** and
  **`runInvokeK_eq : runInvokeK o = runInvoke? o`**: the same with a structural driver (about 2×
  faster in the kernel on loops).
-/
