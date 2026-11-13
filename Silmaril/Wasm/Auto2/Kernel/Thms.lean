module

public import Silmaril.Wasm.Auto2.Kernel.Defs
public import Silmaril.Proofs.Wasm.Auto2.Kernel.Inst

@[expose] public section

/-!
# Kernel-cheap instantiation: results

Proofs in `Silmaril.Proofs.Wasm.Auto2.Kernel.{MemInit,Inst}`.

* `memoryInitLoop_fast`, **`memoryInitLoopK_eq : memoryInitLoopK = memoryInitLoop`**: the byte
  loop of `memory.init` is one `writeL` of the whole segment on the fast path;
* **`instantiateOnceK?_eq : instantiateOnceK? = instantiateOnce?`** (through
  `initDataSegK?_eq`, `initDataListK?_eq`, `initSegmentsK?_eq`, `prepareDirectK?_eq`);
* **`instK?_eq`**: `(validate? m).isSome = true → instK? m = (instance? m).map (·.2)`;
* `bytesEqL_eq`, `sumCheckXK_eq`;
* the front end's checks over `instK?`, given that both modules validate:
  **`checkAmongX_eq_K`**, `liftAmong_eq_K`, `fnBody?_eq_K`, `cexWith_eq_K`.

A certificate proves `(validate? m).isSome = true` once per module by `decide +kernel`, rewrites
each later goal with these equations, and decides it by `decide +kernel` (or `kernel_rfl`) on
the `K` functions: no validation, and memories built lazily in linear time.
-/
