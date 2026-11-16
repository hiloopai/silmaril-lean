# Memory representations behind laws (`Silmaril.Wasm.Execution.MemRep`)

This is step 1 of running Core on a scalable memory: a law-governed interface with two lawful
instances.

* **`MemRep R`** provides the operations Core performs on a memory: `size`, `load`, `store`,
  `readBytes`, `writeBytes`, `grow?` and `zeros`, plus `toBytes : R → ByteArray`.
* **`LawfulMemRep R`** says each operation equals the `ByteArray` specification
  (`Memory.load`, `Memory.store`, …) through `toBytes`.
* **`ByteArray`** is the specification itself. Its laws hold by `rfl` or `Option.map_id'`.
* **`KMem`** is a well-formed `KBytes` tree from `Prelude.Bytes`.
  * Loads are `readLE`.
  * Stores and bulk writes are the path-copying `KBytes.write` from `Prelude.Bytes.Write`,
    which rewrites only the touched leaves.
  * `zeros` and `grow?` use canonical 4 KiB zero leaves.
  * Its laws are proved from the existing `KBytes` theorems: `readLE_eq`, `toList_write`,
    `unpack_leVal` and `toList_zerosCanon`. Two new digit lemmas tie them to Core:
    `decodeLE_eq` and `encodeLE_toList`.
  * The KernelEval benchmarks (#133, `KPath`) measured this representation and its writes in
    the kernel.

## Kernel measurement

The check stores at 64 scattered addresses of a 1 MiB memory, then loads one back. It is
`MemRepExamples.kmem_scatter`, run with `decide +kernel`. One run on a 2-vCPU sandbox:

| representation | result | wall | peak RSS |
|---|---|---|---|
| `KMem` | passes | 6 s | 0.9 GB |
| `ByteArray` (Core's `Memory.store` on `main`) | `(kernel) deterministic timeout` | 179 s | 24.7 GB |

## Core over a representation (step 2)

* **Generic memory instances.** `MemInst (R : Type := ByteArray)`, `Store (H) (R := ByteArray)`
  and `Config (H) (R := ByteArray)` (`Execution/Core/Runtime.lean`). The default argument
  keeps every existing `MemInst`, `Store H` and `Config H` at `ByteArray`, with the same
  names, fields and meaning. A small delaborator prints projections at the default as
  `s.mems` (Lean's application delaborator would print `s.mems ByteArray`).
* **`MemRep.extend`** (append `n` zero bytes, unchecked) with the law `extend_eq`; both
  instances satisfy it (`KMem.extend_eq`). Core's `$growmem` checks its own bounds and
  appends through it.
* **Generic interpreter memory family.** The memory instructions of the computable
  interpreter (`SingleThreaded/Exec/Memory.lean`: loads, stores, `memory.size`/`grow`/`fill`/
  `copy`/`init`, `data.drop`, `Mem.stepArgs`, `memoryStep?`) take `[MemRep R] (s : Store H R)`
  and use `MemRep.load`/`store`/`size`, `MemInst.pagesR` and `MemInst.growR?`
  (`Execution/Core/MemRep.lean`). At `ByteArray` these are the specification operations
  (`MemRep.load_byteArray`, …, `MemInst.growR?_byteArray`), so soundness and completeness
  (`memoryStep?_sound`, `memoryStep?_complete`) and everything downstream are unchanged.
* **Simulation for the memory family** (`Execution/MemRep/Sim`). `Store.toBytes` reads every
  memory through `toBytes`. At a lawful `R`, `memoryStep?_toBytes` and `Mem.stepArgs_toBytes`
  show that a memory-family step on `Store H R` then `toBytes` is the step on
  `s.toBytes`.

## Not yet

1. Make `stepI` (`interpHead`, `HeadFn`, `step?`, `run?`) generic in `R`. The other eight
   families (`parametric`, `numeric`, `vector`, `variable`, `table`, `reference`, the two
   aggregate families, `control`/`admin`) only read and update non-memory store fields, but
   their signatures and the `Store` helpers they use (`Store.global?`, `Store.setGlobal`,
   `Store.table?`, `Store.addStruct`, …) are stated at `Store H`. Each needs the same
   generalization, plus a commuting lemma with `Store.toBytes` (a field-wise rewrite, since
   `toBytes` only touches `mems`). Host calls (`HostSemantics`) are relations on `Store H`
   and need a representation-level host interface or a `toBytes` pre-/post-composition.
2. With that, `stepI_toBytes : (stepI o c).map Config.toBytes = stepI o c.toBytes` follows
   from `memoryStep?_toBytes` and the per-family lemmas; `runI` then commutes by induction.
3. Make the component engine (`core3Exec`) and REF generic in `R`, then transfer REF runs
   and acceptance along `Store.toBytes`.
