# Memory representations behind laws (`Silmaril.Wasm.Execution.MemRep`)

This is step 1 of running Core on a scalable memory: a law-governed interface with two lawful
instances.

* **`MemRep R`** provides the operations Core performs on a memory: `size`, `load`, `store`,
  `readBytes`, `writeBytes`, `grow?`, `extend` and `zeros`, plus `toBytes : R → ByteArray`.
  `grow?` enforces the Core page bounds. `extend` appends a caller-specified number of zero bytes.
* **`LawfulMemRep R`** says each operation equals the `ByteArray` specification
  (`Memory.load`, `Memory.store`, …) through `toBytes`.
* **`ByteArray`** is the specification itself. Its laws hold by `rfl` or `Option.map_id'`.
* **`KMem`** is a well-formed `KBytes` tree from `Prelude.Bytes`.
  * Loads are `readLE`.
  * Bulk reads check bounds and materialize only the requested `KBytes.slice`.
  * Stores and bulk writes are the path-copying `KBytes.write` from `Prelude.Bytes.Write`,
    which rewrites only the touched leaves.
  * `zeros`, `extend` and `grow?` use canonical 4 KiB zero leaves.
  * Its laws use the existing `KBytes` theorems `readLE_eq`, `toList_slice`,
    `toList_write`, `unpack_leVal` and `toList_zerosCanon`. Two digit lemmas tie them to Core,
    `decodeLE_eq` and `encodeLE_toList`.
  * The KernelEval benchmarks (#133, `KPath`) measured this representation and its writes in
    the kernel.

## Kernel measurement

The check stores at 64 scattered addresses of a 1 MiB memory, then loads one back.
`MemRepExamples.kmem_scatter` uses `decide +kernel`. These measurements were recorded for
the original MemRep review on a 2-vCPU sandbox:

| representation | result | wall | peak RSS |
|---|---|---|---|
| `KMem` | passes | 6 s | 0.9 GB |
| `ByteArray` (Core's `Memory.store` at the time) | `(kernel) deterministic timeout` | 179 s | 24.7 GB |

```sh
lake build --wfail +Silmaril.Wasm.Execution.MemRep.Examples
```

The examples also cover checked growth, byte order in the `ByteArray` instance, and a bulk read
across a 4 KiB leaf boundary.

## Interpreter integration

Core's interpreter and stores still use `ByteArray` (`MemInst.bytes`). Running REF and Core on
`KMem` takes three more steps:

1. Make the interpreter's memory operations go through `MemRep`, keeping `ByteArray` as the
   default so existing statements are unchanged.
2. Prove an engine simulation that maps memories by `toBytes`.
3. Transfer REF runs and acceptance along that simulation.
