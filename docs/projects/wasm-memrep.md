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

## The interpreter over a representation (step 3)

* **Generic interpreter.** Every instruction family of the computable interpreter
  (`SingleThreaded/Exec`: `parametricStep?`, `numericStep?`, `vectorStep?`, `variableStep?`,
  `tableStep?`, `memoryStep?`, `referenceStep?`, `aggNewStep?`, `aggAccessStep?`,
  `controlStep?`, `adminStep?` and their helpers), the driver (`Drv.layer`, `step?`, `run?`,
  `HeadFn H R`), `interpHead`, `stepI` and `runI` take `Store H R` / `Config H R`. So do the
  store helpers they use (`Store.global?`, `table?`, `elem?`, `tag?`, `func?`, `funcAt?`,
  `setGlobal`, `setTable`, `setElem`, `setStructField`, `setArrayField`, `addStruct`,
  `addArray`, `addExn`, `Ref.type?`, `refOk?`) and the thread level (`Core.invoke`,
  `Thread.config`, `Thread.code`, `hostArity?`, `decompose?`, `resume`, `resumeResult`,
  `statusC`, `internalC`, `runC`). Apart from definitions, only the driver lemmas `step?_nil`, `step?_cons` and the
  `run?` lemmas `run?_zero`, `run?_succ_none`, `run?_succ_some`, `run?_mono` and
  `run?_stopped` changed: they are now stated over any `R` with the same proofs. Every other
  theorem keeps its statement and proof at the default `ByteArray`. The relational
  side (`Step`, `Head`, `HeadSound`, `HeadExact`, `IsCtxtHead`, `Internal`, `status`) stays
  at `ByteArray`.
* **Simulation** (`Execution/MemRep/Sim/Thms.lean`, proofs in
  `Proofs/Wasm/Execution/MemRepStep.lean`). `Store.toBytes` changes only `mems`, so each
  non-memory family commutes with it at *any* `R`, with no law. Each lemma pushes
  `Option.map` through binds, `if`s and `match`es; store reads and updates of other fields
  commute by `rfl`. The lemmas are `parametricStep?_toBytes`, …, `adminStep?_toBytes` and
  `refOk?_toBytes`. At a lawful `R`:
  * `interpHead_toBytes`: the head step commutes with `toBytes`;
  * `step?_toBytes`: any driver whose head step commutes;
  * `stepI_toBytes : (stepI o c).map Config.toBytes = stepI o c.toBytes`;
  * `runI_toBytes : Prod.map Config.toBytes id (runI o n c) = runI o n c.toBytes`, by
    induction on fuel;
  * thread level: `statusC_toBytes`, `internalC_toBytes`, `runC_toBytes`, `resume_toBytes` and
    `decompose?_toBytes`. These are the functions `core3Exec` uses for its status, internal
    step and resumption.
  Combined with `stepI_sound`/`runI_steps` at `ByteArray`, every step or run on `KMem` is,
  read through `toBytes`, a Core reduction.
* **Host calls.** The interpreter never applies a host relation. `stepI` is the host-free step
  (`noHost`), and a call to a host function is not a head step. `statusC` reports it as
  `callout h args` and the embedder answers with `resume` (as `core3`'s `status`/`resume` do).
  Callouts and resumption are the same on `s` and `s.toBytes` (`statusC_toBytes`,
  `resume_toBytes`), so this layer needs no representation-level host interface. Host
  *functions* acting on memory (the component engine's `memRead?`/`memWrite?` used by the
  canonical ABI) are engine fields. They are still at `ByteArray`; see below.

### Kernel measurement (whole interpreter)

The program does 64 scattered `i32.store`s into a memory and then one `i32.load` (194
interpreter steps). The kernel runs it with `runI neverFail 300`, checked by `decide +kernel`.
The ByteArray runs used the same program truncated to the given fuel. Each row is one run on
a 2-vCPU sandbox. Wall time and peak RSS are for the whole `lean` process, including about
2.7 s and 1.3 GB of imports.

| representation | memory | steps | result | wall | peak RSS |
|---|---|---|---|---|---|
| `KMem` | 1 MiB | full run (194) | passes | 3.1 s | 1.35 GB |
| `KMem` | 64 KiB | full run (194) | passes | 2.9 s | 1.32 GB |
| `ByteArray` | 256 B | fuel 20 | passes | 99 s | 8.9 GB |
| `ByteArray` | 256 B | fuel 80 | passes | 377 s | 26.5 GB |
| `ByteArray` | 4 KiB / 16 KiB | full run | `decide` fails (kernel gives up) | 3–5 s | 1.4–1.7 GB |

The 1 MiB `KMem` run is `MemRepSimExamples.scatterRun` in `Execution/MemRep/Sim/Examples.lean`.

## Not yet

1. **A `KMem` core engine.** `core3`'s step side (`status`, `Internal`, `resume`, `invoke`)
   now runs on `Store H KMem` (`statusC (stepI o)`, `internalC (stepI o)`, `resume`), with the
   simulation lemmas above. A `CoreEngine` needs the remaining fields over `R` too:
   * instantiation (`prepareE?`: `instantiateOnce?`/`instantiateDirect?`, `allocModule?`, data
     segment initialisation into memory);
   * `allocHost` and `externTypeE?`/`funcTypeE?` (store reads only);
   * the canonical-ABI memory accessors `SingleThreaded.memSize?`/`memRead?`/`memWrite?`
     (through `MemRep.readBytes`/`writeBytes`).
   Each needs a `toBytes` lemma. Instantiation is the largest; the data-segment writes go
   through `MemRep.writeBytes`.
2. **Carrying REF runs across engines.** REF (`Component.Machine`, `acceptRun`, `Accepted`) is
   parametric in its `CoreEngine`. Transferring a run on a `KMem` engine to `core3 neverFail`
   needs an engine-simulation notion (a store map commuting with every engine field) and a
   proof that the REF machine, oracle and `Steps` respect it. None exists yet. Without it,
   `Ref.Examples.acceptHiBytes` cannot be kernel-checked on `KMem`. Today it is checked only by
   compiled evaluation (`#guard runHi`).
