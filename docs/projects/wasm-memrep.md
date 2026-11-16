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

## The engine over a representation (step 4)

* **Generic instantiation and accessors.** Everything `core3`'s store fields use now takes
  `Store H R`:
  * constant evaluation (`constInstr?`, `structNew?`, `arrayNewFixed?`, `constExpr?`,
    `evalConst?`) and `$evalglobals`/`$evalexprs(s)` (`evalGlobals?`, `evalExprs?`,
    `evalExprss?`);
  * allocation (`allocTag`, …, `allocElem`, `allocMany`, `allocModule?`, `ModuleInst.initial`);
  * segment initialisation (`tableInitLoop`, `memoryInitLoop`, `elemDrop?`, `dataDrop?`,
    `initElemSeg?`, …, `initSegments?`) and `prepare?`, `instantiate?`, `prepareDirect?`,
    `instantiateDirect?`, `instantiateOnce?`;
  * `externAddrType?`, `externAddrOk?`, `externAddrsOk?`;
  * the component accessors `SingleThreaded.allocHost`, `memSize?`, `memAddrType?`,
    `tableAddrType?`, `memRead?`, `memWrite?`, `tableFunc?`;
  * the engine's own `Core3.externTypeE?`, `prepareE?`, `prepareSpecE?`, `statusE`, `funcTypeE?`.

  Bytes are touched only by `allocMem` (`MemRep.zeros`), `memoryInitLoop` (`MemRep.size`,
  `MemRep.store`) and the accessors (`MemRep.size`, `readBytes`, `writeBytes`). Theorem
  statements are unchanged, except that `memoryInitLoopK_eq` and `tableInitLoopK_eq` (Auto2
  kernel) now name the implicit `ByteArray`. Some proofs needed small edits:
  * proofs that unfold these definitions at `ByteArray` rewrite with the `rfl` lemmas
    `MemRep.size_byteArray`, `store_byteArray`, `readBytes_byteArray`, `writeBytes_byteArray` and
    `zeros_byteArray`, now all in `Execution/MemRep/Defs.lean`;
  * a few proofs compared a `match` of a generic definition with the same `match` written at
    `ByteArray` (by `rfl` or `show`). Lean does not unfold one auxiliary matcher into the other,
    so these proofs now case on the discriminant.
* **Simulation lemmas** (`Execution/MemRep/Inst/Thms.lean`, proofs in
  `Proofs/Wasm/Execution/MemRepInst.lean`). These follow `instantiateOnce?_mapH`:
  * at any `R`: `evalConst?_toBytes`, `evalGlobals?_toBytes`, `externAddrType?_toBytes`,
    `externAddrsOk?_toBytes`, `allocHost_toBytes`, `memAddrType?_toBytes`,
    `tableAddrType?_toBytes` and `tableFunc?_toBytes`;
  * at a lawful `R`: `allocModule?_toBytes`, `initSegments?_toBytes`, `prepare?_toBytes`,
    `instantiateDirect?_toBytes`, `instantiateOnce?_toBytes`, `memSize?_toBytes`,
    `memRead?_toBytes` and `memWrite?_toBytes`.
* **Engine simulation** (`Component/Engine/Sim`).
  * `CoreEngine.StoreImpl E` is the store-dependent part of an engine over `E`'s static part.
    `E.withStore I` has `E`'s modules, types, addresses and threads, by definition.
  * `CoreEngine.StoreSim E I` is a store map `φ` that commutes with every store operation: `empty`,
    `externType?`, `prepare?`, `allocHost`, `funcType?`, the memory and table accessors, `status`
    and `resume`. It is also a functional bisimulation of `Internal` (`internal`,
    `internal_lift`).
  * `CoreEngine.ExecSim` relates executable steppers.
  * `Thms`: `StoreSim.steps` and `steps_lift` (runs), `diverges_iff`, `extends_iff`, `lawful`
    (`CoreEngine.Lawful` carries over) and `ExecSim.runCore`.
* **The `KMem` engine** (`Component/Engine/Core3K`).
  * `core3Impl o R` and `core3On o R := (core3 o).withStore (core3Impl o R)`, with
    `core3On_byteArray : core3On o ByteArray = core3 o` (by `rfl`).
  * `core3K o := core3On o KMem`, with the stepper `core3ExecK o`.
  * `core3Sim o R : (core3 o).StoreSim (core3Impl o R)` has store map `Store.toBytes`.
    `core3ExecSim` relates the steppers, and `core3On_lawful` gives the laws (from
    `core3_lawful`).
  * Consequences: `core3On_steps`, `core3On_steps_lift`, `core3On_diverges_iff` and
    `core3ExecOn_runCore`.
* **A component accepted in the kernel on `KMem`**
  (`Wasi/Component/Accept/Ref/KMem/Examples.lean`). For `Ref.Examples.acceptHiBytes`,
  `runHiK_true` checks the whole pipeline with `decide +kernel`: decode, validate, link the host
  `accept`, instantiate the core module with its 64 KiB memory and data segment, call `run`, and
  lift `list<u8>` from memory. `acceptedK_hi` then gives `Accepted` on REF over
  `core3K neverFail` for the decoded component, by `acceptRun_sound`.

### Kernel measurement (component acceptance)

One run each on a 2-vCPU sandbox. Times are for the whole `lean` process; the imports alone
take 5.2 s and 1.40 GB.

| engine | check | result | wall | peak RSS |
|---|---|---|---|---|
| `core3K neverFail` (`KMem`) | `runHiK = true` | passes | 5.6 s | 2.02 GB |
| `core3 neverFail` (`ByteArray`) | `runHi = true` | `(kernel) deep recursion detected` | 13.8 s | 3.42 GB |
| `core3 neverFail` (`ByteArray`), `maxRecDepth 1000000` | `runHi = true` | `decide` fails to reduce | 223 s | 31.5 GB |

Both checks use `decide +kernel`. The `ByteArray` rows are this branch's `ByteArray` memory
operations, without the separate `writeSlice` change of #707.

## REF over `E.withStore I` and REF over `E` (step 5)

`acceptedK_hi` is about REF over `core3K neverFail`. `refBytesSystem` (and `hi_mem_of_runHi`)
use `core3 neverFail`. This step proves a REF-level simulation and discharges its hypotheses, so
`"hi!"` is in `refBytesSystem` over `core3 neverFail` with no hypothesis (`hi_mem`).

* **Component data indexed by the static part** (`Engine/Static/Defs.lean`). `CoreEngine.Static`
  has the module, extern and address types of an engine, and `CoreEngine.toStatic` (reducible, also
  a coercion) projects them. The plain-data REF types are indexed by it: `CanonOpts`,
  `LiftLowerContext`, `ResolvedBuiltin`, `CanonHost`, `ResourceType`, `BufferDesc`, `End`,
  `Caller`, `Task`, `CFuncInst`, `Canon.Ret`, `ThreadBody`, `LoopPoint`, `Canon.Call`,
  `Instantiate.ItemVal`, `Closure`, `Frame`, and now also `CStore`, `ArenaField`, `AddrTypes`,
  `CopyAction`, `DtorRequest`, `HostImpl`, `Instantiate.Entry`, `Scope`, `TyScope`, `EntityT`
  and `Exports`. Every use `Task E` with `E : CoreEngine` elaborates to `Task E.toStatic`. Since
  `(E.withStore I).toStatic` unfolds to `E.toStatic`, these types agree across the two engines.
* **The core store is the machine's** (option 2 below). `CStore` no longer holds the core store;
  `Machine.Config.core` does (default `E.empty`). The effect signature `Canon.Op` is indexed by
  `CoreEngine.Static` and has four core operations:
  * `readCore`, answered with `CoreEngine.view E m.core : CoreView E (CanonHost E)`: the
    read-only queries extern type, function type test, memory and table address type, memory
    size, contents and write bounds, funcref entries, and the results (without the new store)
    of `allocHost` and `prepare?`;
  * `memWrite m ptr bytes`, `allocHost ty h`, `prepare md imports`: update `m.core` (no change
    when the engine operation fails).
  The 11 definitions that touched `CStore.core` now use them: `ptrTypeIn`, `memBytes?`,
  `LoadPre` and `addrTypesOf` take a `CoreView`; `memLen`, `readMem`, `threadNewIndirect`,
  `allocCoreHost` and `instantiateCore` read through `readCore`; `writeMem`, `allocCoreHost` and
  `instantiateCore` check through `readCore` and then update through the core operation, which
  mirrors the former `get`-then-`modify` structure (and `confine`'s treatment of it). `writeMemSt`,
  `setCoreSt` and `allocHostSt` are gone; `coreImportsWith?` is `coreImportsFor?` over an
  extern-type query. Invariant lemmas that assumed memory writes preserve a `CStore` invariant
  lost that hypothesis (`P.Inv.writeMem`, `storeString`, `StorePres`, …): memory writes no
  longer touch `CStore`.
* **The relation** (`Reference/Machine/Transfer/Defs.lean`), for `S : E.StoreSim I`:
  `ProgRel S` relates programs with the same operations, data and related continuations;
  `CfgRel` asks for equal component stores and `m.core = S.φ m'.core`.
* **The simulation** (`Transfer/Thms.lean`, proofs in
  `Proofs/Wasm/Component/Reference/Transfer.lean`). `step_sim` and `steps_sim` as before; the new
  rules use `view_φ : E.view (S.φ c) = (E.withStore I).view c` and the `memWrite?`, `allocHost`
  and `prepare?` laws. `ProgRel.refl`: every program is related to itself, because programs over
  the two engines have the same type.
* **Relatedness of concrete programs.** A program definition at `E.withStore I` and at `E` is the
  same term up to unfolding as long as its body uses only the static part and the store-free
  fields of the engine. The tactic `prog_rel_refl` closes `ProgRel S p' p` by `ProgRel.refl S p`
  and leaves that check to the kernel (the elaborator's unifier does not unfold the two
  applications). Values of an inductive type indexed by a whole `CoreEngine` would break this
  (constructors at different engines are not definitionally equal), which is why the types
  above moved to `CoreEngine.Static`.
* **Acceptance** (`Wasi/Component/Accept/Ref/Transfer/Thms.lean`). `accepted_of_withStore` (given
  related dispatchers and instantiation programs), `dispatchRel_dispatch` and
  `progRel_acceptLinkedProg` (both by `prog_rel_refl`, for every `E` and `I`), and
  `accepted_of_storeSim`: `Accepted` over `E.withStore I` gives `Accepted` over `E`.
* **`"hi!"`** (`Ref/KMem/Examples.lean`). `hi_mem : refBytesSystem first.prof acceptHiBytes hi`
  over `core3 neverFail`, from `acceptedK_hi` (the kernel run `runHiK_true`) and
  `accepted_of_storeSim (core3Sim neverFail KMem)`. `hi_mem_of_progRel` is kept.
  `Ref.Examples.hi_mem_of_runHi` (hypothesis: the native `#guard runHi`) is kept and superseded.
* `Reference/Canon/Transfer/Thms.lean`: the former pilot (`rel_ptrType`, `rel_memLen`,
  `rel_readMem`, `rel_writeMem`), now by `prog_rel_refl`.

### Kernel measurement (end to end)

One run each on a 2-vCPU sandbox, whole `lean` process (`lake env lean` on the module).

| module | checks | wall | peak RSS |
|---|---|---|---|
| `Wasi/Component/Accept/Ref/KMem/Examples.lean` | `runHiK_true` (`decide +kernel`), `acceptedK_hi`, `hi_mem_of_progRel`, `hi_mem` | 7.2 s | 1.46 GB |
| `Proofs/Wasi/Component/Accept/RefTransfer.lean` | `dispatchRel`, `progRel_acceptLinkedProg` (kernel checks of the two terms, for every `E`, `I`) | 3.1 s | 0.95 GB |
| `Proofs/Wasm/Component/Reference/Transfer.lean` | `view_φ`, `ProgRel.refl`, `step_sim`, `steps_sim` | 3.9 s | 0.86 GB |

### Notes

* Unfolding check. `prog_rel_refl` relies on every definition reachable from `dispatch` and
  `acceptLinkedProg` being exposed (`@[expose]`) and generic in its engine. A program that read
  a store-dependent field of its engine, or built a value of an inductive type indexed by a
  whole `CoreEngine`, would make the kernel check fail. It would not make the theorem false.
* Proof modules that ran REF programs step by step now take a `readCore` step where they used
  to take a `get` step for a core-store read. Lemmas that described a configuration through
  `{ s with core := c }` now set `Config.core`. A few internal proof definitions keep an unused
  core-store argument (`_cs`), so their call sites did not change.
