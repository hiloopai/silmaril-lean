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

## REF over `E.withStore I` and REF over `E` (step 5, partial)

`acceptedK_hi` is about REF over `core3K neverFail`. `refBytesSystem` (and `hi_mem_of_runHi`)
use `core3 neverFail`. This step proves a REF-level simulation that is conditional on related
programs. It does **not** yet give `"hi!"` in `refBytesSystem` unconditionally.

* **Component data indexed by the static part** (`Engine/Static/Defs.lean`). `CoreEngine.Static`
  has the module, extern and address types of an engine, and `CoreEngine.toStatic` (reducible, also
  a coercion) projects them. The plain-data REF types are now indexed by it: `CanonOpts`,
  `LiftLowerContext`, `ResolvedBuiltin`, `CanonHost`, `ResourceType`, `BufferDesc`, `End`,
  `Caller`, `Task`, `CFuncInst`, `Canon.Ret`, `ThreadBody`, `LoopPoint`, `Canon.Call`,
  `Instantiate.ItemVal`, `Closure` and `Frame`. Every use `Task E` with `E : CoreEngine` elaborates
  to `Task E.toStatic`, so no statement changed. Since `(E.withStore I).toStatic` unfolds to
  `E.toStatic`, these types agree across the two engines by definition. In particular the core
  store's host type `CanonHost E` agrees, so no host renaming (`Store.mapH`) is needed. One proof
  needed an explicit engine argument (`Param/Core3R/Link/InstImpDefs.lean`).
* **The relation** (`Reference/Machine/Transfer/Defs.lean`), for `S : E.StoreSim I`:
  * `mapStore S` maps the core store of a `CStore` by `S.φ` and keeps the other fields.
  * `ProgRel S` is a logical relation on `Canon.P`. The two programs issue the same operations
    with the same data. `get` continuations are related at `mapStore`-related stores, and
    `modify` functions commute with `mapStore`.
  * `CfgRel`, `ActRel`, `FocusRel`, `SegRel`, `LabelRel` and `DispatchRel` lift it to
    configurations, labels and dispatchers.
* **The simulation** (`Transfer/Thms.lean`, proofs in
  `Proofs/Wasm/Component/Reference/Transfer.lean`). `step_sim` and `steps_sim`: given related
  dispatchers, every step or run over `E.withStore I` is matched over `E` from a related
  configuration, with related labels. Every rule of `Machine.Step` is covered, including faults
  and host events. The host-frame programs `invokeProg`, `tickProg`, `cancelProg` and `runProg`
  are proved related to themselves. Some commutations, such as `CStore.candidates` with
  `mapStore`, hold by definition, but the elaborator does not unfold two instances of one
  matcher at different engines when the discriminant is stuck. These are closed by `kernel_rfl`
  (`Eq.refl`, checked by the kernel).
* **Acceptance** (`Wasi/Component/Accept/Ref/Transfer/Thms.lean`). `accepted_of_withStore`:
  `Accepted` over `E.withStore I` gives `Accepted` over `E`. It needs two hypotheses: the
  acceptor's dispatchers are `DispatchRel`-related, and the instantiation programs
  `acceptLinkedProg c` are `ProgRel`-related.
* **`"hi!"`, conditionally** (`Ref/KMem/Examples.lean`). `hi_mem_of_progRel`: the two
  hypotheses for `core3Sim neverFail KMem` give `refBytesSystem first.prof acceptHiBytes hi` from
  `acceptedK_hi`.

* **Pilot of the obligations** (`Reference/Canon/Transfer/Thms.lean`). The `Canon.Context`
  programs that touch the core store, `ptrType`, `memLen`, `readMem` and `writeMem`, are
  `ProgRel S`-related to themselves for every `S`. The proofs use only the memory laws of the
  store simulation.

### What remains

The two hypotheses are a parametricity statement: the REF programs reachable from
`acceptLinkedProg` and `Canon.dispatch` are related to themselves across the two engines. Lean
has no internal parametricity, so each generic definition needs its own proof. That means about
500 definitions in `Canon` and `Instantiate`, plus the `Runtime` helpers they use. Two ways to
discharge them:

Only 11 program definitions read or write `CStore.core`. In `Canon.Context` these are
`ptrTypeIn`, `memBytes?`, `memLen`, `readMem`, `writeMemSt` and `writeMem`; the four programs
among them are related by the pilot. The others are `threadNewIndirect` (`Canon.Builtins.Thread`)
and `setCoreSt`, `allocHostSt`, `addrTypesOf`, `allocCoreHost` and `instantiateCore`
(`Instantiate`). Every other program only reads or writes fields that `mapStore` keeps, but
still needs its own `ProgRel` proof, because the program terms differ between the two engines.

1. Prove `ProgRel` compositionally for each program, using `ProgRel.bind` and the primitive
   lemmas. Pure store reads that do not touch `core` commute by definition (`kernel_rfl`). Reads
   and writes of the core store need the `StoreSim` laws.
2. Refactor REF so that programs never see the core store. Core-store accesses (about 200 uses of
   `CStore.core`) would become engine operations issued as effects, and the component store
   without `core` would depend only on `E.toStatic`. Then the programs over the two engines are
   the same term, and only the machine's handling of the new effects needs `StoreSim`.

Until one of these is done, `hi_mem_of_runHi` over `core3` stays conditional on the native
`#guard runHi`, and `hi_mem_of_progRel` stays conditional on the relational hypotheses. The
`ByteArray` kernel run fails on this branch (table above).
