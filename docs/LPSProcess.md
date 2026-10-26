# LPS in Lean: the Linux process layer of OSS Verify

`Silmaril/Process/LPS/**` is an agentic (hand-guided, model-written) translation into Lean of
the Linux process layer of **LPS**, Theorem Labs' Rocq model `rocq-linux-process-semantics`
(MIT licence, copyright (c) 2026 Theorem Labs, PBC), and of the statement shapes of **OSS
Verify** (`oss-verify-proofs/theories/Shapes.v`, same licence).

| source | commit |
| --- | --- |
| `theorem-labs/rocq-linux-process-semantics` | `f1006fe8178338a499b5e5c41be83006c4edd058` (the commit `oss-verify-proofs/release.yaml` pins) |
| `theorem-labs/oss-verify-proofs` | `98e995d4daced70a0a4aa2c810854b88720735f1` (`Shapes.v` byte-identical to the historical `8f5f46768858af236a4270f9628e6beed9aa0e72` pin; [audit](LPSShapesParity.md)) |

Every translated definition names its upstream file and line in its docstring. The table at
the end of this document is generated from those docstrings, and every citation was checked
to name a line of the upstream file that contains the cited name: of 539 matches, the only
five flagged were prose mentions, not citations. The checker reads the clones as data and runs
nothing from them.

The machine translation (Rocq to Lean tooling) is separate; this translation is meant to be
compared with its output later.

## Layout

| Lean module | LPS source | contents |
| --- | --- | --- |
| `Basic` | `BvBase.v`, `State.v:33-556`, `Sys/Uapi.v` (part) | words and bytes, address-space constants (Sv39/48/57), allocation limits, errnos |
| `MemImage` | `MemImageType.v`, `RiscvSemantics.v:298-404` | segments, program-header facts, images, segment reads |
| `Fs` | `Fs.v` | the flat sorted file system |
| `Stream` | `State.v:1793-2366`, `FinInput.v:161-191` | stdin and `/dev/urandom` streams, network streams, the connection queue |
| `State` | `State.v` | syscall input and effect, user-memory readers, descriptors, sockets, pipes, the VM ledger, lazy backing and budget, the `Model`, events, `ProcInput`, `init_model` |
| `Monad` | `Monad.v` | the `Sys` specification monad with `unmodeled`, `choose`, `alt`; monad laws |
| `Syscall` | `Sys/Syscall.v`, `Sys/Uaccess.v` | return helpers, `errno_from`, ABI narrowing, user-buffer gates |
| `Uapi` | `Sys/Uapi.v` | the uapi constants and `struct stat` predicates, with x86-64 layout variants |
| `Uaccess` | `Sys/Uaccess.v`, `State.v:1024-1760`, `Sys/Syscall.v` | gate lemmas, C strings, `copy_bytes_map`, `iovec` import/scatter/gather, narrowings, x86-64 `access_ok` |
| `StateHelpers` | `State.v` | the remaining `Model` accessors and setters, fd/pipe/VM-ledger helpers, `mkProcInput` |
| `Sys/ReadWrite` | `Sys/Fs/ReadWrite.v` | `read_spec`, `write_spec` |
| `Sys/Mmap` | `Sys/Mm/Mmap.v` | `brk_spec`, `mmap_spec`, `munmap_spec`, budget refusal |
| `Sys/MmExt` | `Sys/Mm/{Mremap,Mprotect,Madvise}.v`, `Sys/Mm/Mmap.v:420-1230` (lemmas), `State.v:4282-4901` (lemmas) | `mremap_spec`, `mprotect_spec`, `madvise_spec` and their budget marks, the protected-ledger lemmas, the x86-64 `munmap` bound, the memory-management arms |
| `Sys/MmRunX86` | `Run.v:1358-1460` | the alloc-family rows of `injected_table`, `refusal_b` and `alloc_budget_refused_b` at x86-64 numbers |
| `Sys/Kernel` | `Sys/Kernel/{Exit,Fork,Sys}.v`, `Sys/Fs/Open.v`, `Sys/Drivers/Char/Random.v` | `exit`, `wait4`, `set_tid_address`/`getpid`/`gettid`, `get*id`, `close`, `getrandom` |
| `Sys/Time` | `Sys/Kernel/Time/{Time,Hrtimer,PosixTimers}.v` | `gettimeofday`, `nanosleep`, `clock_gettime`, with the x86-64 `gettimeofday` |
| `Sys/KernelSys` | `Sys/Kernel/{Sys,Groups}.v`, `Sys/Kernel/Sched/Syscalls.v`, `Sys/Drivers/Char/Random.v` | `setuid`/`setgid`/`setresuid`/`setresgid`, `setsid`, `uname`, `prctl`, `prlimit64`, `getgroups`/`setgroups`, `sched_*`, the x86-64 forms, and the lane's LPS and x86-64 arm lists |
| `Sys/Fork` | `Sys/Kernel/Fork.v:134-849` | `cloneSpec`, `clone3Spec`, the x86-64 `clone` register order (`cloneRegsX86`), x86-64-only `fork`/`vfork`; `forkLpsArms`, `forkX86Arms`, `exitLpsArms`, `exitX86Arms` |
| `MonadExt` | `Monad.v:285-424` | the remaining `Sys` readers and setters (`set_fds`, `set_pipes`, `set_sigmask`, `set_creds`, `set_clock`, …) and introduction lemmas, shared by the families |
| `ExitBridge` | `Bridge/Exit.v` | the exit bridge: `Clause`, `denote`, `evaluate`, the `exit.hex` reader, `exit_dispatch_*` |
| `Bridge/Exit` | `Bridge/Exit.v` (x86-64 numbers) | `exit_x86_dispatch_*`: the bridge over `exitX86Arms` |
| `Table` | `Sys/Dispatch.v`, `Sys/SyscallTable.v`, `Specs.v` | the 90-arm table (all translated, read off the families' `…LpsArms`) and dispatch |
| `X86FamilyArms` | new | `familyX86Arms`: the families' `…X86Arms` (108 arms at native x86-64 numbers) for the native x86-64 table's ABI gate |
| `NativeX86All` | new | the complete native x86-64 table: all 90 reference slots live with the families' x86-64 arms (`referenceSlot_live`), 20 extensions, `TASK_SIZE_MAX`-band and `sigaltstack` chaos, `exactTable`/`nativeTable` variants |
| `NativeX86Refusal` | `Run.v:1358-1558` at native numbers | `spuriousRefusalCfgX86`, `refusalBX86`, `injectedTableX86`; `MmRunX86` and the two x86-64 `access_ok` spellings proved equal to them |
| `NativeX86AllStatements` | new | x86-64 statement profile over the complete table, `AT_HWCAP` feature profiles, `validEntry_witness` |
| `NativeX86AllLattice` | new | `nativeTable_restricts_exact` (`Lattice.Restricts`) |
| `NativeX86AllControls` | new | per-family positive/negative dispatch through the native table, guard controls, the fixture's inhabited domain |
| `Isa` | `RiscvSemantics.v` (interface), `Run.v:95-197` | `UserIsa`, the ISA parameter; LPS's overlay memory effects |
| `StackLayout` | `StackLayout.v` | argc/argv/envp/auxv/AT_RANDOM block |
| `Run` | `Run.v` | steps, star, traces, errors, behaviours, `SpuriousCfg`, injected failures, budgets, valid entries and inputs |
| `Equivalence` | `Equivalence.v`, `MustExit.v`, `HaltsAllowed.v` | the statement definitions (`strong_universal_*`), budgets, `image_wf`, must-exit, halts-allowed |
| `Classifier` | `FinInput.v`, `Classifier.v`, `Measure.v` | finite inputs, classifiers, weights |
| `Shapes` | `oss-verify-proofs/theories/Shapes.v` | OSS Verify's shapes, each `rfl`-equal to its LPS definition |
| `OmniRun` | `OmniRun.v` | omni-big-step judgments `Exec`, `Coexec`, `Cosafe` over `SStep`, and their equivalence with each field of a run |
| `GatedSize` | `EquivalenceDefinition/GatedSize.v` | gated partitions of the finite inputs, per-slice obligations, predicate-indexed weight bounds |
| `MeasureLib` | `EquivalenceDefinition/MeasureLib.v` (core) | core distributions, finite support, scaling and mixtures; the countable-sum (`tsum`) reading of the weight bounds |
| `ShapesChecks` | new (after `Checks/GatedSize.v`) | positive and negative controls of the classifier and weight shapes on a one-instruction machine |
| `Machines/RiscV`, `Machines/X86`, `Machines/ProcessMemory` | new | Silmaril's `RiscV.Ext` and `X86.Ext` as `UserIsa`s |
| `Machines/RiscVLPS` | `RiscvSemantics.v`, `Run.v:92,175,191,1058`, `Equivalence.v:436` | `riscvLps`: LPS's own RV64GC machine (`Silmaril.RiscV.LPS`) as a `UserIsa` |
| `Machines/RiscVLPSAgree`, `Machines/RiscVLPSChecks` | `Checks/Riscv*.v` | `riscvLps` against `riscvExt`; the six RISC-V checks of LPS against `riscvLps` |
| `Lattice` | new | the lattice of process semantics and the refinement relations |
| `Checks` | new | non-vacuity and translation checks |

## Design

**Parametric in the ISA.** LPS hard-wires its RV64GC machine. The process layer touches the
machine only through: one step reporting accessed ranges, the pending syscall and its six
argument registers, the readable and writable views, effect application, stepping past the
trap and the initial state. `UserIsa` collects these, so `run`, every statement and every
shape takes the ISA as a parameter. Statements take one ISA per build, which also states
**cross-ISA agreement** (`Shapes.agrees isaRv isaX86`), which LPS cannot. Instances:

* `Machines.riscvExt`: Silmaril's RV64IM `RiscV.Ext` machine (ECALL recognised at the pc;
  misaligned accesses and 2-aligned jump targets decline, as hardware with C or emulation
  would run them);
* `Machines.x86Ext`: Silmaril's x86-64 `X86.Ext` machine (`syscall` recognised at RIP; x86-64
  numbers renumbered to asm-generic for the translated, layout-independent arms; RCX/R11
  clobbers; a `syscall` with an undefined status flag declines);
* `Machines.riscvLps`: LPS's own RV64GC machine, the literal translation
  `Silmaril.RiscV.LPS` of `Riscv/*.v` and `RiscvSemantics.v`, with `Overlay.applyEffect` as
  the effect application (see "RISC-V: `riscvLps`" below).

**One step relation, two readings.** LPS writes `sstep` and `sstep_cfg` separately. Here
`SStep segs spec refused` takes the syscall table and the refusal filter as parameters:
`run` is `noFilter`, `run_scfg cfg` is `spuriousRefusalCfg syscallSpec cfg`.

**Coinduction.** Lean has no coinductive types. LPS's `InputStream` is Silmaril's existing
`Process.Syscall.InputStream` (a stable `ℕ → Option Byte`), which is the first point where the
two process models meet; `NetStream` is a stable item sequence, and `NetQueue` an infinite
sequence of connections.

**Images.** Segments hold decoded bytes instead of hex chunks read by the `rocq-read-file`
plugin, so an image can come from Silmaril's Lean ELF reader instead of `elf-snapshot`.

**Faithfulness choices.** Chunked readers (`read_bytes_map`, `readable_bytes`) are translated
as the plain readers LPS proves them equal to; `stream_take_z` as `stream_take`. The `with_*`
setters are structure updates; `set_x v` is `Sys.modify (·.withX v)`. The `valid_input*`
family is generated from one `ValidInputWith` reading; the `strong_universal_*` family from
`Universal`/`UniversalBudgets` and three conclusions. Errno and `AT_*` constants are cited as
blocks.

## The failure model

LPS answers a syscall in three ways: a determined errno; an environment-injected failure
"refused without cause" (`alt (errno_from L) …` beside the determined answer: `ENOMEM`,
`EINTR`, `EMFILE`, …); or `unmodeled` (fail closed, which the run turns into the error
transition). The six `SpuriousFamily`s say which injected failures a statement admits:
`may_fail_cfg` (all), `alloc_only_cfg false` (allocation only when forced) and
`forced_only_cfg` (none). The filter `spuriousRefusalCfg` removes a refusal only where the
specification also admits a non-refusal. `injected_table` is translated in full, including
the errno lists of arms not yet translated.

## Memory budgets

Every backed byte is charged against `VmMaps.limit`: 16 GiB for a source, 512 GiB for a
target (`shippedBudgets`), or 2 GiB for an ASan plain build (`sanitizerBudgets`).
`MAP_NORESERVE` mappings are lazy and are charged on first touch by `accountStep`. The
`*_budgets` statements exclude inputs on which the source reaches a refusal for budget
(`BudgetRefusedAt`). `X86.Ext` does not report accessed ranges, so under `x86Ext` the run
declines while lazy reservations exist (`UserIsa.reportsAccesses`).

The opt-in native x86 integration is described in [LPSX86Parity.md](LPSX86Parity.md).
`x86ExtNative` and `x86Wire` report consumed instruction fetches and successful
data accesses to the same LPS materializer; the legacy `x86Ext` is unchanged.
Native table/refusal/allocation-budget adapters and the separate static SysV
launch must be selected together. The syscall-family workflow still needs to
migrate the identified user-buffer guards to `Model.addressSpace` before
claiming native address-bound parity.

## The syscall table

All 90 LPS arms are in the table with their numbers, and none is a `pendingArm`
placeholder (`translatedArms_length`; this count holds by construction of `arm`, so the
evidence of translation is the per-arm specifications and checks, not the count). Each
family exports its arms as a `…LpsArms` list;
`familySpecTable` reads them off in `Sys/SyscallTable.v` order, `specTable` spells the same
arms out line by line as `Sys/SyscallTable.v` does, and `specTable_eq_familySpecTable` proves
them equal by `rfl`. `specTable_eq_syscallTable` checks the numbers and names against a
literal copy of `Sys/SyscallTable.v`. The status `pending` (an `unmodeled` arm, on which the
model fails closed) is kept for tables under construction; no row of `specTable` has it.
`allocBudgetRefusedB` is LPS's `alloc_budget_refused_b` in full: it reads the budget marks of
`brk`, `mremap`, `mmap` and `mprotect`.

### Memory management (`Sys/Mmap`, `Sys/MmExt`)

`Sys/MmExt` translates `mremap` (216), `mprotect` (226) and `madvise` (233) with every mode
LPS has: `mremap`'s `MREMAP_MAYMOVE` equal-size no-op, shrink, and grow in place or by moving
(an `alt`, the destination a free choice), with the injected `ENOMEM` on resizing calls only;
`mprotect`'s four argument gates in the kernel's order and its rw exposure (budget-gated,
injected `ENOMEM`) and rw no-op; `madvise(MADV_DONTNEED)`, which gives back first-touch
charges and has no injected failure. It exports `mmLpsArms` (asm-generic numbers) and
`mmX86Arms` (x86-64 numbers 9, 10, 11, 12, 25, 28). The three new specifications read no
ISA constant and are the x86-64 arms unchanged. `munmap` reads `TASK_SIZE`: `munmapSpecWith`
takes it as a parameter, `munmapSpec` is the Sv48 instance and `munmapSpecX86` the x86-64
one (`TASK_SIZE_MAX = 2^47 - 4096`, `taskSizeMaxX86`). `Checks/MmExt` has positive, refusal,
injected-failure, forced and decline instances of each arm.

`Run.lean`'s refusal and budget dispatch (`refusalB`, `injectedTable`, `allocBudgetRefusedB`)
is keyed on the asm-generic numbers 214/216/222/226, which are not memory-management calls
on x86-64. `Sys/MmRunX86` gives the x86-64 counterparts keyed on `brk` 12, `mremap` 25,
`mmap` 9 and `mprotect` 10 (`allocBudgetRefusedBX86`, `mmInjectedTableX86`, `mmRefusalBX86`),
each proved equal to the LPS dispatcher under the renumbering `mmSysnoX86ToLps`. Joining them
with the other families' x86-64 rows, and threading them through `BudgetRefusedAt` and
`spuriousRefusalCfg` for an x86-64 run, is left to the integration step.

### Shared user-ABI layer (`Uapi`, `Uaccess`, `StateHelpers`)

Syscall-family modules reuse these instead of translating them again. Each definition cites
its LPS file and line.

* `Uapi` (`Sys/Uapi.v`): every constant of `Sys/Uapi.v` not already in `Basic` (`PROT_*`,
  `MAP_*`, `GRND_*`), `Sys/Kernel` (`WNOHANG`) or `Run` (`sigKernelOnlyMask`): `O_*`, `AT_*`,
  `dotPath`/`devnullPath`/`urandomPath`, `AF_*`/`SOCK_*`/`IPPROTO_*`/`SOL_SOCKET`/`SHUT_*`,
  `SEEK_*`, `PROT_GROWS*`, `MREMAP_MAYMOVE`, `MADV_DONTNEED`, the `TC*`/`TIOC*` ioctls,
  `F_GETFD`…`F_SETFL`, `LOCK_*`, `CLOCK_*`, `TFD_CREATE_FLAGS`, `EFD_*`, `KTIME_*`, the
  timespec decoders (`tvSecOf`, `timespecNs`, `timespecKtime`, `timespecNsSigned`),
  `SIG_*`/`SS_*`/`MINSIGSTKSZ`/`SIGABRT`, `NR_OPEN_DEFAULT`, `NGROUPS_MAX`, `SCHED_*`,
  `CLONE_VM`, `FUTEX_*`, `NEW_UTS*`, `PR_CAPBSET_READ`, `CAP_LAST_CAP`, and the `struct stat`
  predicates (`statFieldLe`, `statIfmt`, `statBufWf`, `statSizeOk`, `statChrdevOk`,
  `statDevnullOk`, `statUrandomOk`, `statStableEqb`, `statSetSize`). `zlor`/`zland` are
  `Z.lor`/`Z.land` on non-negative integers. It also carries `utsMachineChars`
  (`Sys/Kernel/Sys.v:926`), `epollEventBytes`/`EP_MAX_EVENTS` (`Sys/Fs/EventPoll.v:203`)
  and `kernelSigactionBytes` (`Sys/Kernel/Signal.v:290`), so that each has its x86-64
  variant next to it.
* `Uaccess` (`Sys/Uaccess.v`, `State.v:1024-1760`, `Sys/Syscall.v`): the lemmas that
  discharge the user-buffer gates of `Syscall` (`accessOkb_intro`, `accessOkb_le`,
  `rwRange_in_range`, `rwRange_of_accessOk`, `writeSource_small`, …); pathnames
  (`pathMax`, `CstrResult`, `readCstr`, `cstrAccessLenAux`); `copyBytesMap`; `iovec` arrays
  (`IovEntry`, `IovImport`, `readIovecEntry`, `copyIovecsAux`, `copyIovecsAccesses`,
  `importIovecs`, `importIovecsAccesses`, `capIovecs`, `iovPrefixAccesses`, `scatterIovecs`,
  `gatherIovecs`, `gatherPrefix`, `iovsTotal`, `writevGathered`, `readIovecs`, `IOV_MAX`);
  the narrowings `whence32`, `cmd32`, `clockid32`, `uid32`, `flag32`, `nfds32`, `unfds32`,
  `nfdsSigned`, `sint32`, `how32`, `pipeFlags32`; and `outcomeCopyins`.
  `importIovecsWith`/`importIovecsAccessesWith`/`iovsAccessOkbWith` take the `access_ok`
  predicate as a parameter.
* `StateHelpers` (`State.v`): `Model.connIx`, `.setsidSucceeded`, `.sigaltstackInstalled`,
  `.sigmask`, `.utsname`, `.statpins`, `.rlimitCore`, `.nofile`, `.clock`; the setters
  `withRlimitCore`, `withUtsname`, `withStatpin`, `withSetsidSucceeded`,
  `withSigaltstackInstalled`, `withSigabrtPending`, `withAccepted`; `statpinLookup`;
  `allocFd2`, `pipeNewId`, `le32Bytes`, `pipeFdBytes`; `mkVmMaps`, `vmLiveBytes`, `pageBase`,
  `accessPages`, `vmBackedBytes`, `pageInHalfOpen`, `movePageBase`, `vmResizeBacking`;
  `mkProcInput`.

The audit of `State.lean` against `State.v` found every record and inductive translated
with all its fields and constructors; `cstr_result`, `iov_import` and `iov_entry` are
`CstrResult`, `IovImport` and `IovEntry` in `Uaccess`. Not translated: the chunked readers
(`read_bytes_chunks`, …) and `stream_take_pos`/`net_take_pos`, which are extraction-speed
devices that LPS proves equal to the plain functions.

#### x86-64 variants

LPS takes every uapi header from `asm-generic` (riscv64). x86-64 does too for `fcntl.h`,
`ioctls.h`, `socket.h`, `resource.h`, `errno.h`, `poll.h`, `termbits.h` and `termios.h`, so
those constants are shared. The differences, each with its own definition:

| what | LPS (riscv64) | x86-64 | Lean |
| --- | --- | --- | --- |
| `struct stat` | 128 bytes, `st_mode` at 16, `st_rdev` at 32, padding at 40, 60, 120 | 144 bytes, `st_nlink` (8) at 16, `st_mode` at 24, `__pad0` at 36, `st_rdev` at 40, `__unused[3]` at 120 (`arch/x86/include/uapi/asm/stat.h`) | `StatLayout`, `statLayoutLps`, `statLayoutX86`, `statBufWfX86`, `statSizeOkX86`, `statDevnullOkX86`, `statUrandomOkX86`, `statStableEqbX86`, `statSetSizeX86` |
| `struct epoll_event` | 16 bytes, `data` at 8 | packed, 12 bytes, `data` at 4 (`EPOLL_PACKED`) | `epollEventBytesX86`, `epollEventDataOffX86`, `EP_MAX_EVENTS_X86` |
| kernel `struct sigaction` | 24 bytes, no `sa_restorer` | 32 bytes, `sa_restorer` at 16, `sa_mask` at 24; `SA_RESTORER = 0x04000000` | `kernelSigactionBytesX86`, `SA_RESTORER_OFF_X86`, `SA_MASK_OFF_X86`, `SA_RESTORER_X86` |
| `UTS_MACHINE` | `"riscv64"` | `"x86_64"` | `utsMachineCharsX86` |
| `mmap` flags | — | `MAP_32BIT = 0x40`, `MAP_ABOVE4G = 0x80` | `MAP_32BIT_X86`, `MAP_ABOVE4G_X86` |
| `arch_prctl` | — | `ARCH_SET_GS`/`SET_FS`/`GET_FS`/`GET_GS` | `ARCH_SET_FS_X86`, … |
| `access_ok` | `base + len ≤ 2^47` (Sv48 `TASK_SIZE`) | `base + len ≤ TASK_SIZE_MAX = 2^47 - 4096`, no wrap (`arch/x86/include/asm/uaccess_64.h`) | `accessOkbX86`, `accessOkZeroX86`, `copyBytesMapX86`, `importIovecsX86`, `importIovecsAccessesX86`, `taskSizeMaxX86`, `accessOkbX86_iff` |

The legacy `clone` register order differs: riscv64 selects `CONFIG_CLONE_BACKWARDS`
(`flags, newsp, parent_tid, tls, child_tid`), x86-64 selects none of `CLONE_BACKWARDS*`
(`flags, newsp, parent_tid, child_tid, tls`); `Sys/Fork` decodes both (`cloneRegsBackwards`,
`cloneRegsX86`). Checked and the same on x86-64: `stack_t`, `sigset_t`, `MINSIGSTKSZ`, the signal numbers,
`struct new_utsname`, `struct iovec`, `struct timespec`, `struct sockaddr_in`,
`struct rlimit64`. `Checks/UserAbi.lean` has positive and refusal instances of these
helpers, including a range LPS accepts and x86-64 refuses, and each `struct stat` layout
refusing the other's buffer.


## The model lattice and the refinement relations (`Lattice.lean`)

`processSyntax` has images as programs and `(entry, input, observation)` as observations, an
observation being a trace prefix, reaching an error, or reaching an unmodelled step.
`procSem isa spec refused lim` is a point of the csem lattice (`Compile.Category.Lattice`).

| relation | statement | status |
| --- | --- | --- |
| reading ⊑ may-fail reading | `scfg_le_run` (LPS: `run_scfg ⊆ run`) | proved |
| readings monotone in `cfgLe` | `scfg_mono` | proved |
| stronger filter, fewer behaviours | `procSem_filter_mono` | proved |
| partial table restricts any completion | `restricts_of_completes` | proved |
| partial table: fewer traces | `obsTrace_mono` | proved |
| error-free partial table: same traces, completion error free | `obsTrace_eq_of_errorFree`, `errorFree_of_restricts` | proved |
| budget refusal monotone | `budgetRefused_mono` | proved |
| **`agrees` transfers from this translation to the full LPS table** | `agrees_transfer` | proved |
| LPS ⊑ Silmaril byte-stream contract on read/write/exit programs | `LPSRefinesContractOn` | stated |
| Silmaril RV64 vs LPS RV64GC (`riscvExt` vs `riscvLps`), under one process layer | `IsaRefinesOn`; step-level agreement in `Machines/RiscVLPSAgree` | stated; step agreement proved for non-memory instructions, `ecall`, `ebreak` given the same fetched word |

Silmaril's `Process.Syscall` contract (the read/write/exit model under `RiscV/Linux/**`) and
LPS differ: the contract admits any errno on read and write, a read error may consume input
unobservably and clobber the buffer, and fds are abstract; LPS admits only Linux's errnos
plus the injected ones, models 90 calls, and observes the file system at exit. Both are put in
the lattice over the same syntax: the contract is the table `contractSpec`, and the CLI
observation map `cliView`/`cliOfSyscallEvent` relates their event alphabets.
`LPSRefinesContractOn isa F` is the refinement relation between the two models.

The CLI model of branch `process/cli-model` had no commits beyond `main` when this was
written; `CliEvent` is the observation alphabet proposed for it.

## Checks (`Checks.lean`)

* `validInput_inhabited`: the valid-input premise of the shapes is satisfiable;
* `auxvBytes_length`, `atRandomBytes_length`: the auxv is LPS's 160 bytes;
* `x86_read`, `x86_write`, `x86_exit_group`, `x86_open_declines`: renumbering;
* `translatedArms_eq`, `specTable_length`, `modeledSysnos_nodup`, `specTable_eq_syscallTable`,
  `specTable_eq_familySpecTable`, `translatedArms_length`: the table;
* the `*_is_lps` lemmas of `Shapes.lean` (all `rfl`), and the monotonicity and classifier
  lemmas of `Shapes.v`.

## Not translated (yet)

* The coinductive/observable-equivalence portions of `OmniRun.v`, `GatedSize.v`,
  `MeasureLib.v`, `PatchClassifySpec.v`, `OmniEquivalence.v`,
  most of `Classifier.v` (the patch-diff and plain variants), and the `Checks/` QA layer;

The additive `RunHelpers` now supplies the finite/terminating core of `OmniRun`
and `imageBrkSatisfiable_entry`. The original
`Shapes.disagreesAtMost_of_classifier` retains its explicit entry hypothesis for
compatibility; `ShapesParity.disagreesAtMost_of_classifier_imageWf` supplies the
pinned image-well-formedness route without that extra assumption. See
[the audit](LPSShapesParity.md).

## RISC-V: `riscvLps` and the remaining caveats

The consolidated claim against theorem.dev, with every caveat classified, is in
[AtLeastAsGoodAsTheoremDev.md](AtLeastAsGoodAsTheoremDev.md).

`Machines.riscvLps` (`Machines/RiscVLPS.lean`) runs `Silmaril.RiscV.LPS`, the hand
translation of LPS's RV64GC ISA (`Riscv/*.v`) and user-mode machine (`RiscvSemantics.v`,
see [`RiscVLPS.md`](RiscVLPS.md)), under this process layer. Each `UserIsa` field is the LPS
definition the process layer calls: `step_accesses` (`RiscvSemantics.v:1042`, with its
access reports, so `reportsAccesses = true`), `ms_svc_pending`, `syscall_args` (`Run.v:92`),
`ms_read_byte` and `ms_writable_byte` (`RiscvSemantics.v:217,542`), `apply_effect`
(`Run.v:175`: `set_reg` a0, then `Overlay.applyEffect`), `advance_past_svc` (`Run.v:191`),
`init_machine_state` (`Run.v:1058`: sp and a0 in the register map, the entry block over the
zeroed `stack_max_size` bytes in the overlay, the readable segments as `ms_rom`) and
`image_entry_fetchable` (`Equivalence.v:436`). Compressed fetch (`fetch_tail_any`), IALIGN =
16, w+x fetch through the overlay, misaligned plain accesses performed, misaligned LR/SC/AMO
faulting before the reservation check, the defined-illegal split and the fail-closed
classification of failed fetches are therefore LPS's.

`Machines/RiscVLPSChecks.lean` ports `Checks/RiscvAccessReporting.v`, `RiscvAlignment.v`,
`RiscvAtomicAlignment.v`, `RiscvCompressedFetch.v`, `RiscvDefinedIllegal.v` and
`RiscvSegmentChunks.v` as kernel `decide` checks about `riscvLps.step` (and
`riscvLps.entryFetchable`, `readByte`, `applyEffect`, `advancePastSvc`, `init`), with the
fixtures written as process-layer segments with upstream's `"rwx"` letters. The two checks
about hex text are compiled `#guard`s on `hexChunksDecode`.

### Remaining caveats of statements written with `riscvLps`

1. **Segment bytes, not hex chunks.** LPS's segments carry lowercase hex chunks read by the
   `rocq-read-file` plugin. The ISA port's segment (`RiscV.LPS.Segment`) now holds one
   `Option Byte` per byte, so a hole is expressible: `Segment.ofHex` decodes upstream's
   chunks byte by byte, and `segmentByteAt_ofHex` proves that every byte inside the segment
   reads exactly as upstream's `segment_byte_at` reads the chunks (a bad digit pair is a
   hole at exactly that byte; later bytes stay readable, and the fetch paths and
   `fetchFailure` then decline exactly where upstream's do). Before this change `ofHex`
   truncated at the first bad digit, so a load of a later byte faulted where upstream
   succeeds. The process layer's segment (`MemImage.lean`) holds a `List Byte`, which has
   no holes by construction; `lpsSegment` maps it with `Segment.bytesData`
   (`segmentByteAt_bytesData`: byte `i` reads as `bytes[i]?`). Images built by Silmaril's
   Lean ELF reader are therefore hole-free, and an upstream hex image with a bad digit has
   no process-layer form (statements cannot be made about it, which is safe). Such an
   image enters only through `RiscV.LPS.Segment.ofHex`, holes included. The image is not
   checked against `elf-snapshot`'s output.
2. **Floating point: a lattice of FPU variants, not one kernel.** `Fpu.v` is translated
   with Lean core's `Float.Model` plus `chooseMantissa`/`overflowResult` in place of
   SpecFloat/Flocq (LGPL, not copied), and upstream's `round_aux_value` has no direct
   counterpart. Instead the semantics is stated over a pluggable FPU
   (`RiscV.LPS.FpuOps`, `execWith`, `stepAccessesWith`; `stepAccessesWith_lps` proves the
   literal machine is the `lps` instance), with four variants ordered by refinement
   (`RiscV.LPS.FpuLattice`, `Machines/RiscVLPSFpu.lean`):
   * `lps`: the literal LPS kernel (`riscvLpsWith .lps = riscvLps`);
   * `ieee`: the same operations over Silmaril's own IEEE 754 model
     (`Numeric.Ieee754.Rounding` values, `Numeric.Ieee754.Flags` exception
     specification computed from the exact result over `ℚ`, `Numeric.Float.Profile.riscvFD`
     for the RISC-V choices), giving `riscvLpsIeee`;
   * `agreed`: answers a request only where `lps` and `ieee` compute the same bits and
     flags, unmodeled otherwise, giving `riscvLpsAgreed`; sound with no theorem about
     either kernel, and refined by both (`riscvLpsAgreed_step`: on every step it models,
     `riscvLps` and `riscvLpsIeee` take that same step);
   * `chaos`: every FP request unmodeled.

   Proved for every operand of the format's width and every rounding mode:
   * `RiscV.LPS.FpuAgree`: the rounding-mode decoding (`rm`, `frm`), the rounding choice
     (`chooseMantissa = roundMantissa`) and the overflow direction; decoding
     (`fpDecode = Bits.value`, NaN and signalling-NaN tests); `fclass`; `feq`/`flt`/`fle`
     with their flags; and `fmin`/`fmax` with their flags (IEEE 754-2019
     `minimumNumber`/`maximumNumber`, RISC-V F 2.2).
   * `RiscV.LPS.FpuAgreeRound`: the result bits of every rounded operation (add, sub, mul,
     div, sqrt, fma, `fcvt` between formats, integer to float, saturating float to
     integer).
   * `RiscV.LPS.FpuAgreeFlags`: their `fflags`, with tininess after rounding. Two
     operations carry a side condition:
     * sqrt needs a square root that is not tiny, which holds for every binary32 and
       binary64 operand;
     * div needs an exact quotient that is zero or at least `2 ^ emin` in magnitude.
   * `RiscV.LPS.FpuAgreeAll`: combined over requests, `FpuImpl.run_lps_eq_ieee` gives the
     same bits and flags on every covered request. Hence `agreed` answers each of those
     requests exactly as `lps` does (`FpuOps.agreed_of_covered`).

   * `RiscV.LPS.FpuCoverage`: every request the machine issues (operands read by `fread`,
     binary32/binary64 only, 32/64-bit integers) is covered unless it is a division with
     a nonzero exact quotient below `2 ^ emin` (`execWith_eq_lps_of`). So `agreed`
     executes every other instruction exactly as `exec` (`execWith_agreed_of_not_divWindow`,
     `stepAccessesWith_agreed_eq`).
   * `Machines/RiscVLPSFpuRun.lean`: the refinement lifted from steps to runs
     (`runWith_behaviorEquiv_of_modeled`). If the coarse machine's run never reaches an
     unmodeled configuration, every refinement has the same behaviour (LPS
     `behavior_equiv`). In particular every modeled run of `riscvLpsAgreed` has the behaviour
     of `riscvLps` and of `riscvLpsIeee`.

   In the division window the kernels really disagree (`RiscV.LPS.FpuFindings`, kernel
   `decide`):
   * LPS's `round_tiny` rounds the subnormal `divCore` quotient on its own coarse grid.
   * As a result LPS can miss UF. Example: `fdiv.s` RUP `0x013FFFFF / 3.0` gives NX in
     LPS and NX|UF in IEEE 754 and SoftFloat-RISCV.
   * Upstream `Fpu.v` has the same shape, so the defect is LPS's, not the translation's.
     Executed under Rocq 9.2, upstream `fp_div` returns the same bits with NX only on
     all three finding inputs (`scripts/riscv/lps-fpu-div-underflow.v`). SoftFloat's run
     is recorded in `scripts/riscv/softfloat-div-underflow.c`.
   * `agreed` declines those requests, and `ieee` is the variant that matches RISC-V.

   Tested (`RiscV.LPS.FpuTestFloatChecks`, compiled `#guard`s):
   * Both kernels reproduce all 19456 sampled Berkeley TestFloat 3e vectors generated with
     SoftFloat's RISC-V specialization: bits and all five flags, both formats, all five
     modes, every arithmetic and conversion operation.
   * The two kernels agree on all 71688 special-value requests, including
     `fmin`/`fmax`, `fclass` and comparisons.
   * The sampled vectors do not reach the UF window above.
   * The 83 `FpuTests.v` checks still pass by kernel `decide`.
3. **Translation fidelity is checked by upstream's own checks, not by a Rocq build.** Rocq
   was not run; the definition-by-definition table is
   [`RiscVLPS-correspondence.tsv`](RiscVLPS-correspondence.tsv) (14 entries not ported, each
   with its reason: structure updaters, syscall-layer helpers, unused hex readers, the Flocq
   lemma). The comparison with the machine translation (`tools/rocq2lean`) is open.
4. **The process layer's own gaps apply unchanged** (see "Known precision gaps" below).

There is no other ISA caveat: no RISC-V behaviour of `riscvLps` differs from LPS's
`RiscvSemantics.v` by design.

### `riscvLps` against `riscvExt` (`Machines/RiscVLPSAgree.lean`)

`RvAgree` relates the two states (same pc, integer registers and pending syscall). Proved:
the pending syscall and the six argument registers agree (`svcPending_agree`,
`syscallArgs_agree`); `init`, `advancePastSvc` and the register part of `applyEffect`
preserve agreement (`init_agree`, `advancePastSvc_agree`, `applyEffect_agree`); given the
same fetched word, a non-memory RV64IM instruction `riscvExt` retires is retired by
`riscvLps` to an agreeing state with no access and the overlay unchanged
(`step_agree_retire`), `ecall` sets the same pending syscall (`step_agree_ecall`), and
`ebreak` faults in both (`step_agree_ebreak`); where Ext traps on a misaligned plain access
or a jump target ≡ 2 (mod 4), `riscvExt` declines (`step_unmodeled_misaligned_data`,
`step_unmodeled_jump_target`).

Where they differ or are not related:

* **Memory is not related, and parity does not need it.** theorem.dev's RISC-V statements
  quantify over runs of LPS's own machine (`RiscvSemantics.v` under `Run.v`); `riscvLps`
  is that machine, field by field, with its own overlay-over-image memory
  (`ms_read_byte`, `ms_writable_byte`, `apply_effect`). A statement written with
  `riscvLps` is therefore the upstream statement, and needs no relation to `riscvExt` or to
  `Process.Memory`. `riscvExt` is a second, Silmaril-native RISC-V model; relating the two
  would let one statement transfer to the other model, which is stronger than parity and
  is not claimed. (For byte loads there is a partial relation already,
  `RiscV.OSSVerify.MemoryRelation`.)
  No simulation between `Process.Memory` and LPS's overlay over
  the image is proved, so the fetch agreement is a hypothesis of the step theorems and loads
  and stores are not covered. Known differences: after `munmap` of part of a loaded segment
  LPS still fetches an `r-x` segment's static bytes and still reads a readable segment
  (`apply_unmaps` only clears the overlay), while `Process.Memory` removes the region; LPS
  wraps byte addresses modulo `2^64`, Ext requires the span to end below `2^64`.
* misaligned plain loads/stores: LPS performs them, `riscvExt` declines;
* jump targets ≡ 2 (mod 4): LPS retires, `riscvExt` declines;
* fetch at pc ≡ 2 (mod 4): LPS fetches, `riscvExt` faults; reachable for `riscvExt` only
  at the entry point, which its `entryFetchable` rejects;
* words Ext does not decode (C, A, F, D, Zicsr, FENCE, FENCE.I): LPS executes, faults
  (all-zero parcel, writes to read-only CSRs, misaligned atomics) or declines; `riscvExt`
  declines;
* LPS's FP registers, `fcsr` and reservation have no Ext counterpart.

## Known precision gaps added by the instances

* x86-64 `TASK_SIZE` is `0x7ffffffff000`, one page below LPS's Sv48 bound;
* `AT_HWCAP` and `valid_hwcap` are riscv64's; the x86-64 auxiliary vector is LPS's ten entries.

## Correspondence table

Generated from the docstrings (`scripts` in `/srv/scratch/campaigns/research/rocq-to-lean/`).

### Syscall arms

One row per line of `Sys/SyscallTable.v`: the specification and the module that defines it,
the family list that exports the arm, and the native x86-64 number(s) of the same call in
`familyX86Arms` (whether the native table enables it is decided by its ABI-review gate in
`NativeX86`).

| no. | call | specification (module) | arm list | x86-64 no. |
| ---: | --- | --- | --- | ---: |
| 17 | `getcwd` | `getcwdSpec` (`Sys/FsMeta/DPath`) | `fsMetaLpsArms` | 79 |
| 19 | `eventfd2` | `eventfd2Spec` (`Sys/FdEvents/EventFd`) | `fdEventsLpsArms` | 290 |
| 20 | `epoll_create1` | `epollCreate1Spec` (`Sys/FdEvents/EventPoll`) | `fdEventsLpsArms` | 291 |
| 21 | `epoll_ctl` | `epollCtlSpec` (`Sys/FdEvents/EventPoll`) | `fdEventsLpsArms` | 233 |
| 22 | `epoll_pwait` | `epollPwaitSpec` (`Sys/FdEvents/EventPoll`) | `fdEventsLpsArms` | 281 |
| 23 | `dup` | `dupSpec` (`Sys/FsIo/File`) | `fsIoLpsArms` | 32 |
| 24 | `dup3` | `dup3Spec` (`Sys/FsIo/File`) | `fsIoLpsArms` | 292 |
| 25 | `fcntl` | `fcntlSpec` (`Sys/FsCtl`) | `fsCtlLpsArms` | 72 |
| 29 | `ioctl` | `ioctlSpec` (`Sys/FsCtl`) | `fsCtlLpsArms` | 16 |
| 32 | `flock` | `flockSpec` (`Sys/FsCtl`) | `fsCtlLpsArms` | 73 |
| 35 | `unlinkat` | `unlinkatSpec` (`Sys/FsMeta/Namei`) | `fsMetaLpsArms` | 263 |
| 46 | `ftruncate` | `ftruncateSpec` (`Sys/FsIo/Open`) | `fsIoLpsArms` | 77 |
| 48 | `faccessat` | `faccessatSpec` (`Sys/FsIo/Open`) | `fsIoLpsArms` | 269 |
| 56 | `openat` | `openatSpec` (`Sys/FsIo/Open`) | `fsIoLpsArms` | 257 |
| 57 | `close` | `closeSpec` (`Sys/Kernel`) | `fsIoLpsArms` | 3 |
| 59 | `pipe2` | `pipe2Spec` (`Sys/FdEvents/Pipe`) | `fdEventsLpsArms` | 293 |
| 61 | `getdents64` | `getdents64Spec` (`Sys/FsMeta/Readdir`) | `fsMetaLpsArms` | 217 |
| 62 | `lseek` | `lseekSpec` (`Sys/FsIo/ReadWrite`) | `fsIoLpsArms` | 8 |
| 63 | `read` | `readSpec` (`Sys/ReadWrite`) | `fsIoLpsArms` | 0 |
| 64 | `write` | `writeSpec` (`Sys/ReadWrite`) | `fsIoLpsArms` | 1 |
| 65 | `readv` | `readvSpec` (`Sys/FsIo/ReadWrite`) | `fsIoLpsArms` | 19 |
| 66 | `writev` | `writevSpec` (`Sys/FsIo/ReadWrite`) | `fsIoLpsArms` | 20 |
| 67 | `pread64` | `pread64Spec` (`Sys/FsIo/ReadWrite`) | `fsIoLpsArms` | 17 |
| 68 | `pwrite64` | `pwrite64Spec` (`Sys/FsIo/ReadWrite`) | `fsIoLpsArms` | 18 |
| 72 | `pselect6` | `pselect6Spec` (`Sys/FdEvents/Select`) | `fdEventsLpsArms` | 270 |
| 73 | `ppoll` | `ppollSpec` (`Sys/FdEvents/Select`) | `fdEventsLpsArms` | 271 |
| 78 | `readlinkat` | `readlinkatSpec` (`Sys/FsMeta/Stat`) | `fsMetaLpsArms` | 267 |
| 79 | `newfstatat` | `newfstatatSpec` (`Sys/FsMeta/Stat`) | `fsMetaLpsArms` | 262 |
| 80 | `fstat` | `fstatSpec` (`Sys/FsMeta/Stat`) | `fsMetaLpsArms` | 5 |
| 82 | `fsync` | `fsyncSpec` (`Sys/FsCtl`) | `fsCtlLpsArms` | 74 |
| 83 | `fdatasync` | `fsyncSpec` (`Sys/FsCtl`) | `fsCtlLpsArms` | 75 |
| 85 | `timerfd_create` | `timerfdCreateSpec` (`Sys/FdEvents/Timerfd`) | `fdEventsLpsArms` | 283 |
| 93 | `exit` | `exitSpec` (`Sys/Kernel`) | `exitLpsArms` | 60 |
| 94 | `exit_group` | `exitSpec` (`Sys/Kernel`) | `exitLpsArms` | 231 |
| 96 | `set_tid_address` | `setTidAddressSpec` (`Sys/Kernel`) | `forkLpsArms` | 218 |
| 98 | `futex` | `futexSpec` (`Sys/Futex`) | `futexLpsArms` | 202 |
| 101 | `nanosleep` | `nanosleepSpec` (`Sys/Time`) | `kernelSysLpsArms` | 35 |
| 113 | `clock_gettime` | `clockGettimeSpec` (`Sys/Time`) | `kernelSysLpsArms` | 228 |
| 119 | `sched_setscheduler` | `schedSetschedulerSpec` (`Sys/KernelSys`) | `kernelSysLpsArms` | 144 |
| 123 | `sched_getaffinity` | `schedGetaffinitySpec` (`Sys/KernelSys`) | `kernelSysLpsArms` | 204 |
| 124 | `sched_yield` | `schedYieldSpec` (`Sys/KernelSys`) | `kernelSysLpsArms` | 24 |
| 130 | `tkill` | `tkillSpec` (`Sys/Signal`) | `signalLpsArms` | 200 |
| 131 | `tgkill` | `tgkillSpec` (`Sys/Signal`) | `signalLpsArms` | 234 |
| 132 | `sigaltstack` | `sigaltstackSpec` (`Sys/Signal`) | `signalLpsArms` | 131 |
| 134 | `rt_sigaction` | `rtSigactionSpec` (`Sys/Signal`) | `signalLpsArms` | 13 |
| 135 | `rt_sigprocmask` | `rtSigprocmaskSpec` (`Sys/Signal`) | `signalLpsArms` | 14 |
| 144 | `setgid` | `setidSpec` (`Sys/KernelSys`) | `kernelSysLpsArms` | 106 |
| 146 | `setuid` | `setidSpec` (`Sys/KernelSys`) | `kernelSysLpsArms` | 105 |
| 147 | `setresuid` | `setresidSpec` (`Sys/KernelSys`) | `kernelSysLpsArms` | 117 |
| 149 | `setresgid` | `setresidSpec` (`Sys/KernelSys`) | `kernelSysLpsArms` | 119 |
| 157 | `setsid` | `setsidSpec` (`Sys/KernelSys`) | `kernelSysLpsArms` | 112 |
| 158 | `getgroups` | `getgroupsSpec` (`Sys/KernelSys`) | `kernelSysLpsArms` | 115 |
| 159 | `setgroups` | `setgroupsSpec` (`Sys/KernelSys`) | `kernelSysLpsArms` | 116 |
| 160 | `uname` | `unameSpec` (`Sys/KernelSys`) | `kernelSysLpsArms` | 63 |
| 167 | `prctl` | `prctlSpec` (`Sys/KernelSys`) | `kernelSysLpsArms` | 157 |
| 169 | `gettimeofday` | `gettimeofdaySpec` (`Sys/Time`) | `kernelSysLpsArms` | 96 |
| 172 | `getpid` | `getpidSpec` (`Sys/Kernel`) | `kernelLpsArms` | 39 |
| 174 | `getuid` | `getidSpec` (`Sys/Kernel`) | `kernelLpsArms` | 102 |
| 175 | `geteuid` | `getidSpec` (`Sys/Kernel`) | `kernelLpsArms` | 107 |
| 176 | `getgid` | `getidSpec` (`Sys/Kernel`) | `kernelLpsArms` | 104 |
| 177 | `getegid` | `getidSpec` (`Sys/Kernel`) | `kernelLpsArms` | 108 |
| 178 | `gettid` | `gettidSpec` (`Sys/Kernel`) | `kernelLpsArms` | 186 |
| 198 | `socket` | `socketSpec` (`Sys/SocketCore`) | `socketLpsArms` | 41 |
| 199 | `socketpair` | `socketpairSpec` (`Sys/Socket`) | `socketLpsArms` | 53 |
| 200 | `bind` | `bindSpec` (`Sys/SocketCore`) | `socketLpsArms` | 49 |
| 201 | `listen` | `listenSpec` (`Sys/SocketCore`) | `socketLpsArms` | 50 |
| 202 | `accept` | `accept4Spec` (`Sys/SocketCore`) | `socketLpsArms` | 43 |
| 203 | `connect` | `connectSpec` (`Sys/SocketCore`) | `socketLpsArms` | 42 |
| 204 | `getsockname` | `getsocknameSpec` (`Sys/SocketCore`) | `socketLpsArms` | 51 |
| 205 | `getpeername` | `getpeernameSpec` (`Sys/SocketCore`) | `socketLpsArms` | 52 |
| 206 | `sendto` | `sendtoSpec` (`Sys/Socket`) | `socketLpsArms` | 44 |
| 207 | `recvfrom` | `recvfromSpec` (`Sys/Socket`) | `socketLpsArms` | 45 |
| 208 | `setsockopt` | `setsockoptSpec` (`Sys/SocketCore`) | `socketLpsArms` | 54 |
| 209 | `getsockopt` | `getsockoptSpec` (`Sys/SocketCore`) | `socketLpsArms` | 55 |
| 210 | `shutdown` | `shutdownSpec` (`Sys/SocketCore`) | `socketLpsArms` | 48 |
| 211 | `sendmsg` | `sendmsgSpec` (`Sys/Socket`) | `socketLpsArms` | 46 |
| 212 | `recvmsg` | `recvmsgSpec` (`Sys/Socket`) | `socketLpsArms` | 47 |
| 214 | `brk` | `brkSpec` (`Sys/Mmap`) | `mmLpsArms` | 12 |
| 215 | `munmap` | `munmapSpec` (`Sys/Mmap`) | `mmLpsArms` | 11 |
| 216 | `mremap` | `mremapSpec` (`Sys/MmExt`) | `mmLpsArms` | 25 |
| 220 | `clone` | `cloneSpecRegs` (`Sys/Fork`) | `forkLpsArms` | 56 |
| 222 | `mmap` | `mmapSpec` (`Sys/Mmap`) | `mmLpsArms` | 9 |
| 226 | `mprotect` | `mprotectSpec` (`Sys/MmExt`) | `mmLpsArms` | 10 |
| 233 | `madvise` | `madviseSpec` (`Sys/MmExt`) | `mmLpsArms` | 28 |
| 242 | `accept4` | `accept4Spec` (`Sys/SocketCore`) | `socketLpsArms` | 288 |
| 260 | `wait4` | `wait4Spec` (`Sys/Kernel`) | `exitLpsArms` | 61 |
| 261 | `prlimit64` | `prlimit64Spec` (`Sys/KernelSys`) | `kernelSysLpsArms` | 302 |
| 278 | `getrandom` | `getrandomSpec` (`Sys/Kernel`) | `kernelLpsArms` | 318 |
| 435 | `clone3` | `clone3Spec` (`Sys/Fork`) | `forkLpsArms` | 435 |
| 439 | `faccessat2` | `faccessat2Spec` (`Sys/FsIo/Open`) | `fsIoLpsArms` | 439 |

90 translated, 0 pending, 90 total. The x86-64-only legacy entry points in `familyX86Arms`
(no LPS arm): `open` 2, `stat` 4, `lstat` 6, `poll` 7, `access` 21, `pipe` 22, `select` 23,
`dup2` 33, `fork` 57, `vfork` 58, `getdents` 78, `rmdir` 84, `creat` 85, `unlink` 87,
`readlink` 89, `epoll_create` 213, `epoll_wait` 232, `eventfd` 284.

### Definitions

### `BvBase.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 23 | `byte` | `Byte` | Basic.lean |
| 31 | `len_word` | `lenWord` | Basic.lean |
| 35 | `word_to_nat` | `wordToNat` | Basic.lean |
| 36 | `nat_to_word` | `natToWord` | Basic.lean |
| 43 | `word_to_nat_bounded` | `wordToNatBounded` | Basic.lean |
| 66 | `word_le8` | `wordLe8` | Basic.lean |
| 85 | `bytes_le_to_Z` | `bytesLeToNat`, `bytesLeToZ` | Basic.lean |
| 93 | `le_bytes_to_word` | `leBytesToWord` | Basic.lean |
| 101 | `Z_to_le_bytes` | `zToLeBytes` | Basic.lean |
| 148 | `word_le4` | `wordLe4` | Basic.lean |

### `Classifier.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 249 | `classifier_alloc_limit` | `classifierAllocLimit` | Classifier.lean |
| 665 | `verdict_accept` | `verdictAccept` | Classifier.lean |
| 666 | `verdict_reject` | `verdictReject` | Classifier.lean |
| 1338 | `good_input_s` | `GoodInputS` | Classifier.lean |
| 1418 | `decides_fo` | `DecidesFo` | Classifier.lean |
| 1448 | `classifies_good_inputs_T_s` | `ClassifiesGoodInputsTS` | Classifier.lean |
| 1479 | `decides_fo_hwcap_rv64gc` | `DecidesFoHwcap` | Classifier.lean |
| 1557 | `classifies_patch_diff_T_s_hwcap_rv64gc` | `ClassifiesPatchDiffTSHwcapRv64gc` | Classifier.lean |
| 1562 | `classifies_patch_diff_T_s_hwcap_rv64gcv` | `ClassifiesPatchDiffTSHwcapRv64gcv` | Classifier.lean |
| 1567 | `classifies_good_inputs_T_s_hwcap_rv64gc` | `ClassifiesGoodInputsTSHwcapRv64gc` | Classifier.lean |
| 1571 | `classifies_good_inputs_T_s_hwcap_rv64gcv` | `ClassifiesGoodInputsTSHwcapRv64gcv` | Classifier.lean |
| 1575 | `classifies_patch_diff_T_s_hwcap_splits` | `classifiesPatchDiffTS_hwcap_splits` | Classifier.lean |
| 1581 | `classifies_good_inputs_T_s_hwcap_splits` | `classifiesGoodInputsTS_hwcap_splits` | Classifier.lean |
| 1591 | `accepts_fo` | `AcceptsFo` | Classifier.lean |
| 1596 | `rejects_fo` | `RejectsFo` | Classifier.lean |
| 1979 | `classifies_error_free_inputs_T_s_hwcap_rv64gc` | `ClassifiesErrorFreeInputsTSHwcapRv64gc` | Classifier.lean |
| 1983 | `classifies_error_free_inputs_T_s_hwcap_rv64gcv` | `ClassifiesErrorFreeInputsTSHwcapRv64gcv` | Classifier.lean |
| 1987 | `classifies_error_free_inputs_T_fo_hwcap_rv64gc` | `ClassifiesErrorFreeInputsTFoHwcapRv64gc` | Classifier.lean |
| 1990 | `classifies_error_free_inputs_T_fo_hwcap_rv64gcv` | `ClassifiesErrorFreeInputsTFoHwcapRv64gcv` | Classifier.lean |
| 1993 | `classifies_error_free_inputs_T_s_hwcap_splits` | `classifiesErrorFreeInputsTS_hwcap_splits` | Classifier.lean |
| 1999 | `classifies_error_free_inputs_T_fo_hwcap_splits` | `classifiesErrorFreeInputsTFo_hwcap_splits` | Classifier.lean |

### `Equivalence.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 101 | `trace_equiv` | `TraceEquiv` | Equivalence.lean |
| 122 | `equiv` | `BehEquiv` | Equivalence.lean |
| 193 | `modeled` | `Modeled` | Equivalence.lean |
| 215 | `error_free` | `ErrorFree` | Equivalence.lean |
| 233 | `dies_by_signal` | `DiesBySignal` | Equivalence.lean |
| 264 | `error_free_unkilled` | `ErrorFreeUnkilled` | Equivalence.lean |
| 496 | `image_phdrs_readable` | `imagePhdrsReadable` | Equivalence.lean |
| 551 | `image_brk_witness` | `imageBrkWitness` | Equivalence.lean |
| 555 | `image_brk_satisfiable` | `imageBrkSatisfiable` | Equivalence.lean |
| 714 | `strong_equiv` | `StrongEquiv` | Equivalence.lean |
| 733 | `strong_universal_T` | `strongUniversalT` | Equivalence.lean |
| 776 | `strong_equiv_error_free` | `StrongEquivErrorFree` | Equivalence.lean |
| 807 | `strong_universal_error_free_T` | `strongUniversalErrorFreeT` | Equivalence.lean |
| 913 | `strong_universal_T_abort` | `strongUniversalTAbort` | Equivalence.lean |
| 925 | `strong_universal_T_either` | `strongUniversalTEither` | Equivalence.lean |
| 967 | `strong_equiv_error_free_abort` | `StrongEquivErrorFreeAbort` | Equivalence.lean |
| 975 | `strong_universal_error_free_T_abort` | `strongUniversalErrorFreeTAbort` | Equivalence.lean |
| 1017 | `strong_universal_error_free_T_either` | `strongUniversalErrorFreeTEither` | Equivalence.lean |
| 1170 | `strong_equiv_va` | `StrongEquivVa` | Equivalence.lean |
| 1181 | `strong_universal_T_sv39` | `strongUniversalTSv39` | Equivalence.lean |
| 1188 | `strong_universal_T_sv57` | `strongUniversalTSv57` | Equivalence.lean |
| 1199 | `strong_universal_T_va_any` | `strongUniversalTVaAny` | Equivalence.lean |
| 1349 | `strong_universal_T_hwcap_rv64gc` | `strongUniversalTHwcapRv64gc` | Equivalence.lean |
| 1366 | `strong_universal_error_free_T_hwcap_rv64gc` | `strongUniversalErrorFreeTHwcapRv64gc` | Equivalence.lean |
| 1554 | `strong_universal_T_scfg` | `strongUniversalTScfg` | Equivalence.lean |
| 1569 | `strong_universal_error_free_T_scfg` | `strongUniversalErrorFreeTScfg` | Equivalence.lean |
| 1626 | `strong_universal_T_scfg_abort` | `strongUniversalTScfgAbort` | Equivalence.lean |
| 1687 | `strong_universal_error_free_T_scfg_abort` | `strongUniversalErrorFreeTScfgAbort` | Equivalence.lean |
| 1898 | `strong_universal_error_free_T_cfg` | `strongUniversalErrorFreeTCfg` | Equivalence.lean |
| 2160 | `source_within_budget` | `SourceWithinBudget` | Equivalence.lean |
| 2193 | `strong_universal_T_budgets` | `strongUniversalTBudgets` | Equivalence.lean |
| 2201 | `strong_universal_T_budgets_abort` | `strongUniversalTBudgetsAbort` | Equivalence.lean |
| 2209 | `strong_universal_error_free_T_budgets` | `strongUniversalErrorFreeTBudgets` | Equivalence.lean |
| 2217 | `strong_universal_error_free_T_budgets_abort` | `strongUniversalErrorFreeTBudgetsAbort` | Equivalence.lean |
| 2333 | `strong_universal_error_free_T_budgets_hwcap_rv64gc` | `strongUniversalErrorFreeTBudgetsHwcapRv64gc` | Equivalence.lean |
| 2366 | `strong_universal_error_free_T_budgets_abort_hwcap_rv64gc` | `strongUniversalErrorFreeTBudgetsAbortHwcapRv64gc` | Equivalence.lean |
| 2584 | `source_within_budget_scfg` | `SourceWithinBudgetScfg` | Equivalence.lean |
| 2613 | `strong_universal_T_scfg_budgets` | `strongUniversalTScfgBudgets` | Equivalence.lean |
| 2621 | `strong_universal_error_free_T_scfg_budgets` | `strongUniversalErrorFreeTScfgBudgets` | Equivalence.lean |
| 2708 | `strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc` | `strongUniversalErrorFreeTScfgBudgetsHwcapRv64gc` | Equivalence.lean |
| 2814 | `strong_universal_error_free_T_scfg_budgets_abort` | `strongUniversalErrorFreeTScfgBudgetsAbort` | Equivalence.lean |
| 2908 | `strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc` | `strongUniversalErrorFreeTScfgBudgetsAbortHwcapRv64gc` | Equivalence.lean |
| 3177 | `strong_universal_error_free_T_budgets_either` | `strongUniversalErrorFreeTBudgetsEither` | Equivalence.lean |
| 3243 | `asan_fixed_overhead` | `asanFixedOverhead` | Equivalence.lean |
| 3252 | `sanitizer_source_limit` | `sanitizerSourceLimit` | Equivalence.lean |
| 3257 | `budget_headroom_ok` | `budgetHeadroomOk` | Equivalence.lean |
| 3308 | `BUDGETS` | `Budgets` | Equivalence.lean |
| 3315 | `ShippedBudgets` | `shippedBudgets` | Equivalence.lean |
| 3335 | `SanitizerBudgets` | `sanitizerBudgets` | Equivalence.lean |

### `EquivalenceDefinition/FinInput.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 161 | `stream_of_list` | `ofList` | Stream.lean |
| 191 | `stream_of_list_then` | `ofListThen` | Stream.lean |

### `FinInput.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 452 | `FinProcInput` | `FinProcInput` | Classifier.lean |
| 496 | `to_proc_input` | `FinProcInput.toProcInput` | Classifier.lean |
| 527 | `valid_fin_input` | `ValidFinInput` | Classifier.lean |
| 594 | `FinCore` | `FinCore` | Classifier.lean |
| 601 | `fin_core` | `FinProcInput.core` | Classifier.lean |
| 990 | `inhabited_fin_input` | `inhabitedFinInput` | Classifier.lean |

### `Fs.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 49 | `path` | `Path` | Fs.lean |
| 51 | `path_eqb` | `pathEqb` | Fs.lean |
| 76 | `path_ltb` | `pathLtb` | Fs.lean |
| 86 | `Fs` | `FileSystem` | Fs.lean |
| 88 | `fs_lookup` | `lookup` | Fs.lean |
| 95 | `fs_set` | `set` | Fs.lean |
| 132 | `fs_remove` | `remove` | Fs.lean |
| 139 | `fs_sorted` | `sorted` | Fs.lean |
| 283 | `valid_fs` | `ValidFs` | Fs.lean |
| 297 | `path_slash_byte` | `slashByte` | Fs.lean |
| 313 | `key_is_relative` | `KeyIsRelative` | Fs.lean |
| 333 | `fs_keys_relative` | `KeysRelative` | Fs.lean |
| 368 | `file_from` | `fileFrom` | Fs.lean |
| 402 | `file_read` | `fileRead` | Fs.lean |
| 427 | `file_write` | `fileWrite` | Fs.lean |
| 466 | `file_truncate` | `fileTruncate` | Fs.lean |

### `HaltsAllowed.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 109 | `halts_allowed_T` | `haltsAllowedT` | Equivalence.lean |
| 125 | `halts_allowed_T_scfg` | `haltsAllowedTScfg` | Equivalence.lean |
| 153 | `halts_allowed_T_scfg_budgets` | `haltsAllowedTScfgBudgets` | Equivalence.lean |
| 338 | `status_allowed` | `statusAllowed` | Equivalence.lean |
| 366 | `byte_codes` | `byteCodes` | Equivalence.lean |

### `Measure.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 185 | `sum_weights` | `sumWeights` | Classifier.lean |
| 287 | `DISTRIBUTION` | `Distribution` | Classifier.lean |
| 407 | `weight_bound_T_fo` | `WeightBoundTFo` | Classifier.lean |

### `MemImageType.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 16 | `Segment` | `Segment` | MemImage.lean |
| 64 | `PhdrInfo` | `PhdrInfo` | MemImage.lean |
| 95 | `seg_readable` | `Segment.readable` | MemImage.lean |
| 96 | `seg_writable` | `Segment.writable` | MemImage.lean |
| 97 | `seg_executable` | `Segment.executable` | MemImage.lean |
| 125 | `Image` | `Image` | MemImage.lean |

### `Monad.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 129 | `outcome` | `Outcome` | Monad.lean |
| 135 | `Sys` | `Sys` | Monad.lean |
| 137 | `pure` | `pure` | Monad.lean |
| 141 | `bind` | `bind` | Monad.lean |
| 172 | `sys_equiv` | `Equiv` | Monad.lean |
| 268 | `unmodeled` | `unmodeled` | Monad.lean |
| 271 | `choose` | `choose` | Monad.lean |
| 275 | `alt` | `alt` | Monad.lean |
| 279 | `emit` | `emit` | Monad.lean |
| 285 | `input` | `input` | Monad.lean |
| 289 | `get_model` | `getModel` | Monad.lean |
| 290 | `modify` | `modify` | Monad.lean |
| 314 | `get_vmmaps` | `getVmmaps` | Monad.lean |

### `MustExit.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 261 | `must_exit_with` | `MustExitWith` | Equivalence.lean |
| 697 | `decided_from` | `DecidedFrom` | Equivalence.lean |
| 760 | `must_exit_with_scfg` | `MustExitWith` | Equivalence.lean |
| 857 | `run_decided` | `RunDecided` | Equivalence.lean |
| 929 | `must_exit_in_at` | `MustExitInAt` | Equivalence.lean |
| 946 | `must_exit_in` | `MustExitIn` | Equivalence.lean |
| 1290 | `must_exit_in_scfg` | `MustExitIn` | Equivalence.lean |
| 1384 | `run_reaches_killed_cfg` | `RunReachesKilled` | Equivalence.lean |

### `RiscvSemantics.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 139 | `write_to_mem` | `writeToMem` | Isa.lean |
| 203 | `machine_result` | `MachineResult` | Isa.lean |
| 298 | `segment_byte_at` | `Segment.byteAt` | MemImage.lean |
| 332 | `find_segment` | `findSegment` | MemImage.lean |
| 397 | `memory_read` | `memoryRead` | MemImage.lean |
| 528 | `wview` | `segmentWritableByte` | MemImage.lean |
| 825 | `access_report` | `AccessReport` | Isa.lean |

### `Run.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 80 | `behavior` | `Behavior` | Run.lean |
| 95 | `apply_writes` | `applyWrites` | Isa.lean |
| 104 | `zeros_cover` | `zerosCover` | Isa.lean |
| 113 | `apply_zeros` | `applyZeros` | Isa.lean |
| 128 | `apply_unmaps` | `applyUnmaps` | Isa.lean |
| 139 | `apply_copy` | `applyCopy` | Isa.lean |
| 150 | `apply_copies` | `applyCopies` | Isa.lean |
| 175 | `apply_effect` | `applyEffect`, `applyMemoryEffect` | Isa.lean, Machines/ProcessMemory.lean |
| 203 | `config` | `Config` | Run.lean |
| 211 | `segment_reservation` | `segmentReservation` | Run.lean |
| 216 | `segments_reserved` | `segmentsReserved` | Run.lean |
| 221 | `step_to` | `StepTo` | Run.lean |
| 316 | `mi_account_step` | `accountStep` | Run.lean |
| 394 | `sys_input` | `sysInput` | Run.lean |
| 399 | `sstep` | `SStep` | Run.lean |
| 468 | `star` | `Star` | Run.lean |
| 496 | `obs_trace` | `ObsTrace` | Run.lean |
| 689 | `reaches_error` | `ReachesError` | Run.lean |
| 805 | `unmodeled_at` | `UnmodeledAt` | Run.lean |
| 813 | `reaches_unmodeled` | `ReachesUnmodeled` | Run.lean |
| 879 | `all_traces_error` | `AllTracesError` | Run.lean |
| 955 | `entry_block_top` | `entryBlockTop` | Run.lean |
| 958 | `entry_page_top` | `entryPageTop` | Run.lean |
| 961 | `entry_slack_len` | `entrySlackLen` | Run.lean |
| 964 | `entry_slack` | `entrySlack` | Run.lean |
| 969 | `entry_stack_image` | `entryStackImage` | Run.lean |
| 1074 | `(` | `stackOverlay` | Isa.lean |
| 1096 | `init_config` | `initConfig` | Run.lean |
| 1138 | `ExecEntry` | `ExecEntry` | Run.lean |
| 1164 | `run` | `runWith`, `run` | Run.lean |
| 1294 | `SpuriousFamily` | `SpuriousFamily` | Run.lean |
| 1301 | `SpuriousCfg` | `SpuriousCfg` | Run.lean |
| 1310 | `may_fail_cfg` | `mayFailCfg` | Run.lean |
| 1311 | `forced_only_cfg` | `forcedOnlyCfg` | Run.lean |
| 1315 | `alloc_only_cfg` | `allocOnlyCfg` | Run.lean |
| 1318 | `family_may_fail` | `familyMayFail` | Run.lean |
| 1331 | `cfg_le` | `cfgLe` | Run.lean |
| 1346 | `InjectedArm` | `InjectedArm` | Run.lean |
| 1358 | `injected_table` | `injectedTable` | Run.lean |
| 1394 | `injected_arm` | `injectedArm` | Run.lean |
| 1398 | `ret_in_errnos` | `retInErrnos` | Run.lean |
| 1406 | `brk_refusal_b` | `brkRefusalB` | Run.lean |
| 1418 | `refusal_b` | `refusalB` | Run.lean |
| 1451 | `alloc_budget_refused_b` | `allocBudgetRefusedB` | Run.lean |
| 1533 | `injected_family_off` | `injectedFamilyOff` | Run.lean |
| 1544 | `spurious_refusal_cfg` | `spuriousRefusalCfg` | Run.lean |
| 1558 | `refusal_decided` | `RefusalDecided` | Run.lean |
| 1618 | `sstep_cfg` | `SStep` | Run.lean |
| 1910 | `run_scfg` | `runScfg`, `runWith` | Run.lean |
| 1926 | `behavior_equiv` | `BehaviorEquiv` | Run.lean |
| 1960 | `run_nospurious` | `runNospurious` | Run.lean |
| 1970 | `run_cfg` | `runCfg` | Run.lean |
| 2086 | `budget_refused_at` | `BudgetRefusedAt` | Run.lean |
| 2244 | `run_budget_refused` | `RunBudgetRefusedWith`, `RunBudgetRefused` | Run.lean |
| 2252 | `run_scfg_budget_refused` | `RunBudgetRefusedWith`, `RunScfgBudgetRefused` | Run.lean |
| 2292 | `valid_sp` | `ValidSp` | Run.lean |
| 2305 | `valid_brk` | `ValidBrk` | Run.lean |
| 2336 | `valid_mmap_base` | `ValidMmapBase` | Run.lean |
| 2351 | `valid_sp_va` | `ValidSpVa` | Run.lean |
| 2356 | `valid_mmap_base_va` | `ValidMmapBaseVa` | Run.lean |
| 2382 | `total_arg_bytes` | `totalArgBytes` | Run.lean |
| 2446 | `valid_argv` | `ValidArgv` | Run.lean |
| 2457 | `valid_envp` | `ValidEnvp` | Run.lean |
| 2541 | `entry_stack_span` | `entryStackSpan` | Run.lean |
| 2558 | `entry_stack_fits_va` | `EntryStackFitsVa` | Run.lean |
| 2635 | `valid_entry_va` | `ValidEntryVa` | Run.lean |
| 2643 | `valid_entry` | `ValidEntry` | Run.lean |
| 2700 | `valid_id` | `ValidId` | Run.lean |
| 2703 | `valid_creds` | `ValidCreds` | Run.lean |
| 2752 | `valid_nofile` | `ValidNofile` | Run.lean |
| 2818 | `valid_sigmask` | `ValidSigmask` | Run.lean |
| 2859 | `valid_hwcap` | `ValidHwcap` | Run.lean |
| 2906 | `valid_urandom` | `ValidUrandom` | Run.lean |
| 2973 | `valid_input` | `ValidInput` | Run.lean |
| 3007 | `valid_input_abort` | `ValidInputAbort` | Run.lean |
| 3021 | `valid_input_either` | `ValidInputEither` | Run.lean |
| 3075 | `valid_input_sv39` | `ValidInputSv39` | Run.lean |
| 3084 | `valid_input_sv57` | `ValidInputSv57` | Run.lean |
| 3093 | `valid_input_va_any` | `ValidInputVaAny` | Run.lean |
| 3258 | `valid_input_hwcap_rv64gc` | `ValidInputHwcapRv64gc` | Run.lean |
| 3267 | `valid_input_hwcap_rv64gcv` | `ValidInputHwcapRv64gcv` | Run.lean |
| 3345 | `valid_input_abort_hwcap_rv64gc` | `ValidInputAbortHwcapRv64gc` | Run.lean |
| 3354 | `valid_input_abort_hwcap_rv64gcv` | `ValidInputAbortHwcapRv64gcv` | Run.lean |

### `oss-verify-proofs/theories/Shapes.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 57 | `Budgets.Standard` | `Budgets.standard` | Shapes.lean |
| 61 | `Budgets.Asan` | `Budgets.asan` | Shapes.lean |
| 76 | `Env.may_fail` | `Env.mayFail` | Shapes.lean |
| 79 | `Env.alloc_forced_only` | `Env.allocForcedOnly` | Shapes.lean |
| 81 | `Env.forced_only` | `Env.forcedOnly` | Shapes.lean |
| 98 | `Exits.any` | `Exits.any` | Shapes.lean |
| 107 | `Exits.ok_or_refused` | `Exits.okOrRefused` | Shapes.lean |
| 123 | `agrees` | `agrees` | Shapes.lean |
| 143 | `agrees_in` | `agreesIn` | Shapes.lean |
| 161 | `agrees_iff_agrees_in_may_fail` | `agrees_iff_agreesIn_mayFail` | Shapes.lean |
| 174 | `agrees_abort_modelled` | `agreesAbortModelled` | Shapes.lean |
| 189 | `agrees_in_abort_modelled` | `agreesInAbortModelled` | Shapes.lean |
| 214 | `agrees_rv64gc` | `agreesRv64gc` | Shapes.lean |
| 229 | `agrees_abort_modelled_rv64gc` | `agreesAbortModelledRv64gc` | Shapes.lean |
| 245 | `agrees_in_rv64gc` | `agreesInRv64gc` | Shapes.lean |
| 274 | `halts_within_budget` | `haltsWithinBudget` | Shapes.lean |
| 291 | `halts_may_fail` | `haltsMayFail` | Shapes.lean |
| 302 | `halts_within_budget_mono` | `haltsWithinBudget_mono` | Shapes.lean |
| 310 | `halts_may_fail_mono` | `haltsMayFail_mono` | Shapes.lean |
| 337 | `disagrees_at_most` | `disagreesAtMost` | Shapes.lean |
| 350 | `classifies` | `classifies` | Shapes.lean |
| 371 | `classifier_rejects_at_most` | `classifierRejectsAtMost` | Shapes.lean |
| 384 | `agreement_decidable` | `agreementDecidable` | Shapes.lean |
| 390 | `disagrees_at_most_rv64gc` | `disagreesAtMostRv64gc` | Shapes.lean |
| 400 | `classifies_rv64gc` | `classifiesRv64gc` | Shapes.lean |
| 418 | `agreement_decidable_rv64gc` | `agreementDecidableRv64gc` | Shapes.lean |
| 422 | `classifies_rv64gc_of_classifies` | `classifiesRv64gc_of_classifies` | Shapes.lean |
| 427 | `disagrees_at_most_mono` | `disagreesAtMost_mono` | Shapes.lean |
| 436 | `classifier_rejects_at_most_mono` | `classifierRejectsAtMost_mono` | Shapes.lean |
| 455 | `disagrees_at_most_of_classifier` | `disagreesAtMost_of_classifier` | Shapes.lean |
| 471 | `agreement_decidable_of_classifier` | `agreementDecidable_of_classifier` | Shapes.lean |
| 475 | `disagrees_at_most_rv64gc_of_classifier` | `disagreesAtMostRv64gc_of_classifier` | Shapes.lean |
| 491 | `agreement_decidable_rv64gc_of_classifier` | `agreementDecidableRv64gc_of_classifier` | Shapes.lean |

### `Specs.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 185 | `modeled_sysnos` | `modeledSysnos` | Table.lean |
| 189 | `syscall_spec` | `syscallSpec` | Table.lean |

### `StackLayout.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 17 | `string_addrs` | `stringAddrs` | StackLayout.lean |
| 27 | `flatten_strings` | `flattenStrings` | StackLayout.lean |
| 51 | `hwcap_rv64gc` | `hwcapRv64gc` | StackLayout.lean |
| 52 | `hwcap_rv64gcv` | `hwcapRv64gcv` | StackLayout.lean |
| 211 | `auxv_entries` | `auxvEntries` | StackLayout.lean |
| 225 | `build_auxv` | `buildAuxv` | StackLayout.lean |
| 228 | `auxv_bytes` | `auxvBytes` | StackLayout.lean |
| 243 | `auxv_size` | `auxvSize` | StackLayout.lean |
| 318 | `EntryDraw` | `EntryDraw` | StackLayout.lean |
| 347 | `at_random_bytes` | `atRandomBytes` | StackLayout.lean |
| 360 | `at_random_ptr` | `atRandomPtr` | StackLayout.lean |
| 374 | `build_stack_bytes` | `buildStackBytes` | StackLayout.lean |
| 433 | `stack_to_mem` | `stackToMem` | StackLayout.lean |

### `State.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 33 | `two_pow_64` | `twoPow64` | Basic.lean |
| 34 | `page_size` | `pageSize` | Basic.lean |
| 39 | `page_round_up_Z` | `pageRoundUp` | Basic.lean |
| 41 | `page_round_down_Z` | `pageRoundDown` | Basic.lean |
| 61 | `page_round_down_Z_within` | `pageRoundDown_within` | Sys/MmExt.lean |
| 80 | `stack_max_size` | `stackMaxSize` | Basic.lean |
| 112 | `sp_window_lo` | `spWindowLo` | Basic.lean |
| 113 | `sp_window_hi` | `spWindowHi` | Basic.lean |
| 204 | `brk_aslr_max` | `brkAslrMax` | Basic.lean |
| 249 | `mmap_base_min` | `mmapBaseMin` | Basic.lean |
| 269 | `mmap_base_max` | `mmapBaseMax` | Basic.lean |
| 331 | `TASK_SIZE` | `taskSize` | Basic.lean |
| 393 | `VaSize` | `VaSize` | Basic.lean |
| 399 | `sv39_task_size` | `sv39TaskSize` | Basic.lean |
| 400 | `sv57_task_size` | `sv57TaskSize` | Basic.lean |
| 404 | `va_task_size` | `vaTaskSize` | Basic.lean |
| 413 | `va_stack_top` | `vaStackTop` | Basic.lean |
| 420 | `va_sp_window_hi` | `vaSpWindowHi` | Basic.lean |
| 421 | `va_sp_window_lo` | `vaSpWindowLo` | Basic.lean |
| 424 | `va_mmap_base_max` | `vaMmapBaseMax` | Basic.lean |
| 426 | `va_mmap_base_min` | `vaMmapBaseMin` | Basic.lean |
| 468 | `source_alloc_limit` | `sourceAllocLimit` | Basic.lean |
| 469 | `target_alloc_limit` | `targetAllocLimit` | Basic.lean |
| 473 | `addr_is_error_b` | `addrIsError` | Basic.lean |
| 477 | `errno_ret` | `errnoRet` | Basic.lean |
| 562 | `SyscallInput` | `SyscallInput` | State.lean |
| 585 | `in_arg` | `SyscallInput.arg` | State.lean |
| 591 | `MemCopy` | `MemCopy` | State.lean |
| 627 | `SyscallEffect` | `SyscallEffect` | State.lean |
| 637 | `mkEffect` | `mkEffect` | State.lean |
| 639 | `with_copyins` | `SyscallEffect.withCopyins` | State.lean |
| 652 | `read_bytes_aux` | `readBytesAux` | State.lean |
| 706 | `read_bytes_map` | `readBytesMap` | State.lean |
| 842 | `readable_bytes_aux` | `readableBytesAux` | State.lean |
| 894 | `readable_bytes` | `readableBytes` | State.lean |
| 1083 | `read_u64` | `readU64` | State.lean |
| 1132 | `MAX_RW_COUNT` | `MAX_RW_COUNT` | State.lean |
| 1150 | `rw_count_clamp` | `rwCountClamp` | State.lean |
| 1344 | `access_okb` | `accessOkb` | State.lean |
| 1793 | `InputStream` | `InputStream` | Stream.lean |
| 1806 | `stream_take` | `take` | Stream.lean |
| 1817 | `stream_bytes` | `bytes` | Stream.lean |
| 1821 | `stream_rest` | `rest` | Stream.lean |
| 1915 | `stream_take_z` | `takeZ` | Stream.lean |
| 1989 | `stream_infinite` | `Infinite` | Stream.lean |
| 2040 | `stream_const` | `const` | Stream.lean |
| 2076 | `default_urandom` | `defaultUrandom` | Stream.lean |
| 2127 | `NetStream` | `NetStream` | Stream.lean |
| 2141 | `net_take` | `take` | Stream.lean |
| 2236 | `net_ended` | `isEnded` | Stream.lean |
| 2260 | `net_take_z` | `takeZ` | Stream.lean |
| 2318 | `PeerAddr` | `PeerAddr` | Stream.lean |
| 2343 | `NetQueue` | `NetQueue` | Stream.lean |
| 2357 | `net_silent` | `netSilent` | Stream.lean |
| 2361 | `nq_peer` | `nqPeer` | Stream.lean |
| 2363 | `nq_script` | `nqScript` | Stream.lean |
| 2365 | `nq_rest` | `nqRest` | Stream.lean |
| 2424 | `SockState` | `SockState` | State.lean |
| 2434 | `PIPE_BUF` | `PIPE_BUF` | State.lean |
| 2462 | `PipeBuf` | `PipeBuf` | State.lean |
| 2611 | `FdEntry` | `FdEntry` | State.lean |
| 2704 | `VmMaps` | `VmMaps` | State.lean |
| 2737 | `alloc_top` | `allocTop` | State.lean |
| 2852 | `live_bytes` | `liveBytes` | State.lean |
| 2888 | `FdState` | `FdState` | State.lean |
| 2897 | `VmState` | `VmState` | State.lean |
| 2907 | `IoState` | `IoState` | State.lean |
| 2930 | `FsState` | `FsState` | State.lean |
| 2964 | `Creds` | `Creds` | State.lean |
| 3030 | `creds_privileged` | `Creds.privileged` | State.lean |
| 3035 | `ProcState` | `ProcState` | State.lean |
| 3337 | `LimState` | `LimState` | State.lean |
| 3381 | `TimeState` | `TimeState` | State.lean |
| 3429 | `Model` | `Model` | State.lean |
| 3441 | `m_fds` | `fds` | State.lean |
| 3442 | `m_pipes` | `pipes` | State.lean |
| 3443 | `m_vmmaps` | `vmmaps` | State.lean |
| 3444 | `m_vm_lazy` | `vmLazy` | State.lean |
| 3445 | `m_vm_materialized` | `vmMaterialized` | State.lean |
| 3447 | `m_stdin` | `stdin` | State.lean |
| 3448 | `m_urandom` | `urandom` | State.lean |
| 3449 | `m_net` | `net` | State.lean |
| 3451 | `m_fs` | `fs` | State.lean |
| 3452 | `m_halted` | `halted` | State.lean |
| 3453 | `m_tid` | `tid` | State.lean |
| 3456 | `m_has_children` | `hasChildren` | State.lean |
| 3464 | `m_killed` | `killedBy` | State.lean |
| 3466 | `m_sigabrt_pending` | `sigabrtPending` | State.lean |
| 3468 | `m_abort_terminal` | `abortTerminal` | State.lean |
| 3477 | `m_creds` | `creds` | State.lean |
| 3491 | `overflow_id` | `overflowId` | State.lean |
| 3506 | `default_nofile` | `defaultNofile` | State.lean |
| 3513 | `mkModel` | `mkModel` | State.lean |
| 3528 | `with_fds` | `withFds` | State.lean |
| 3531 | `with_pipes` | `withPipes` | State.lean |
| 3534 | `with_vmmaps` | `withVmmaps` | State.lean |
| 3538 | `with_vm_backing` | `withVmBacking` | State.lean |
| 3542 | `with_stdin` | `withStdin` | State.lean |
| 3548 | `with_urandom` | `withUrandom` | State.lean |
| 3556 | `with_net` | `withNet` | State.lean |
| 3581 | `statpins_restrict` | `statpinsRestrict` | State.lean |
| 3588 | `with_fs` | `withFs` | State.lean |
| 3605 | `with_halted` | `withHalted` | State.lean |
| 3614 | `with_tid` | `withTid` | State.lean |
| 3698 | `with_abort_terminal` | `withAbortTerminal` | State.lean |
| 3708 | `with_nofile` | `withNofile` | State.lean |
| 3711 | `with_creds` | `withCreds` | State.lean |
| 3746 | `with_children` | `withChildren` | State.lean |
| 3766 | `with_sigmask` | `withSigmask` | State.lean |
| 3847 | `with_killed` | `withKilled` | State.lean |
| 3881 | `with_clock` | `withClock` | State.lean |
| 3902 | `event` | `Event` | State.lean |
| 3922 | `fd_lookup` | `fdLookup` | State.lean |
| 3929 | `fd_insert` | `fdInsert` | State.lean |
| 3933 | `fd_remove` | `fdRemove` | State.lean |
| 3943 | `alloc_fd_aux` | `allocFdAux` | State.lean |
| 3952 | `alloc_fd` | `allocFd` | State.lean |
| 3974 | `pipe_lookup` | `pipeLookup` | State.lean |
| 3982 | `pipe_insert` | `pipeInsert` | State.lean |
| 4014 | `pipe_write_room` | `pipeWriteRoom` | State.lean |
| 4022 | `pipe_append` | `pipeAppend` | State.lean |
| 4040 | `pipe_take` | `pipeTake` | State.lean |
| 4073 | `pipe_consume` | `pipeConsume` | State.lean |
| 4217 | `pipe_end_live` | `pipeEndLive` | State.lean |
| 4268 | `iv_overlap` | `ivOverlap` | State.lean |
| 4273 | `region_free` | `regionFree` | State.lean |
| 4282 | `region_free_In` | `regionFree_mem` | Sys/MmExt.lean |
| 4298 | `region_free_intro` | `regionFree_intro` | Sys/MmExt.lean |
| 4313 | `region_free_false` | `regionFree_false` | Sys/MmExt.lean |
| 4325 | `map_remove` | `mapRemove` | State.lean |
| 4336 | `reserved_top` | `reservedTop` | State.lean |
| 4360 | `iv_subtract` | `ivSubtract` | State.lean |
| 4369 | `maps_subtract` | `mapsSubtract` | State.lean |
| 4381 | `maps_subtract_all` | `mapsSubtractAll` | State.lean |
| 4417 | `entries_nonzero` | `EntriesNonzero` | Sys/MmExt.lean |
| 4420 | `entries_nonzero_nil` | `entriesNonzero_nil` | Sys/MmExt.lean |
| 4437 | `entries_nonzero_cons` | `entriesNonzero_cons` | Sys/MmExt.lean |
| 4450 | `bv_unsigned_range_u64` | `uns_range` | Sys/MmExt.lean |
| 4457 | `bv_unsigned_Z_to_bv_u64` | `uns_zw` | Sys/MmExt.lean |
| 4466 | `iv_subtract_nonzero` | `ivSubtract_nonzero` | Sys/MmExt.lean |
| 4488 | `maps_subtract_nonzero` | `mapsSubtract_nonzero` | Sys/MmExt.lean |
| 4501 | `maps_subtract_all_nonzero` | `mapsSubtractAll_nonzero` | Sys/MmExt.lean |
| 4509 | `vm_backed_maps` | `vmBackedMaps` | State.lean |
| 4530 | `page_base_of` | `pageBaseOf` | State.lean |
| 4535 | `page_mem` | `pageMem` | State.lean |
| 4538 | `page_insert` | `pageInsert` | State.lean |
| 4549 | `access_pages_acc` | `accessPagesAcc` | State.lean |
| 4560 | `accesses_pages` | `accessesPages` | State.lean |
| 4568 | `page_in_ranges` | `pageInRanges` | State.lean |
| 4577 | `newly_materialized_pages` | `newlyMaterializedPages` | State.lean |
| 4583 | `materialize_accesses` | `materializeAccesses` | State.lean |
| 4650 | `vm_backing_used` | `vmBackingUsed` | State.lean |
| 4659 | `vm_backing_within_limit` | `vmBackingWithinLimit` | State.lean |
| 4662 | `materialize_model_accesses` | `materializeModelAccesses` | State.lean |
| 4670 | `page_outside_range` | `pageOutsideRange` | State.lean |
| 4676 | `vm_forget_range` | `vmForgetRange` | State.lean |
| 4697 | `write_accesses` | `writeAccesses` | State.lean |
| 4704 | `syscall_effect_accesses` | `syscallEffectAccesses` | State.lean |
| 4746 | `lazy_interior` | `lazyInterior` | State.lean |
| 4755 | `vm_add_lazy` | `vmAddLazy` | State.lean |
| 4809 | `map_contains` | `mapContains` | State.lean |
| 4821 | `map_has` | `mapHas` | State.lean |
| 4857 | `noaccess_pages_owned` | `NoaccessPagesOwned` | Sys/MmExt.lean |
| 4901 | `vm_noaccess_entries_nonzero` | `VmNoaccessEntriesNonzero` | Sys/MmExt.lean |
| 4930 | `tmp_prefix` | `tmpPrefix` | State.lean |
| 4934 | `tmp_key` | `tmpKey` | State.lean |
| 4943 | `tmp_nul_free` | `tmpNulFree` | State.lean |
| 4961 | `fs_seed_tmp` | `fsSeedTmp` | State.lean |
| 5150 | `ProcInput` | `ProcInput` | State.lean |
| 5327 | `in_fs` | `ProcInput.fs` | State.lean |
| 5370 | `init_model` | `initModel` | State.lean |
| 5396 | `init_model_noaccess_nonzero` | `initModel_noaccess_nonzero` | Sys/MmExt.lean |

### `Sys/Dispatch.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 34 | `SpecArm` | `SpecArm` | Table.lean |
| 41 | `lookup_arm` | `lookupArm` | Table.lean |
| 53 | `dispatch` | `dispatch` | Table.lean |
| 61 | `arm_numbers` | `armNumbers` | Table.lean |

### `Sys/Drivers/Char/Random.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 26 | `getrandom_errnos` | `getrandomErrnos` | Sys/Kernel.lean |
| 51 | `getrandom_small_max` | `getrandomSmallMax` | Sys/Kernel.lean |
| 90 | `getrandom_spec` | `getrandomSpec` | Sys/Kernel.lean |

### `Sys/Fs/DPath.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 46 | `,` | `injectedTable` | Run.lean |

### `Sys/Fs/File.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 166 | `,` | `injectedTable` | Run.lean |

### `Sys/Fs/Namei.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 32 | `dotdot_path` | `dotdotPath` | Run.lean |
| 46 | `path_has_slash` | `pathHasSlash` | Run.lean |

### `Sys/Fs/Open.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 1387 | `close_spec` | `closeSpec` | Sys/Kernel.lean |

### `Sys/Fs/Pipe.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 41 | `,` | `injectedTable` | Run.lean |

### `Sys/Fs/ReadWrite.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 34 | `modeled_zero_fill` | `modeledZeroFill` | Sys/ReadWrite.lean |
| 44 | `modeled_file_gap` | `modeledFileGap` | Sys/ReadWrite.lean |
| 90 | `append_new_pos` | `appendNewPos` | Sys/ReadWrite.lean |
| 233 | `rw_pos_einvalb` | `rwPosEinvalb` | Sys/ReadWrite.lean |
| 257 | `socket_pending_error` | `socketPendingErrorWith accessOkb` | Sys/ReadWrite.lean |
| 321 | `read_urandom` | `readUrandom` | Sys/ReadWrite.lean |
| 345 | `read_spec` | `readSpec` | Sys/ReadWrite.lean |
| 859 | `write_range_gate` | `writeRangeGate` | Sys/ReadWrite.lean |
| 869 | `write_ledger` | `writeLedger` | Sys/ReadWrite.lean |
| 895 | `write_file_tail` | `writeFileTail` | Sys/ReadWrite.lean |
| 909 | `write_spec` | `writeSpec` | Sys/ReadWrite.lean |

### `Sys/Kernel/Exit.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 22 | `exit_spec` | `exitSpec` | Sys/Kernel.lean |
| 33 | `WAIT_ANY32` | `WAIT_ANY32` | Sys/Kernel.lean |
| 244 | `wait4_spec` | `wait4Spec` | Sys/Kernel.lean |

### `Sys/Kernel/Fork.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 72 | `PID_MAX_ENVELOPE` | `PID_MAX_ENVELOPE` | Sys/Kernel.lean |
| 123 | `set_tid_address_spec` | `setTidAddressSpec` | Sys/Kernel.lean |
| 393 | `SIGCHLD` | `SIGCHLD` | Sys/Fork.lean |
| 510 | `clone_errnos` | `cloneErrnos` | Sys/Fork.lean |
| 564 | `clone_fork_flags_b` | `cloneForkFlagsB` | Sys/Fork.lean |
| 615 | `clone_no_shared_file_b` | `cloneNoSharedFileB` | Sys/Fork.lean |
| 679 | `clone_pid_ok_b` | `clonePidOkB` | Sys/Fork.lean |
| 699 | `clone_resolve` | `cloneResolve` | Sys/Fork.lean |
| 708 | `clone_spec` | `cloneSpec` | Sys/Fork.lean |
| 783 | `CLONE_ARGS_SIZE` | `CLONE_ARGS_SIZE` | Sys/Fork.lean |
| 786 | `clone_args_field` | `cloneArgsField` | Sys/Fork.lean |
| 789 | `clone3_fork_args_b` | `clone3ForkArgsB` | Sys/Fork.lean |
| 804 | `CLONE_ARGS_SIZE_nat` | `CLONE_ARGS_SIZE_nat` | Sys/Fork.lean |
| 806 | `clone_args_size_nat_ok` | `cloneArgsSizeNat_ok` | Sys/Fork.lean |
| 823 | `clone3_resolve` | `clone3Resolve` | Sys/Fork.lean |
| 830 | `clone3_resolve_inv` | `clone3Resolve_inv` | Sys/Fork.lean |
| 841 | `clone3_spec` | `clone3Spec` | Sys/Fork.lean |
| 510 | `,` | `injectedTable` | Run.lean |

### `Sys/Kernel/Sys.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 112 | `getpid_spec` | `getpidSpec` | Sys/Kernel.lean |
| 173 | `gettid_spec` | `gettidSpec` | Sys/Kernel.lean |
| 730 | `getid_spec` | `getidSpec` | Sys/Kernel.lean |
| 756 | `setid_errnos` | `setidErrnos` | Run.lean |

### `Sys/Mm/Madvise.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 166 | `madvise_dontneed_b` | `madviseDontneedB` | Sys/MmExt.lean |
| 171 | `madvise_dontneed_ok` | `madviseDontneedOk` | Sys/MmExt.lean |
| 213 | `madvise_noaccess_decline_names_a_protected_byte` | `madvise_noaccess_decline_names_a_protected_byte` | Sys/MmExt.lean |
| 238 | `madvise_dontneed_next` | `madviseDontneedNext` | Sys/MmExt.lean |
| 245 | `madvise_spec` | `madviseSpec` | Sys/MmExt.lean |

### `Sys/Mm/Mmap.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 141 | `min_brk` | `minBrk` | Sys/Mmap.lean |
| 154 | `brk_is_grow` | `brkIsGrow` | Sys/Mmap.lean |
| 165 | `brk_grants` | `brkGrants` | Sys/Mmap.lean |
| 173 | `brk_page_range` | `brkPageRange` | Sys/Mmap.lean |
| 185 | `brk_zeros` | `brkZeros` | Sys/Mmap.lean |
| 208 | `brk_unmaps` | `brkUnmaps` | Sys/Mmap.lean |
| 339 | `brk_budget_ok` | `brkBudgetOk` | Sys/Mmap.lean |
| 343 | `brk_grow_ok` | `brkGrowOk` | Sys/Mmap.lean |
| 360 | `brk_r_ok` | `brkROk` | Sys/Mmap.lean |
| 381 | `brk_maps_next` | `brkMapsNext` | Sys/Mmap.lean |
| 396 | `maps_subtract_ranges` | `mapsSubtractRanges` | Sys/Mmap.lean |
| 403 | `brk_model_next` | `brkModelNext` | Sys/Mmap.lean |
| 467 | `maps_subtract_ranges_nonzero` | `mapsSubtractRanges_nonzero` | Sys/MmExt.lean |
| 481 | `mmap_request_len_nonzero` | `mmap_request_len_nonzero` | Sys/MmExt.lean |
| 518 | `mmap_noaccess_grant_inline_nonzero` | `mmap_noaccess_grant_inline_nonzero` | Sys/MmExt.lean |
| 537 | `mmap_fixed_noaccess_inline_nonzero` | `mmap_fixed_noaccess_inline_nonzero` | Sys/MmExt.lean |
| 562 | `munmap_inline_nonzero` | `munmap_inline_nonzero` | Sys/MmExt.lean |
| 577 | `brk_model_next_noaccess_nonzero` | `brkModelNext_noaccess_nonzero` | Sys/MmExt.lean |
| 585 | `forget_vm_ranges` | `forgetVmRanges` | Sys/Mmap.lean |
| 593 | `with_brk_next` | `withBrkNext` | Sys/Mmap.lean |
| 598 | `brk_spec` | `brkSpec` | Sys/Mmap.lean |
| 637 | `brk_budget_refused_b` | `brkBudgetRefusedB` | Sys/Mmap.lean |
| 645 | `,` | `injectedTable` | Run.lean |
| 645 | `mmap_errnos` | `mmapErrnos` | Sys/Mmap.lean |
| 675 | `MAP_NORESERVE` | `MAP_NORESERVE` | Basic.lean |
| 687 | `mmap_flags_core` | `mmapFlagsCore` | Sys/Mmap.lean |
| 690 | `mmap_noreserve_b` | `mmapNoreserveB` | Sys/Mmap.lean |
| 693 | `with_mmap_backing` | `withMmapBacking` | Sys/Mmap.lean |
| 696 | `with_mmap_replacement` | `withMmapReplacement` | Sys/Mmap.lean |
| 703 | `with_mmap_destroyed` | `withMmapDestroyed` | Sys/Mmap.lean |
| 708 | `mmap_flags_core_id` | `mmap_flags_core_id` | Sys/MmExt.lean |
| 761 | `mmap_anon_b` | `mmapAnonB` | Sys/Mmap.lean |
| 780 | `mmap_off_aligned_b` | `mmapOffAlignedB` | Sys/Mmap.lean |
| 816 | `mmap_pglen_ok_b` | `mmapPglenOkB` | Sys/Mmap.lean |
| 890 | `mmap_plain_anon_b` | `mmapPlainAnonB` | Sys/Mmap.lean |
| 999 | `mmap_modeled_b` | `mmapModeledB` | Sys/Mmap.lean |
| 1009 | `mmap_noaccess_b` | `mmapNoaccessB` | Sys/Mmap.lean |
| 1017 | `mmap_fixed_noaccess_b` | `mmapFixedNoaccessB` | Sys/Mmap.lean |
| 1065 | `mmap_fixed_rw_b` | `mmapFixedRwB` | Sys/Mmap.lean |
| 1074 | `mmap_fixed_rw_next` | `mmapFixedRwNext` | Sys/Mmap.lean |
| 1082 | `mmap_fixed_rw_next_noaccess_nonzero` | `mmapFixedRwNext_noaccess_nonzero` | Sys/MmExt.lean |
| 1143 | `mmap_fixed_destroyed_next` | `mmapFixedDestroyedNext` | Sys/Mmap.lean |
| 1153 | `mmap_fixed_destroyed_next_noaccess_nonzero` | `mmapFixedDestroyedNext_noaccess_nonzero` | Sys/MmExt.lean |
| 1164 | `mmap_fixed_rw_span_next` | `mmapFixedRwSpanNext` | Sys/Mmap.lean |
| 1174 | `mmap_fixed_rw_span_next_noaccess_nonzero` | `mmapFixedRwSpanNext_noaccess_nonzero` | Sys/MmExt.lean |
| 1190 | `mmap_fixed_noaccess_span_next` | `mmapFixedNoaccessSpanNext` | Sys/Mmap.lean |
| 1204 | `mmap_fixed_noaccess_span_next_noaccess_nonzero` | `mmapFixedNoaccessSpanNext_noaccess_nonzero` | Sys/MmExt.lean |
| 1220 | `mmap_fixed_noaccess_span_next_noaccess_nonzero_of_len` | `mmapFixedNoaccessSpanNext_noaccess_nonzero_of_len` | Sys/MmExt.lean |
| 1233 | `mmap_noreserve_backed_ok` | `mmapNoreserveBackedOk` | Sys/Mmap.lean |
| 1238 | `mmap_fixed_rw_budget_ok` | `mmapFixedRwBudgetOk` | Sys/Mmap.lean |
| 1255 | `mmap_fixed_rw_span_budget_ok` | `mmapFixedRwSpanBudgetOk` | Sys/Mmap.lean |
| 1384 | `mmap_noreplace_flags_b` | `mmapNoreplaceFlagsB` | Sys/Mmap.lean |
| 1396 | `mmap_noreplace_rw_b` | `mmapNoreplaceRwB` | Sys/Mmap.lean |
| 1400 | `mmap_noreplace_noaccess_b` | `mmapNoreplaceNoaccessB` | Sys/Mmap.lean |
| 1470 | `mmap_spec` | `mmapSpec` | Sys/Mmap.lean |
| 2119 | `mmap_budget_refused_b` | `mmapBudgetRefusedB` | Sys/Mmap.lean |
| 2220 | `munmap_free_ok` | `munmapFreeOk` | Sys/Mmap.lean |
| 2224 | `munmap_spec` | `munmapSpec` | Sys/Mmap.lean |

### `Sys/Mm/Mprotect.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 78 | `mprotect_errnos` | `mprotectErrnos` | Sys/MmExt.lean |
| 189 | `mprotect_modeled_b` | `mprotectModeledB` | Sys/MmExt.lean |
| 197 | `mprotect_grows_conflict_b` | `mprotectGrowsConflictB` | Sys/MmExt.lean |
| 205 | `mprotect_model_next` | `mprotectModelNext` | Sys/MmExt.lean |
| 220 | `mprotect_model_next_noaccess_nonzero` | `mprotectModelNext_noaccess_nonzero` | Sys/MmExt.lean |
| 230 | `mprotect_budget_ok` | `mprotectBudgetOk` | Sys/MmExt.lean |
| 233 | `mprotect_spec` | `mprotectSpec` | Sys/MmExt.lean |
| 330 | `mprotect_budget_refused_b` | `mprotectBudgetRefusedB` | Sys/MmExt.lean |

### `Sys/Mm/Mremap.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 115 | `,` | `injectedTable` | Run.lean |
| 115 | `mremap_errnos` | `mremapErrnos` | Sys/MmExt.lean |
| 120 | `mremap_maps_next` | `mremapMapsNext` | Sys/MmExt.lean |
| 129 | `mremap_backing_uniform_b` | `mremapBackingUniformB` | Sys/MmExt.lean |
| 133 | `mremap_source_lazy_b` | `mremapSourceLazyB` | Sys/MmExt.lean |
| 140 | `mremap_model_next` | `mremapModelNext` | Sys/MmExt.lean |
| 159 | `mremap_tail` | `mremapTail` | Sys/MmExt.lean |
| 176 | `page_align_is0_b` | `pageAlignIs0B` | Sys/MmExt.lean |
| 202 | `mremap_source_b` | `mremapSourceB` | Sys/MmExt.lean |
| 220 | `mremap_final_budget_b` | `mremapFinalBudgetB` | Sys/MmExt.lean |
| 251 | `mremap_inplace_grow_b` | `mremapInplaceGrowB` | Sys/MmExt.lean |
| 341 | `mremap_fresh_b` | `mremapFreshB` | Sys/MmExt.lean |
| 376 | `mremap_fresh_avoids_noaccess` | `mremap_fresh_avoids_noaccess` | Sys/MmExt.lean |
| 416 | `mremap_inplace_effect` | `mremapInplaceEffect` | Sys/MmExt.lean |
| 443 | `mremap_move_effect` | `mremapMoveEffect` | Sys/MmExt.lean |
| 610 | `mremap_spec` | `mremapSpec` | Sys/MmExt.lean |
| 694 | `mremap_move_charge` | `mremapMoveCharge` | Sys/MmExt.lean |
| 718 | `mremap_move_budget_b` | `mremapMoveBudgetB` | Sys/MmExt.lean |
| 774 | `mremap_budget_refused_b` | `mremapBudgetRefusedB` | Sys/MmExt.lean |

### `Sys/Syscall.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 19 | `ret_only` | `retOnly` | Syscall.lean |
| 22 | `err_ret` | `errRet` | Syscall.lean |
| 27 | `record_copyins` | `recordCopyins` | Syscall.lean |
| 77 | `errno_from` | `errnoFrom` | Syscall.lean |
| 80 | `w_is0` | `wIs0` | Syscall.lean |
| 114 | `abi_low32` | `abiLow32` | Syscall.lean |
| 151 | `fd32` | `fd32` | Syscall.lean |
| 238 | `int32` | `int32` | Syscall.lean |
| 324 | `pid32` | `pid32` | Syscall.lean |
| 329 | `waitopts32` | `waitopts32` | Syscall.lean |

### `Sys/SyscallTable.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 41 | `spec_table` | `specTable` | Table.lean |

### `Sys/Uaccess.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 319 | `rw_bytes_max` | `rwBytesMax` | Syscall.lean |
| 329 | `modeled_rw_count` | `modeledRwCount` | Syscall.lean |
| 397 | `modeled_rw_range` | `modeledRwRange` | Syscall.lean |
| 442 | `access_ok_zero` | `accessOkZero` | Syscall.lean |
| 499 | `write_source` | `writeSource` | Syscall.lean |
| 536 | `delivered_writes` | `deliveredWrites` | Syscall.lean |

### `Sys/Uapi.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 808 | `sig_kernel_only_mask` | `sigKernelOnlyMask` | Run.lean |

### `proofs/theories/Images.v`

| line | upstream | Lean | file |
| ---: | --- | --- | --- |
| 21 | `image_wf` | `ImageWf` | Equivalence.lean |
