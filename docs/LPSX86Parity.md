# Native x86 integration for the direct LPS translation

The claim this work supports, its caveats and its variant lattice, for x86-64 and riscv64,
are in [AtLeastAsGoodAsTheoremDev.md](AtLeastAsGoodAsTheoremDev.md).

This work builds on the direct ISA-parametric LPS translation. The syscall
families own `Sys/*` and `Table.lean`; this work adds machine, launch and native
ABI integration without editing those files.

The semantic reference is LPS `f1006fe8178338a499b5e5c41be83006c4edd058`.
The reference table (`specTable`) has all 90 arms translated. The reviewed
default native table (`NativeX86.table`) still enables only `reviewedNames` and
keeps the rest pending; the complete native table is `NativeX86.All.nativeTable`
(next section). A pending call produces an explicit unmodeled outcome, rather
than an empty relation that could make a safety proof vacuous.

## The complete native table (`NativeX86.All`)

`NativeX86All.lean` installs the families' own x86-64 arms (`familyX86Arms`)
into all ninety reference slots through `checkedTableWithFamilies`
(`checked_referenceTable`), and composes twenty extensions separately: the
eighteen family legacy arms, `getrlimit` (97, as `prlimit64(0, …)` with the
x86-64 `access_ok`) and `arch_prctl(ARCH_SET_FS)`. Where `Legacy.arms`
and the families both export a legacy name (`open`, `stat`, `lstat`, `poll`,
`access`, `pipe`, `dup2`, `unlink`, `readlink`), the family arm is used.

* `referenceSlot_live`: every catalogue row dispatches, at its native number, a
  translated arm whose specification is the chaos form of the family's x86-64
  arm with that number and name (not just a status flag).
* Kernel profile: Linux x86-64 v6.13 through v6.18 (the checked range), four-level paging, LAM off
  (`USER_PTR_MAX = TASK_SIZE_MAX`). v6.12 itself (`TASK_SIZE_MAX - 1`) is not
  covered.
* Chaos (`guard`, `sigaltstackChaos`): an arm answers only `unmodeled` when an
  argument register lies in `[TASK_SIZE_MAX, 2^47]`, or a constant-size pointer
  argument (`constPtrArgs`) lies within its size below `TASK_SIZE_MAX`, where
  x86-64's base-only `access_ok` may let a copy write a prefix and then fault;
  and `sigaltstack` answers only where every `strict_sas_size` reading agrees.
* `pointerAudit`: every native arm's pointer registers (constant-size, range,
  path, unread); `constPtrArgs` is derived from it, `pointerAudit_complete`
  covers every arm of `nativeTable`, `constPtrArgs_reviewed` matches the
  hand-reviewed list.
* `NativeX86AllReach`: a build-time walk of the definitions reachable from the
  native arms fails if LPS's `copy_iovecs_aux` (no `access_ok`) is reached
  outside `__import_iovec`. Before `sendmsgSpecX86`, arm 46 was LPS's
  `sendmsg_spec`, which sends the readable prefix where x86-64 Linux returns
  `-EFAULT`; that was a soundness bug, now fixed and locked by this check.
* Variants: `exactTable` (family arms unchanged) and `nativeTable` (with chaos);
  `nativeTable_restricts_exact` is `Lattice.Restricts` between them.
  `sigaltstackChaosUpTo bound` is a further (uninstalled) point for a declared
  signal-frame bound, between `sigaltstackChaos` and the family arm.
* `NativeX86Refusal`: the x86-64 refusal reading over the native specification.
  `system` uses `spuriousRefusalCfgX86Ext`, which gives `open`/`creat`,
  `access`, `unlink`/`rmdir`, `pipe` and `fork`/`vfork` the injected family of
  `openat`, `faccessat`, `unlinkat`, `pipe2` and `clone`; `systemCatalogue`
  keeps the catalogue-only `spuriousRefusalCfgX86` (never refuses an
  extension), the weaker point (`spuriousRefusalCfgX86_le_ext`).
  `MmRunX86`'s hard-coded rows and `refusal_b` are proved equal to the
  renumbered LPS ones, and `accessOkbX86` equals `accessOkbFor x86AddressSpace`
  on every `unsigned long` length.
* `SoundReference` (riscv64): LPS's `sendmsg_spec` skips `__import_iovec`'s
  `access_ok` on riscv64 too. `soundSyscallSpec` (LPS's arm, `unmodeled` where
  the imports differ) restricts both LPS's `syscallSpec` and the Linux-faithful
  `linuxSyscallSpec`, so agreement proved over it transfers to both
  (`agrees_lps_of_sound`, `agrees_linux_of_sound`).
* `NativeX86AllStatements`: the statement profile over this system with an
  explicit `AT_HWCAP` feature profile (quantified or declared;
  `agreement_of_quantified`), and `validEntry_witness`, a valid entry for every
  valid input and draw.
  Fidelity gap: the launch writes `AT_HWCAP2 = 0` and `AT_SYSINFO_EHDR = 0` and
  no `AT_MINSIGSTKSZ`, which no kernel in the profile produces; statements cover
  this declared launch only, not Linux's actual auxiliary vector.

## Gap sweep (`NativeX86.GapSweep`)

`X86GapSweep.lean` adds a more-defined point above `nativeTable`: `gapTable` puts
five guarded arms in front of the hub's table, and `gapTable_restricts` proves
`Restricts (dispatch nativeTable) (dispatch gapTable)`. The hub is unchanged.

* `arch_prctl` (158): `ARCH_SET_FS` as in the hub; `ARCH_SET_GS` (0, or `-EPERM`
  at or above `TASK_SIZE_MAX`; the GS base is invisible to `X86.Ext`);
  `ARCH_GET_FS`/`ARCH_GET_GS` as `put_user` of any word (`-EFAULT` outside
  `access_ok`, the band below `TASK_SIZE_MAX` included: the single store faults
  whole on the guard page, so that band is answered rather than guarded).
  `Machines.x86ExtNativeFs` stores the machine's FS base for a successful
  `ARCH_GET_FS`, and `getFs_step_admitted` (arm level) and
  `getFs_dispatch_admitted` (at `dispatch gapTable`) show that this is the step
  for an effect the specification admits.
* `setrlimit` (160): `prlimit64(0, resource, rlim, NULL)`, with a NULL `rlim`
  declined.
* `kill` (62): `tkill(pid, sig)` for `pid > 0`. The model is single-threaded, so
  the process-directed and thread-directed sends agree. `pid <= 0` declines.
* `clock_nanosleep` (230): `nanosleep` for `CLOCK_MONOTONIC` without
  `TIMER_ABSTIME`; other clocks and absolute sleeps decline.
* `epoll_pwait2` (441): the `timespec` checks (`-EFAULT`, `-EINVAL`), then
  `epoll_pwait`. See the order of `do_epoll_wait` below.
* `do_epoll_wait` order (`epoll_wait` 232, `epoll_pwait` 281, `epoll_pwait2`
  441). Up to v6.14 Linux checks `maxevents` (`-EINVAL`), then `access_ok`
  (`-EFAULT`), then `fdget(epfd)` (`-EBADF`) (`fs/eventpoll.c:2541-2559` in
  v6.8). From v6.15, commit `6b47d35d4d9e` ("eventpoll: abstract out parameter
  sanity checking") looks `epfd` up first and then runs `ep_check_params`. That is
  LPS's (v6.18) order, which the asm-generic translation keeps
  (`FdEventsAbi.epollFdFirst`). The hub's profile (v6.13 to v6.18) spans both
  orders. The orders disagree exactly on an unopened `epfd` with a bad
  `maxevents` or a bad `events` range (`epollWaitOrders_agree`,
  `epollWaitOrders_disagree`). The native table's version chaos
  (`All.epollOrderChaos`, part of `chaos`) and the gap sweep's `epoll_pwait2` arm
  return `unmodeled` on those inputs and keep the shared answer elsewhere. The
  installed arms restrict both the v6.14-order arms (`FdEventsAbi.x86`) and the
  v6.15-order arms (`FdEventsAbi.x86FdFirst`):
  `epollWait_restricts_v614`/`_v615`, `epollPwait_restricts_v614`/`_v615` and
  `epollPwait2_restricts_v614`/`_v615`. The tables restrict their exact
  variants (`nativeTable_restricts_exact`, `gapTable_restricts_exact`).
* `rt_sigprocmask` (14, hub family): the `oset` copy-out now uses the whole-range
  `accessGateX86`. The former base-only reading restricts it
  (`rtSigprocmask_restricts`). The band answer (`-EFAULT`, nothing written) is
  that of the `USER_PTR_MAX` profile (v6.13+). v6.8's `access_ok` is a sign test,
  so there a band `oset` is partly written before `-EFAULT`; probes on a 6.8
  host are outside the profile for that band.

## Native numbering and ABI boundary

`NativeX86.numbers` pairs all 90 LPS arms with Linux v6.12 native x86 numbers.
`NativeX86.table` uses the actual LPS `SpecArm` definitions. Machine state keeps
raw native RAX: the old synthetic `x86Renumber` path remains a legacy option.
The selected arm and the refusal classifier both receive the corresponding
reference number; adapting only dispatch would leave refusal/budget classifiers
testing the wrong numbers.

Only `reviewedNames` is enabled through this generic adapter. Other families
remain pending until their x86 ABI has been reviewed or a native override is
supplied. In particular, x86 `stat`, `epoll_event` and `sigaction` have distinct
layouts. Linux x86-64 `clone` swaps the fourth and fifth arguments relative to
RISC-V (`CLONE_BACKWARDS`); the pinned LPS fork-only arm reads only flags, so
that particular difference is inert for its current specification. A matching
number and name do not establish ABI compatibility.

The native review gate now also includes the five scalar FsCtl calls
`fcntl`, `ioctl`, `flock`, `fsync`, `fdatasync`. These remain pending in
the default table until their reference translations are integrated. See
[the native family integration notes](LPSX86NativeFamilies.md) for the review
scope and opt-in layout-aware installer.

`Machines.X86ArchPrctl` adds native syscall 158 for `ARCH_SET_FS`: a base below
the fixed four-level bound succeeds and sets FS from the original RSI; a base
at or above it returns `EPERM`. Other operations remain explicitly unmodeled.
The success bridge and failure-preserves-FS theorem connect the spec to the
actual native machine effect hook. This does not model five-level kernels or
FS selectors.

`NativeX86Budget` adapts allocation-refusal diagnostics too: native `brk(12)`
and `mmap(9)` must reach reference classifiers 214 and 222. Concrete zero-budget
controls prove refusals, while break queries and lazy `MAP_NORESERVE` requests
are not incorrectly classified as immediate allocation refusals. The legacy
`BudgetRefusedAt` remains reference-numbered. `Machines.X86NativeLaunch`
selects the native table, refusal filter, budget diagnostic and stack together.

## Machine access reports and static launch

`Machines.x86ExtNative` and `Machines.x86Wire` report the consumed instruction
fetch and the data ranges read or written on successful execution. Their full
results agree on `X86Wire.CommonAt`, including faults and syscalls. Controls
cover fetched loads, unconditional CMOV source reads, LEA without data reads,
invalid addresses, native syscall numbers, and code/data lazy-page charging.
Already materialized pages are not charged twice. Failed instructions do not
return a partially updated state. REP/string instructions remain unmodeled.

The deterministic native adapter requires all six status flags to be defined
when SYSCALL saves RFLAGS to R11. For example, XOR-zeroing leaves AF undefined.
`Machines.x86WithFlagOracle` is an additional option that completes only unknown
flags using a supplied sequence of Boolean choices. It preserves every known
flag and realizes every compatible total valuation; fully defined syscall
behavior projects to the native behavior. Client claims covering all completions
must quantify over **every oracle**. Controls show both AF choices execute and
produce distinct R11 values. This is a scoped syscall-choice model, not full
undefined-flag treatment for all instructions or a hardware refinement proof.

`Machines.X86Launch` supplies a separate 20-entry x86 auxv, platform string,
16-byte stack alignment and the explicit architecture profile to the real LPS
initialization/transition relation. The scoped launch is fixed-address static
ELF64 ET_EXEC, initially zero FS/RDX, with no dynamic loader, vDSO or optional
hardware features advertised. A concrete 129-byte ELF has byte/header/program-
header checks, an inhabited launch, startup-register facts and malformed-machine,
misalignment and address-bound rejection controls. `ELFImage` and `ELFImageX86`
now provide a checked general byte-to-snapshot option for this fixed static
ET_EXEC profile, proving exact file/BSS slices and existing snapshot validity.
Their controls recover the same fixture and an actual guarded launch. Corpus
application and large-image performance remain separate work.

`StatementProfile` makes initialization, syscalls, refusal interpretation,
allocation classification and input domains explicit alongside the ISA. Its
four agreement forms are definitionally equal to the literal reference Shapes
when instantiated with the reference profile. `NativeX86Statements` selects
the native stack, snapshot and System instead. Its controls exhibit a valid
domain and an exit trace, and distinguish native exit 60 from reference dispatch.
These are statement APIs and small execution proofs, not corpus agreement proofs.

`X86LaunchExecution` proves an actual four-transition LPS path from that
initialized ELF through MOV, SUB, SYSCALL and native exit 0, under any refusal
filter. It supplies a finite normal execution and an observable exit trace,
and refutes the universal all-error observation. This is an existence result;
universal error freedom is a separate theorem. Code reads are proved through
symbolic loader/frame rules, without evaluating the 8 MiB stack map in Lean.

## Concrete musl coverage

[The pinned static-musl checksum executable](../examples/verification-projects/x86-musl-startup/README.md)
records an actual QEMU run reaching `main` and exiting zero. Of its 341 distinct
reached addresses, 337 decode with the observed length in Wire, three are native
syscall boundaries, and one is the unsupported REP STOSQ spelling `f3 48 ab`.
The trace contains 658 instruction attempts; REP STOSQ first appears at attempt
31 in `__init_libc`. A Lean leaf checks the preceding 31 byte spans and the REP
decoder rejection. This is external execution evidence with checked local
decoding, not an execution or hardware-correspondence theorem. Closing this
decode gap still requires a suitable undefined-flag option and an actual Lean
startup proof. The coverage analyzer labels environment and exit status as
unverified if execution metadata is absent.

An additive `x86WireDf0RepStosq` option now handles that exact REP spelling as
one checked eight-byte store per microstep. It preserves every old modeled
success/fault, with controls for zero count, progress, memory framing and faults
after an earlier iteration. DF=0 is an explicit profile assumption; DF is absent
from the state and CLD/STD remain unsupported. `X86FlagOracle` factors the old
syscall-choice wrapper over a native stepper, with canonical equality by `rfl`.
`X86WireFlagOracle` supplies Wire and Wire+REP instances. Choices fill only the
six arithmetic-status flags at SYSCALL, preserving known values; all-completions
claims must quantify over every oracle. Neither addition establishes whole-run
or hardware refinement. The pinned coverage report continues to describe the
unchanged baseline Wire decoder.

### The pinned executable under the Lean launch

`Machines.X86MuslStartup` embeds the 16,256 pinned bytes
(`Machines.X86MuslStartupBytes`, generated and checked by
`tools/verification-projects/x86_musl_lean_bytes.py`). It proves that
`ELFImage.loadX86` accepts them for `x86WireDf0RepStosq` and the flag-oracle
wrapper, that a launch with argv `checksum` and an empty environment satisfies
the native launch guards, and that the first actual LPS transition
(`xor %rbp,%rbp` at 0x401062) retires under any syscall specification and
refusal filter. The first-step theorem is proved for the deterministic option
(`first_process_step`) and, for every oracle, for the flag-oracle option
(`first_process_step_oracle`). `main`'s first bytes are fetchable in the same
launch memory.

By the disassembly, `test %eax,%eax` at 0x401744 is the last flag writer before
the `set_tid_address` SYSCALL at 0x401768, and logic operations leave AF
undefined (`logicFlags_undefined`). Given that, `syscall_unmodeled_of_adjust`
shows the deterministic option is `unmodeled` at that SYSCALL, so the
reachability statements use the flag-oracle option.

The remaining obstacle is proof engineering. `Std.ExtHashMap` operations do not
reduce in the kernel, and the launch eagerly backs an 8 MiB stack. The 532-attempt
path (including 38 REP STOSQ microsteps) therefore cannot be checked by one
`decide`. It needs per-step symbolic lemmas, or a reflective executor over a
list-based memory view with a proved simulation lemma. Image reads already go
through `segmentsView` (`ProcessMemorySupport`).
## ELF convention

The parity lanes follow this ELF representation convention:
file-level facts are stated on the lossless CST `Formats.ELF.Cst.File`, linked
to the pinned bytes by the chunked check `Cst.File.IsCST` and its soundness
theorem. The loaded image is LPS `Image`, built from the CST by
`ELFImage.fromCst` and `fromCstX86` (`ELFImageCst`). Raw-byte
proofs remain where they already exist, and each is tied to the CST by a theorem.

| Statement | Layer used |
| --- | --- |
| `X86LaunchControls` `header_from_bytes`, `programHeaders_from_bytes`, `entry_code_from_bytes` | bytes (`decide +kernel`); kept, and re-derived from `IsCST` in `X86LaunchCst` (`header_from_cst`, `programHeaders_from_cst`, `entry_code_from_cst`) |
| `X86LaunchControls` snapshot, launch and startup facts; `X86LaunchExecution` four-step exit | the hand-written `Snapshot`; `CstControls.fromCstX86_fixture` proves it is the CST's snapshot, and `X86LaunchCst` restates validity, launch and the exit path for every snapshot `fromCstX86` returns |
| `ELFImageControls` loader controls and rejections | bytes through the `Formats.ELF` readers (`parse`, `loadX86`); `CstControls.load_eq`, `loadX86_eq` equate them with the CST loader |
| `ELFImageCstControls` | CST + `IsCST` + `fromCst` (the standard) |
| `Examples.MuslChecksum` (the static-musl checksum ELF, 16,256 bytes) | CST + `IsCST` (4 chunks of at most 4 KiB) + `fromCst`: `fromCst_eq`, `image_shape`, `validSnapshot`; the byte-loader statements `load_eq`, `loadX86_eq` are corollaries |
| `X86.Ext.Wire.MuslStartupCoverage` (local decoding of the reached spans) | bytes; not yet restated on the CST's code view |
| probe kit (`parity/lps-probes`, `Probes.Kit`) | raw byte lists (`Probe.fileBytes`) checked by the readers; not yet converted |
`X86MuslRun.reaches_main` (`Machines/X86MuslRunMain.lean`) proves that the
actual LPS run relation takes the flag-oracle launch to `main` (0x401030) in 542
transitions with no events, under `NativeX86.extendedSyscallSpec` (the native
table plus `arch_prctl(ARCH_SET_FS)`), for every platform, oracle and spurious
refusal configuration. The run is generated from `lps-run.trace` by
`tools/verification-projects/x86_musl_lean_run.py`; each step is a theorem
about the actual step function. The states after `set_tid_address` are
functions of a symbolic thread id, so `star_main` holds for every id in
`(0, 2^22)`; the id reaches only RAX (overwritten two instructions later) and
`td->tid`, and every fetch and read on the path is checked away from it.
`reaches_main_facts` adds the calling state of `main(argc, argv, envp)`
(`MainFacts`), for every thread id.

`X86MuslRunUniversal.every_execution` is the universal form: every execution
from the launch is a silent prefix of this path, or has entered `main` in
`mainCfg … tid` for a valid `tid`, with `MainFacts tid`. Nothing before `main`
is stuck, errors or diverges (`Funnel`; `errors_after_main`,
`unmodeled_after_main`, `no_divergence_before_main`). The proof reads the run as
a funnel: each instruction step is the unique `SStep` of its configuration, and
at the two syscalls every specified outcome is enumerated (`arch_prctl` has one,
0; `set_tid_address` one per thread id). It holds for every refusal filter that
refuses neither startup syscall. Three filters are instantiated: LPS's `run`
reading `noFilter` (`every_execution_run`), the reference-numbered
`NativeX86.defaultRefusalFilter cfg` (`every_execution_default`), and
`nativeScfgFilter cfg`, which is `spuriousRefusalCfg extendedSyscallSpec cfg`
on native numbers (`every_execution_scfg`; `startupNotRefused_spurious` holds
for every specification). No Lean definition names one of these as the native
x86 `run_scfg`, and a filter that refuses a startup outcome is outside these
theorems. Neither syscall has an
injected-failure family (`startup_no_injected_family`) and neither
specification has a failure outcome here, so no refusal ending (such as musl's
`a_crash` after a failed `__set_thread_area`) is reachable. Under the plain
native table without the `arch_prctl` arm (`extended_agrees` relates the two),
every execution reaches the pending `arch_prctl`, whose only step is the
unmodeled `SError` (`native_every_execution`, `native_reaches_unmodeled`).

These statements fix one launch: argv `checksum`, an empty environment and one
`ExecEntry` (`sp = 0x7fffffffe000`, AT_RANDOM bytes and slack all zero). They
are about `extendedSyscallSpec`, not the integration hub's
`NativeX86.All.nativeTable`, which is not on this base.

**The launch is a minimal synthetic SysV profile, not Linux's.** "Every
execution" above means every execution from `X86Launch.entryStack`, which
differs from Linux `create_elf_tables` (`fs/binfmt_elf.c`, checked against
6.8):

* Layout: Linux puts the argv/envp strings and the separate execfn string at
  the top, then the `arch_align_stack` gap, the platform string `x86_64`, the
  16 AT_RANDOM bytes directly below it, and `STACK_ROUND` padding above
  auxv/envp/argv/argc. The model puts the strings directly after auxv, then the
  platform string, padding, and the random bytes last (highest).
* AT_EXECFN points at the argv[0] copy; Linux points it at `bprm->exec`, the
  execve filename.
* Entries: the model has 20 entries in its own order. Linux x86-64 always
  emits AT_MINSIGSTKSZ, emits AT_RSEQ_FEATURE_SIZE/AT_RSEQ_ALIGN with
  `CONFIG_RSEQ` (6.3+), and emits AT_SYSINFO_EHDR only with a vDSO, nonzero;
  the model emits `(AT_SYSINFO_EHDR, 0)`. Linux has 22-23 entries.
* AT_HWCAP is `inp.hwcap = 0`; Linux uses CPUID.1:EDX, never 0 on x86-64, and
  the model does not tie it to the `platform` parameter. AT_HWCAP2 is 0; Linux
  sets the FSGSBASE bit where supported.
* The `ExecEntry` is fixed: no `arch_align_stack` offset, zero random bytes and
  slack.

musl's `__init_libc` walks auxv once per entry, so the 542-step path does not
carry over to a Linux-shaped auxv without being regenerated. A Linux-shaped
launch option, and quantifying the run over `ExecEntry` draws (random bytes,
slack, an aligned `sp` range) and auxv values with symbolic overlays as for the
thread id, are open work.

### Start-up loops over every launch

Generalizing `reaches_main` from one launch to every launch needs the start-up
loops whose trip count or addresses depend on the launch. `Machines.X86MuslLoops`
steps the actual flag-oracle Wire+REP option for a symbolic core and memory, with
instructions fetched from a loaded code slice. It also defines `BackClosed`
properties: both a `Star` run and `Leads` over the actual `SStep` relation
(`XStep`, where an error is a dead end) are back-closed. Each summary is proved once
for every back-closed property:

| Loop | Code | Summary |
| --- | --- | --- |
| envp scan | 0x4011ea–0x401216 | `Envp.scan`: RAX = `8 * #envp + 8`, for every environment |
| auxiliary vector into `aux[38]` | 0x401216–0x40124b | `Auxv.run`: `libc.auxv`, `aux` = `auxFold` of the pairs |
| `argv[0]` basename | 0x40127a–0x4012bb | `Progname.scan`: `__progname = pn + slashOff s` |
| REP STOSQ clear of `aux` | 0x4011dd | `Memset.memset`: any count, value and destination |

`X86MuslLoopsEvery` states each summary as `Leads` (every execution reaches the
exit with the summarized registers and memory) and as `Star`.
`X86MuslLoopsPinned` checks every hypothesis on the pinned run's states, together
with the end states the summaries predict. There is no argv walk on this path:
`__libc_start_main` computes `envp = argv + argc + 1` directly.

## Address profiles and syscall-family handoff

`AddressSpaceProfile` is carried by `Model` and selected by `UserIsa`. Native
x86 uses `TASK_SIZE = 0x7ffffffff000`. The default remains the historical Sv48
profile for **every** `VaSize`, with initialization equality proved by `rfl`.
Explicit Sv39/Sv57 profiles are additional options, not silent behavior changes.

The syscall-family integration must use `m.addressSpace` at these sites before
claiming native address-bound parity:

- `Syscall.modeledRwRange`: add a profile-taking counterpart and legacy wrapper.
- `Syscall.accessOkZero`: select the model's address profile.
- `Sys/ReadWrite`: direct `accessOkb`, `modeledRwRange` and write-range gates.
- `Sys/Kernel`: `uname`/`getrandom` user-buffer gates.
- `Sys/Mmap`: `munmapSpec`'s global `taskSize` guard must read the model profile.

This milestone does not treat buffer-range inclusion as whole-process refinement.

## x86 launch windows against Linux ASLR

`Machines.X86LaunchAslr` states, as Lean sets parameterised by `LinuxAslrConfig`
(`randomize_va_space` as any integer, `ADDR_NO_RANDOMIZE`, `mmap_rnd_bits`, the stack
rlimit, `stack_guard_gap`, legacy layout), the placements Linux x86-64 v6.13-v6.18
produces for a static ET_EXEC launch, and proves each `X86Launch.ValidEntry` window
contains them. Widening a window is sound for universal statements; a window that is too
narrow would make them silently exclude real launches. Line numbers are v6.18 (checked
against the v6.13 and v6.18 sources and the local 6.8 tree; the quantities agree).

| Window | Linux range | Containment | Change |
| --- | --- | --- | --- |
| stack `x86LaunchBounds.spWindowLo..Hi`, 16-aligned | stack top `STACK_TOP - r*4096 - a*4096`, `r <= 0x3fffff` (mm/util.c:341-355, arch/x86/include/asm/elf.h:328-329), `a <= 2` from `arch_align_stack` + `PAGE_ALIGN` (arch/x86/kernel/process.c:1019-1023, fs/exec.c:635-636); `rsp` within `linuxEntryReach` below it (mm/vma_exec.c:150, fs/exec.c:1831-1840, fs/binfmt_elf.c:149-150,192-228,300-303) | `linuxSp_mem_window` | **widened**: the low end was `TASK_SIZE - 2 GiB` (riscv64's 1 GiB stack randomization plus slack), which excluded most x86-64 placements (`old_sp_window_excluded_linux`); it is now `TASK_SIZE - (0x3fffff + 2) * 4096 - 2 GiB` |
| brk `ValidBrk` (`reservedTop .. + brk_aslr_max`) | `ELF_PAGEALIGN(elf_brk)`, or with `randomize_va_space > 1` that plus one page plus `randomize_page(_, SZ_1G)` (fs/binfmt_elf.c:93,1033,1240-1242,1330-1340, arch/x86/kernel/process.c:1026-1032, mm/util.c:371-387) | `linuxBrk_mem_window`, `reservedTop_eq_linuxBrkStart` | none: LPS's `brk_aslr_max = 1 GiB` equals x86-64's `SZ_1G`; the top is attained (`linuxBrk_top_attained`) |
| mmap base `[64 KiB, TASK_SIZE - 128 MiB]`, page-aligned | top-down `PAGE_ALIGN(task_size - clamp(gap, 128 MiB, task_size/6*5) - rnd)` or legacy `PAGE_ALIGN(task_size/3) + rnd`, `rnd < 2^mmap_rnd_bits` pages, bits `<= 32` (arch/x86/mm/mmap.c:41-131, arch/x86/include/asm/processor.h:677, arch/x86/Kconfig:354-360, mm/mmap.c:941-954) | `linuxMmapBase_mem_window` | none |

`randomize_va_space = 0` (or `ADDR_NO_RANDOMIZE`, or `norandmaps`) gives one point of
each window (`linuxStackTops_unrandomized`, `linuxBrks_unrandomized`,
`linuxMmapBases_unrandomized`; with the default rlimit the base is exactly the window's top,
`defaultConfig_unrandomized_mmapBase`). `load_elf_binary` reads a snapshot of the sysctl
while `arch_align_stack` reads it live; the stack theorem holds for every shift in the
randomized range (`stackTop_mem_window`), so that race is covered. `linuxEntry_valid`
combines the three: a Linux placement is a valid entry when the two non-window premises
hold (the model's entry block fits below `TASK_SIZE`; the image lies below `rsp - 8 MiB`).

Remaining gaps, recorded rather than proved: (1) the fit premise compares the model's
entry block with `TASK_SIZE`, not with Linux's stack top; Linux's block is larger than the
model's in the default configuration (23 auxv entries with the vDSO and rseq against the
model's 20), so a Linux `rsp` satisfies it there, but this is argued, not proved, and it
can fail by a few bytes for a kernel booted with `vdso=0` and without `CONFIG_RSEQ`;
(2) with `legacy_va_layout`, Linux allocates mmaps bottom-up from the base, which the model's
allocator does not represent: the base is in the window, the allocation direction is not
modelled; (3) the witness entry of `NativeX86.All.validEntry_witness` stays at
`TASK_SIZE - 2 GiB` (`spWitnessLevel`), so its image premise is unchanged by the widening.

## Reality probes

`Silmaril/Process/LPS/Probes` connects the launch to Linux runs of tiny static
ELFs (`examples/verification-projects/theorem-dev/lps-probes`). Each probe is
recorded under strace, and its generated Lean data module holds the ELF bytes
and the observation. The proofs then show that the model admits the observed
raw syscalls, output and exit status (`Probe.Admits`). They also prove a
universal `Omni.Exec` statement: either exactly that behaviour
(`Probe.Determined`) or an explicit list of reference-sanctioned alternatives,
such as the short channel write for `write_hello`. Each mutant has a refutation.
`lps_probes.py check` verifies that sources, pins, JSON, generated Lean data,
proof modules and live runs agree.

The error and edge-case probes (`write_efault`, `write_closed`, `close_twice`,
`write_zero`, `read_badfd`) are each determined by one reference branch
(`KitReturns.lean`). `read_echo` reads stdin into its own writable image and
echoes it (`KitMemory.lean`). Its universal statement holds for every stdin
stream: the output is a prefix of what was read, which is a prefix of stdin,
with the reference short read and short write as the named alternatives.

## Validation and remaining work

Targeted Lean compilation checks the new definitions and their positive,
boundary and negative controls. Full build and kernel replay belong to CI.
The compiled helpers also supply inhabited legacy entries, classifier
corollaries and the finite/terminating Omni core; see [the shape audit](LPSShapesParity.md).
This is not a claim of full syscall, x86 instruction, dynamic-loader, or
sanitizer-runtime coverage.

Full semantic parity additionally needs the remaining family translations,
architecture-specific layouts, process/machine memory correspondence, the
missing reference theorem helpers, and instruction/runtime coverage for the
chosen executable corpus. The machine reporter is a checked Lean definition
reviewed against our executor; it is not a hardware-correctness certificate.

The selected upstream source snapshot, Linux syscall table and machine-readable
ledger are checked offline by `tools/verification-projects/lps_x86_parity.py`.
Its completion gate deliberately rejects this milestone while those obligations
remain. Hashes and declaration/status checks are source-integrity evidence;
they do not prove source-to-Lean equivalence.
