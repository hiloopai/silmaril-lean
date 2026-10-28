# Concrete musl startup coverage

`checksum.elf` is a pinned Linux x86-64 SysV, static, non-PIE executable. It uses
unmodified musl 1.2.5 startup, computes a wrapping integer checksum in `main`, and
returns zero. `build.json` pins source/archive/artifact hashes, GCC version and
flags. `MUSL-COPYRIGHT` accompanies the linked musl code.

The final ELF SHA-256 is
`0ef7a89e9e1e07386fb608d06255b5523081ff9a48e0aa4c69a42e2311ed4ad0`.
Two builds in different directories produced these same bytes after stripping
musl assembly debug information; instruction bytes and ordinary symbols remain.
This checks reproducibility with the recorded compiler, rather than pinning a
complete compiler container. Build output directories cache musl; use a fresh
directory when changing its version, compiler, or flags.

## What was reached

`execution.json` records QEMU 8.2.2, an empty environment, fixed guest argv0
`checksum`, the ELF/trace hashes, the exact invocation,
and exit status zero. `checksum.qemu.trace` uses `-singlestep` and
`-d in_asm,exec,nochain`. This gives **instruction attempts**, including repeated
attempts at REP instructions, rather than counting every statically disassembled
instruction as executed. It is concrete external execution evidence, not a Lean
execution or hardware-refinement theorem.

The recorded run has 658 attempts at 341 distinct instruction addresses. It
reaches `main` at attempt 532. The trace records these native x86 syscalls:

| Syscall | Observed result | Existing model requirement |
| --- | --- | --- |
| `arch_prctl(ARCH_SET_FS, ...)` | 0 | Optional `X86ArchPrctl` extension |
| `set_tid_address(...)` | positive TID | Translated native syscall arm |
| `exit_group(0)` | termination | Translated native syscall arm |

`coverage.json` checks every reached byte span against a file-backed ELF
`PT_LOAD`, then runs the current Lean Wire decoder through kernel `#reduce`:

* 337 addresses decode with the exact observed length, including ENDBR64.
* Three addresses contain `0f 05`. The native `UserIsa` handles these separately
  from Wire decoding; actual execution also needs the syscall table and suitable
  flags (or the explicit undefined-flag choice adapter).
* The only remaining reached instruction-decoder gap is **REP STOSQ**:
  `f3 48 ab`, PC `0x4011dd`, in `__init_libc`. It is first attempted at index 31,
  before `main`; QEMU logs 38 attempts at that PC.

`Silmaril/X86/Ext/Wire/MuslStartupCoverage.lean` proves exact local decoding for
the 31 preceding reached byte spans and proves that this REP STOSQ spelling is
rejected. No theorem claims that all the accepted instructions can execute on
this ELF under Lean: decoding alone does not check state, data accesses, flags,
syscalls, the loader, or memory-accounting invariants.

## Reproduce or extend

On Linux, with `x86_64-linux-gnu-gcc`, matching binutils, Python 3 and QEMU user
mode installed, run from the repository root:

```sh
bash tools/verification-projects/x86_musl_build.sh /tmp/musl-checksum
python3 tools/verification-projects/x86_musl_trace.py run \
  /tmp/musl-checksum/checksum.elf --output /tmp/musl-checksum
python3 tools/verification-projects/x86_musl_trace.py analyze \
  /tmp/musl-checksum --lean lean
python3 tools/verification-projects/test_x86_musl_trace.py
```

The analyzer inherits `LEAN_PATH`, so use `lake env python3 ...` in an ordinary
configured checkout. The build accepts an already downloaded archive as its
second argument, checks its pinned SHA-256, and supports `X86_MUSL_CC`,
`X86_MUSL_AR`, `X86_MUSL_RANLIB`, `X86_MUSL_OBJDUMP`, `X86_MUSL_READELF`, and
`X86_MUSL_JOBS`. The trace runner and analyzer are separate extractors; neither
changes the generic project format or other architecture pipelines.

`Machines.X86RepStosq` now provides an additive REP STOSQ option with explicit
DF=0 scope, one checked eight-byte store per microstep, RCX progress, and
per-iteration memory-access reporting. Its controls prove fetched-byte success,
zero-count behavior, destination faults and persistence of an earlier completed
iteration. Every old modeled success or fault is preserved. DF is not represented
in the state: DF=0 is a profile assumption, and CLD/STD remain unsupported.

`Machines.X86WireFlagOracle` optionally wraps Wire or Wire+REP in the reusable
syscall flag oracle. It completes only the six arithmetic-status flags, only
at a fetched SYSCALL; known flags remain unchanged. Coverage of all completions
requires quantification over every oracle. Undefined-flag branches before a
syscall can still decline. REP microsteps consume no choices. This closes the
observed decode gap with an additional scoped model, without changing the
baseline `coverage.json` or proving musl startup in Lean. REP microsteps are not
claimed to correspond one-for-one with retired hardware instructions.

`Machines.X86MuslStartup` now loads these exact bytes through the checked Lean
ELF loader and launches them under the Wire+REP option. `X86MuslRun.reaches_main`
proves that an execution of the flag-oracle option reaches `main`;
`X86MuslRunUniversal.every_execution` proves that every execution does, for every
thread id `set_tid_address` may return, entering `main` with the facts of
`MainFacts` (argc, argv, envp, stack alignment, return address, FS base, `td->tid`).
These theorems start from one fixed launch, `X86Launch.entryStack`: a minimal
synthetic SysV stack and 20-entry auxv, not Linux's `create_elf_tables` layout
(string placement, AT_EXECFN, AT_MINSIGSTKSZ/AT_RSEQ_*, HWCAP and AT_RANDOM
differ), with one fixed `ExecEntry`.
See [`docs/LPSX86Parity.md`](../../../docs/LPSX86Parity.md).
