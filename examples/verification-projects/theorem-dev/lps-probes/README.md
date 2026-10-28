# LPS reality probes (x86-64)

A probe is a tiny static x86-64 Linux ELF, written by hand in GNU as with no libc.
Each probe connects three things:

1. **Reality.** `tools/verification-projects/lps_probes.py` builds the probe and runs it
   on Linux under `strace -f -X raw -e trace=all`, in a fresh temporary directory that
   holds only the declared input files and stdin. It records the raw syscalls (number,
   raw arguments, raw return), the bytes written to stdout and stderr, and the exit status
   or killing signal in `probes/<name>.json`.
2. **Lean.** `lps_probes.py gen-lean` writes `Silmaril/Process/LPS/Probes/Data/<Name>.lean`
   with the ELF bytes, the parsed header and program header, and the recorded observation
   (`observed`). The proof module (`Silmaril/Process/LPS/Probes/<Module>.lean`) loads
   *those bytes* through the static x86 launch (`Machines.X86Launch`) and proves its theorems
   against *that* `observed` value.
3. **Link.** `lps_probes.py check` fails unless sources → bytes → `SHA256SUMS` → JSON →
   generated Lean data → proof module → live runs all agree, on every available backend.
   The JSON's `lean` field names the proof module and its theorems. The check verifies
   that the module exists, imports and uses the generated data module, states every
   listed theorem, and contains no `sorry`, `axiom` or `native_decide`. For a mutant
   (`mutantOf`), the check also requires the recorded Linux behaviour to differ from the
   original's.

| Probe | Source | Linux (recorded) | Lean |
|---|---|---|---|
| `exit42` | `mov $60,%eax; mov $42,%edi; syscall` | `exit(0x2a)`, status 42 | `Probes.Exit42`: `admits`, `determined` (every run, any refusal filter), `no_error`, `no_unmodeled` |
| `exit43` | mutant: status 43 | `exit(0x2b)`, status 43 | `Probes.Exit43`: `admits`, `not_determined_42` |
| `write_hello` | `write(1, "hello\n", 6); exit(0)` | `write(1, 0x40009a, 6) = 6`, stdout `hello\n`, status 0 | `Probes.WriteHello`: `admits`, `exec`, `sound` (full write or reference short write, then exit 0), `no_error` |
| `write_hello5` | mutant: length 5 | `write(1, 0x40009a, 5) = 5`, stdout `hello`, status 0 | `Probes.WriteHello5`: `admits`, `not_traces_original` |
| `write_efault` | `write(1, 0x10, 6); exit(0 - rax)` | `write = -14` (EFAULT), status 14 | `Probes.WriteEfault`: `determined`, `sound`, `admits`, `no_error` |
| `write_efault_ok` | mutant: buffer = the message | stdout `hello\n`, status 250 | `Probes.WriteEfaultOk`: `admits`, `not_determined_original` |
| `write_closed` | `close(1); write(1, msg, 6); exit(0 - rax)` | `close = 0`, `write = -9` (EBADF), status 9 | `Probes.WriteClosed`: `determined`, `sound`, `admits`, `no_error` |
| `write_closed2` | mutant: `close(2)` | stdout `hello\n`, status 250 | `Probes.WriteClosed2`: `admits`, `not_determined_original` |
| `close_twice` | `close(0); close(0); exit(0 - rax)` | `0`, then `-9` (EBADF), status 9 | `Probes.CloseTwice`: `determined`, `sound`, `admits`, `no_error` |
| `close_twice1` | mutant: second close of fd 1 | `0`, `0`, status 0 | `Probes.CloseTwice1`: `admits`, `not_determined_original` |
| `write_zero` | `write(1, msg, 0); exit(rax)` | `write = 0`, no output, status 0 | `Probes.WriteZero`: `determined`, `sound`, `admits`, `no_error` |
| `write_zero1` | mutant: length 1 | stdout `h`, status 1 | `Probes.WriteZero1`: `admits`, `not_determined_original` |
| `read_badfd` (rwx) | `read(99, buf, 6); exit(0 - rax)` | `read = -9` (EBADF), status 9 | `Probes.ReadBadfd`: `determined`, `sound`, `admits`, `no_error` |
| `read_badfd0` (rwx) | mutant: fd 0, empty stdin | `read = 0`, status 0 | `Probes.ReadBadfd0`: `admits`, `not_determined_original` |
| `read_echo` (rwx, stdin `ping\n`) | `n = read(0, buf, 16); write(1, buf, n); exit(0)` | `read = 5`, `write = 5`, stdout `ping\n`, status 0 | `Probes.ReadEcho`: `exec_any` (every stdin), `exec`, `sound`, `admits`, `no_error` |
| `read_echo2` (rwx, stdin `ping\n`) | mutant: read length 2 | stdout `pi`, status 0 | `Probes.ReadEcho2`: `exec_any`, `admits`, `not_traces_original` |
| `open_read` | `openat(AT_FDCWD, "in.txt", O_RDONLY)`; `read(fd, rsp, 64)`; `write(1, rsp, n)`; `close`; `exit(0)`, with `in.txt` = `hi\n` | `openat = 3`, `read(3, sp, 64) = 3`, `write(1, sp, 3) = 3`, `close(3) = 0`, stdout `hi\n`, status 0, files unchanged | `Probes.OpenRead`: `admits`, `exec`/`sound` (`ReadThenPrint`: `full`, `shortWrite`, `openFailed` with an injected `openat` errno), `no_error` |
| `open_read_name` | mutant: name `in.txu` | `openat = -ENOENT`, `read`/`close = -EBADF`, nothing printed, status 0 | `Probes.OpenReadName`: `determined`, `admits`, `not_traces_original` |
| `open_read_wr` | mutant: `write` (1) instead of `read` (0) on the `O_RDONLY` descriptor | `write(3, sp, 64) = -EBADF`, nothing printed, status 0 | `Probes.OpenReadWr`: `determined`, `admits`, `not_traces_original` |
| `open_missing` | `openat(AT_FDCWD, "nofile", O_RDONLY)`; `exit(-ret)` | `openat = -ENOENT`, status 2 | `Probes.OpenMissing`: `determined`, `sound`, `admits`, `no_error` |
| `open_efault` | mutant: path pointer `0x1000` (unmapped) | `openat = -EFAULT`, status 14 | `Probes.OpenEfault`: `determined`, `admits`, `not_determined_missing` |
| `open_create` | `openat(AT_FDCWD, "out.txt", O_WRONLY\|O_CREAT\|O_TRUNC, 0644)`; `write(fd, "ok", 2)`; `close`; `exit(2)` | `openat = 3`, `write = 2`, `close = 0`, status 2; final files `out.txt` = `ok` | `Probes.OpenCreate`: `admits` (with that final file system), `exec`/`sound` (`CreateThenExit`: `created`, `injected`), `no_error` |
| `open_create_ko` | mutant: writes `ko` | same calls; final files `out.txt` = `ko` | `Probes.OpenCreateKo`: `admits`, `not_sound_original` |
| `open_legacy` | legacy `open("in.txt", O_RDONLY)` (number 2, used by musl); `exit(fd)` | `open = 3`, status 3 | `Probes.OpenLegacy`: `admits`, `exec`/`sound` (`OpenStatus`: `opened`, `injected`), `no_error`, `hub_open_translated`, `previousHub_unmodeled` |
| `identity` | `getpid`, `gettid`, `set_tid_address(0)`, `getuid`, `geteuid`; exit with the differences | pid = tid = set_tid_address, uid = euid = 1000, status 0 | `Probes.Identity`: `determined` (exit 0 for every thread id the model chooses), `sound`, `admits` (Linux's id and uid), `no_error` |
| `identity1` | mutant: final `add $0` → `add $1` | status 1 | `Probes.Identity1`: `admits`, `not_determined_original` |
| `getrandom8` | `getrandom(rsp, 8, 0)`; exit with the return | `getrandom(sp, 8, 0) = 8`, status 8 | `Probes.Getrandom`: `determined`, `sound`, `every_bytes` (every 8-byte string is delivered by some run), `admits`, `no_error` |
| `getrandom_badflags` | mutant: flags 0 → 0xdead | `-EINVAL`, status 234 | `Probes.GetrandomBadflags`: `unmodeled_at_call` (fail closed, any filter), `unmodeled`, `not_admits`, `not_determined_original` |
| `unknown_syscall` | call 999; exit with the return | `-ENOSYS`, status 218 | `Probes.UnknownSyscall`: `unmodeled_at_call` (fail closed, any filter), `unmodeled`, `not_admits`, `any_filter` |
| `unknown_exit_group` | mutant: 999 → 231 (`exit_group`) | `exit_group(0)`, status 0 | `Probes.UnknownExitGroup`: `determined`, `admits`, `not_stops`, `exit_group_iff_exit` |
| `arch_fs` | `arch_prctl(ARCH_SET_FS, 0x400000)`; exit with `%fs:0` | `= 0`, status 127 (ELF magic 0x7f) | `Probes.ArchFs`: `determined`, `sound`, `admits`, `no_error` |
| `arch_fs1` | mutant: base 0x400001 | status 69 (`E`) | `Probes.ArchFs1`: `admits`, `not_determined_original` |
| `arch_getfs` | `ARCH_SET_FS`, then `ARCH_GET_FS` into the stack; exit with the value | reads back 0x400078, status 120 | `Probes.ArchGetfs`: `unmodeled_at_get` (`ARCH_GET_FS` is not modeled), `unmodeled`, `not_admits` |
| `arch_getfs_exit` | mutant: second call → `exit(0x1003)` | status 3 | `Probes.ArchGetfsExit`: `determined`, `admits`, `not_stops` |
| `lite_*` | GCC -O2 builds of `examples/coreutils-lite/*.c` | see each JSON | `Problems.CoreutilsLite.TrueFalse` (every launch, every flag oracle) and `.EchoCat` (specs; open) |

Values that differ between runs or backends (process ids, the user id, a stack address)
are declared in the JSON's `hostDependent` list. Live runs must produce them but do not
compare their values; the JSON keeps the recorded value, and the proofs take the launch
parameter (`ProcInput.uid`, `ExecEntry.sp`) or the model's choice (the thread id) from it.
The native backend disables address randomization (`ADDR_NO_RANDOMIZE`), so the stack
pointer is reproducible there.

## Final file systems and stack arguments

A probe's `inputs.files` populate both the harness's work directory and the launch file
system (`harnessInputFiles inputFiles`). After the run the harness reads back every
regular file in the work directory except the probe into `expected.files`, and `check`
compares it across backends; the Lean `observed.files` is the file system of the exit
event. Arguments that point into the randomized entry stack are listed in `stackArgs`
and recorded as `"sp"`; the Lean side reads them as `probe.entry.sp`. A backend can be
skipped for one probe only with a reason (`skipBackends`), and at least one must remain.

## Gaps found by the file probes

| Gap | Kind | Status |
|---|---|---|
| Legacy x86-64 `open` (number 2) had no row in the hub's previous native table `NativeX86.extendedTable`, so the call was `unmodeled` there (`OpenLegacy.previousHub_unmodeled`). Linux opens the file. | missing feature | **Closed in the hub** (#3534, #3564): `NativeX86.All.nativeTable` installs fs-io's `openSpecX86` as an extension arm (`OpenLegacy.hub_open_translated`), and every probe theorem is about that table (`Probes.table` is `NativeX86.All.nativeTable`, no probe-local arms). |
| `openat` (257) is a pending arm in `NativeX86.extendedTable` (`OpenMissing.previousHub_openat_pending`, `OpenMissing.previousHub_unmodeled`). | missing feature (pending arm) | **Closed in the hub**: the reference slot dispatches fs-io's `openatSpec` (`OpenMissing.hub_openat_translated`). `NativeX86.extendedTable` is still the table of `Machines.X86NativeLaunch`/`X86LaunchExecution`; the `previousHub_*` theorems are about it. |
| The hub table guards every arm with the `TASK_SIZE_MAX` boundary chaos (`NativeX86.All.boundarySuspect`): an argument register in `[TASK_SIZE_MAX, 2^47]`, or a constant-size pointer within its size below `TASK_SIZE_MAX`, makes the call only `unmodeled`. | design choice (sound chaos) | Every kit rule takes `boundarySuspect = false` as a side condition, discharged by evaluation or register by register (`probe_clear`); no probe's registers reach the window. |
| `openat` can fail with an injected `ENOMEM`, `EACCES`, `EMFILE` or `ENFILE` (LPS `Sys/Fs/Open.v` `openat_errnos`) on an existing file; Linux did not. | design choice (reference-faithful refusal) | Named as the `openFailed`/`injected` alternatives of the universal statements. |
| A regular-file `write` is never short in LPS (`Sys/Fs/ReadWrite.v`), while a channel write may be. | design choice | The stdout write keeps the `shortWrite` alternative; the file write has none. |
| `ARCH_GET_FS` (`arch_prctl(0x1003, …)`) is not modeled by the hub (`NativeX86.archPrctlSpec` models only `ARCH_SET_FS`). | missing feature (chaos) | Open, documented: `arch_getfs` is proved to stop `unmodeled` at that call (`ArchGetfs.unmodeled_at_get`) and its Linux run is not admitted. |
| The universal statements (`exec`/`sound`/`determined`) are for one launch: the entry draw `Probe.entry` (`X86Launch.Controls.entry`: fixed stack pointer `0x7fffffffe000`, zero slack, zero `AT_RANDOM`) and the harness input `harnessInputFiles inputFiles` are fixed. The reference quantifies the entry draw independently (`Run.v` `Variable mi_draw : EntryDraw`). They quantify over refusal filters and syscall alternatives only; the recorded `"sp"` arguments are matched against `P.entry.sp`, not against Linux's randomized address. | missing feature (proof generality) | Open: generalizing over `entry` (stack alignment, slack, draw) is not done. |
| qemu-user holds its own `-D` log open at descriptor 3, so a guest `openat` returns 4 there. | harness limitation | The fd-returning probes skip qemu-user (`skipBackends`, with this reason) and are backed by native, bwrap and container (container: outcome, output and files only, no tracer). `open_missing`/`open_efault` agree on all four. |

## Commands

```sh
tools/verification-projects/lps_probes.py backends          # which backends work here
tools/verification-projects/lps_probes.py check             # every link, live, all backends
tools/verification-projects/lps_probes.py check --offline   # no runs: sources, pins, JSON, Lean
tools/verification-projects/lps_probes.py record <probe>    # (re)record JSON + pin + Lean data
tools/verification-projects/lps_probes.py run <probe>       # print the observation per backend
python3 -B tools/verification-projects/test_lps_probes.py   # unit, link-mutation and live tests
```

Always run probes through `lps_probes.py`, never directly.

## Build

`build.sh <probe.s> <out> [rx|rwx]` runs `as --64` and `ld -static -nostdlib --build-id=none -s`
with `probes/probe.ld`. The result is one R+X `PT_LOAD` at `0x400000` and file offset 0,
which covers the ELF header, the program header and the code. A probe that reads into
a buffer of its own image declares `"image": "rwx"`. It is then linked with
`probes/probe-rwx.ld`, which makes the same `PT_LOAD` R+W+X, so the buffer has a
fixed address that the model and every backend agree on. A byte's file offset is
its distance from `0x400000`, so the Lean segment is a prefix of the file. Binaries are
not committed; `SHA256SUMS` pins the rebuilt bytes (GNU binutils 2.42).

## Execution backends and isolation

Each JSON records the backend that produced it, the host kernel (`uname -r`), the tool
versions and the backends that agreed.

* **container** (podman/docker, preferred and auto-detected): `--network none --read-only`,
  a tmpfs `/tmp`, only the work directory bound, all capabilities dropped, pids/memory/CPU
  limits, `--platform linux/amd64` (so it also works from macOS). The default image runs
  the probe without a tracer, which compares outcome and output only. Without a tracer the
  engine reports a kill by signal n as status 128 + n, so a status above 128 matches that
  exit status or that signal. The image is pulled before the run, outside the capture. Set
  `LPS_PROBES_CONTAINER_IMAGE` to an image with `/usr/bin/strace` to trace as well.
* **bwrap**: every namespace unshared, read-only `/usr`, only the work directory writable,
  plus the strace allowlist. strace runs under `setarch -R` inside the sandbox, so the
  stack is not randomized there either (entering the user namespace clears a personality
  set outside it). Detection runs a trivial sandbox first. On Ubuntu 24.04 with
  `kernel.apparmor_restrict_unprivileged_userns=1`, user namespaces are refused, so the
  backend reports itself unavailable and the tool falls back.
* **native**: strace on the host, with guards. The guards are a fresh `mkdtemp` working
  directory, an empty environment, rlimits (CPU 2 s, address space 64 MiB, file size
  1 MiB, 16 descriptors, `NPROC=0`, no core dumps), and a static check that declared
  paths and string literals are relative and cannot escape. strace fault injection also
  denies every syscall outside the probe's `allow` list with `EPERM`; such a denial makes
  the run fail loudly. The probe stops itself before `execve`, so the limits apply to the
  probe and not to strace.
* **qemu-user** (`qemu-x86_64 -d strace`; `--qemu` or `LPS_PROBES_QEMU`): emulates the CPU
  on any host and gives an independent cross-check. **It is not isolation.** qemu-user
  forwards every syscall to the host kernel. The same working-directory, environment and
  rlimit guards apply, except `NPROC`, since qemu starts a helper thread. The binary is
  never committed. qemu-user also checks a `read` buffer before it forwards the call:
  for a read-only buffer it answers `-EFAULT` where Linux checks the descriptor first
  and answers `-EBADF`. The read probes therefore use writable (`rwx`) images.
* **qemu-system** (recipe only): boot a minimal x86-64 Linux VM (for example
  `qemu-system-x86_64 -m 256 -nographic -kernel bzImage -initrd probes.cpio -append console=ttyS0`)
  whose initramfs contains a static `strace` and the probe. Copy the probe and its inputs
  into a tmpfs, run `strace -f -X raw -e trace=all -o /trace ./probe < stdin`, print the
  trace, the output and `echo $?` on the serial console, and power off. A backend that
  parses the console into the same observation dictionary can then join `check`.

`check` runs every available backend and fails on any disagreement between them. On this
host that is container (podman, no tracer in the default image), bwrap, native and
qemu-user; every fixture is recorded by bwrap with the agreement of all four (the
descriptor-returning file probes skip qemu-user, see the gaps). A backend without a
tracer compares only outcome, output and final files.

## Writing a probe

1. Write `probes/<name>.s`. Keep it a few instructions long, and use forms the x86 machine
   decodes (`mov $imm32,%r32`, ALU, loads and stores, and so on). At each `syscall`, all
   six status flags must be defined. They are defined at entry, after `mov` and after
   `sub`; `xor`-zeroing leaves AF undefined (see `X86LaunchExecution.lean`).
2. Write `probes/<name>.json` with `probe`, `claim`, `mutantOf` (or `null`), `inputs`
   (`files`: relative name to hex contents; `stdinHex`), `allow` (the syscall allowlist)
   and `lean` (`module` and the fully qualified `theorems`), and optionally
   `"image": "rwx"`. With a nonempty `stdinHex`, the generated data module also defines
   `stdin`, launches the probe with `harnessInputWith stdin`, and records in
   `observed.stdin` the bytes the reads returned. Those bytes are listed first in
   `Observed.events`, so every read of stdin must precede the writes.
3. Run `lps_probes.py record <name>`. It builds the probe, runs every backend, requires
   them to agree, and writes the JSON `expected`/`recorded` fields, `SHA256SUMS` and
   `Data/<Name>.lean`. Then run `sil gen umbrellas`.
4. Prove the theorems with the kit (`Silmaril/Process/LPS/Probes/Kit.lean`):

   ```lean
   open Data.Exit42
   theorem layout : probe.Layout := by probe_layout
   instance checked : probe.Checked :=
     ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

   theorem determined (refused : RefusalFilter) : probe.Determined refused observed := by
     unfold Probe.Determined
     rw [Probe.initial_at]
     probe_instr 120 5 (.movI32 .rax 60)    -- segment offset, length, decoded instruction
     probe_instr 125 5 (.movI32 .rdi 42)
     probe_trap 130                          -- `syscall`
     probe_exit 42                           -- RDI at the exit
     exact ⟨_, rfl, rfl, rfl, rfl⟩

   theorem admits (refused : RefusalFilter) : probe.Admits refused observed := by
     apply Probe.admits_of
     case run => rw [Probe.initial_at]; probe_instr 120 5 (.movI32 .rax 60); …; probe_exit 42
     all_goals probe_side
   ```

   The code starts at segment offset 120 (`0x400078`). `objdump -d` on a built probe
   gives the offsets and lengths. A `write` of `count` image bytes at offset `off` is
   `probe_write off count`. In an `Omni.Exec` proof it leaves `∀ ds, WritePrefix … ds → …`
   (every delivered prefix: the reference short write). In a `Run` it is
   `probe_write off count with ds`, which names the bytes delivered.
   Syscalls with a single outcome (error returns, `close`, an empty write, a read at end
   of file) are stepped with `probe_ret lemma` from `KitReturns.lean`, for example
   `probe_ret write_badf_iff` or `probe_ret close_ok_iff`. A read of stdin into an `rwx`
   buffer at segment offset `boff` is `apply Probe.exec_read (boff := …) (count := …)`
   (or `Probe.run_read … (bs := …)`) from `KitMemory.lean`. It leaves
   `∀ bs, ReadPrefix … bs → …`. After it, the memory holds the read bytes, so the
   steps use `probe_instrW`, `probe_trapW`, `probe_exitW` and
   `Probe.exec_write_written`. `ReadEcho.lean` shows how to quantify over the stdin
   stream with `Probe.withStdin`.
5. Run `lps_probes.py check` and the tests, and build the touched modules.
