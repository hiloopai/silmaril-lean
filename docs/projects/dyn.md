# Dynamically linked processes

`Silmaril.Elf.Link.Dyn` models a dynamically linked x86-64 Linux process running against
glibc 2.39, and proves end-to-end facts about real gcc and clang executables in it. The
umbrella header is `Silmaril.Elf.Link.Dyn.Thms`. The ELF file layer, the loader relation
`ExeLoaded` and its image come from the ELF API ([ELF](elf.md)).

## Layers

| layer | modules | main names |
|---|---|---|
| loader (**trusted**) | `Dyn.Loader`, `Dyn.Image` (ELF API), `Dyn.Glibc` | `ExeLoaded`, `ImageOk`, `Glibc.libcChunks`, `ldChunks` |
| process | `Dyn.Proc`, `Dyn.ProcG`, `Dyn.ProcX`, `Dyn.Imports` | `Proc.proc W`, `PState`, `Ghost`, `World`, `Fn`, `gateStep` |
| library contracts | `Dyn.Proc`, `Dyn.Stdio`, `Dyn.Streams` | `puts`, `printf`/`scanf` (`Stdio.Contracts`), stdio streams (`fopen`, `fread`, `fwrite`, `ferror`, …, `Streams.Table`) |
| block certificates | `Dyn.Cert`, `Silmaril.X86.Bir9X` (modules `Silmaril.X86.Bir9.X.*`) | blocks checked once by `decide +kernel` and replayed as one step |
| C runtime | `Dyn.Crt` | `_start`, `_init`, `frame_dummy`, `__do_global_dtors_aux`, `_fini` of a gcc or clang PIE, `Crt.crt_run` |
| library modules | `Dyn.LibMod`, `Dyn.Libc` | `LibModule`, `ModRet`, `relax`, the C-runtime machine `crt M W`, `crt_sound` |
| program API | `Dyn.Program`, `Dyn.Program.Cli` | `Bin`, `Bin.ok`, `LibPin`, `Spec`, `Tier`, `Program.Verified`, `verified`, `call_site`, `verify_main` |
| standard executables | `Dyn.Program.StdExe` | `StdExe`, `StdExe.Verified`, `Entry`, tactics `at_main`, `main_returns`, `main_straight`, steps `mblock`, `mcallN`, `mret`, `mloop` |
| institution | `Silmaril.X86.BinInstitution` (with `.Cli`) | `ISig`, `Sign`, `Sen`, `inst`, `DynSen`, `ProcSen`, `withImports` |

**The process.** `Proc.proc W` is silmaril's `Open9` inside the executable's image and,
at the addresses the loader bound the imports to, each glibc function as **one atomic step**
given by its contract (`World`: start-up, `exit`, the callback gate, `puts`, stdio). `ProcG`
lifts it to any image ISA extending `Open9`; `ProcX` adds the extended block lifter.

**The program API.** A program is a pinned executable (`Bin`, its generated facts checked
by one `decide +kernel` of `Bin.ok`) against pinned glibc lookups (`LibPin`). Its
specification maps a C-level world (argv, files, stdin) to an outcome (stdout, stderr,
status). `Program.Verified` says that every run of every allowed load of the process ends with
the specified outcome. `Program.verified` reduces it to a proof of `main` against the
library contracts. `StdExe` packages the common case: an `-O2` gcc or clang PIE against glibc
2.39. `Program.Cli` and `BinInstitution.Cli` read these statements in the CLI institution
(`Silmaril.Cli.Institution`).

**Library modules.** `LibMod` is the pattern for libraries with global state: an invariant
over the memory the library owns, functions that preserve it within a frame convention, and
the C-runtime machine that stops when client code touches library memory. `crt_sound`
relates proofs on that machine to the process model.

## Examples

The C sources and the pinned executables are in `examples/dyn/`. `examples/dyn/pin.sh --check`
checks the sha256 of the committed files and `--build` rebuilds them.

* `Dyn.Hello`: hello world for gcc (eager binding, CET `.plt.sec`) and clang (lazy binding):
  every run *of the process model* (the file's code on `Open9`, glibc's functions as trusted
  contract steps, memory from the trusted loader relation) halts with status 0 and stdout
  `hello, world\n`. `hello_gcc_sen` restates the gcc result as a sentence of `BinInstitution`.
  This is not a claim about glibc's code: real execution (`LibMod.helloGcc_real`) is
  conditional on the open `Task.helloGccCrt` and `HelloLib` (`Dyn.LibMod.Hello`).
* `Dyn.Small`: `return 0`, `return 42` and a `scanf`/`printf` adder for gcc and clang, with
  non-vacuity witnesses.
* `Dyn.Program.Examples`: hello, `cat` of stdin and `cat FILE` through the program API.
* `Dyn.Program.StdExe.Examples`: hello (gcc and clang), `cat` of stdin and the adder as
  standard executables.
* `Dyn.LibMod.Hello`: hello world through the library-module machine.

## GNU `sha256sum`

`Dyn.Sha256sum` verifies GNU coreutils 9.4 `sha256sum` (Ubuntu `coreutils` 9.4-3ubuntu6.3,
the pinned `examples/elf/pinned/gnu-sha256sum`, read through `Dyn.PinBytes.sha256sum`), a PIE
with `DF_BIND_NOW` and `DT_NEEDED = [libcrypto.so.3, libc.so.6]`. `libcrypto.so.3`, `libc.so.6`
and `ld.so` enter only through byte ranges (`Sha256sum.Scope`); the theorems hold for every file
agreeing with them. Licences: [`NOTICES/effects-examples`](../../NOTICES/effects-examples/README.md)
(coreutils), [`NOTICES/glibc`](../../NOTICES/glibc/README.md),
[`NOTICES/openssl`](../../NOTICES/openssl/README.md).

* `Sha256sum.sha_slots` (`Sha256sum.Thms`): the eager slot table of all 84 relocations.
* `Sha256sum.sha256sum_stdin` (stdin): for every `libcrypto.so.3`, `libc.so.6` and `ld.so`
  agreeing with the pinned chunks, every base, ifunc choice and binding mode, a process started
  by the kernel on the loaded image, in a world with the imports' contracts (`MainImps`,
  `TailImps`, `ExitOk`) whose library enters `main` with `argv = [a0]` and standard input `data`
  (`MainLib` at `World.atMain`), ends with the exit status and standard output of
  `Silmaril.Apps.Sha256sum.sha256sum` on that world, and nothing on stderr.
  `sha256sum_stdinK` asks `MainLib` only at the entries the start-up can produce.
* `Sha256sum.sha256sum_files` (`sha256sum F1 … Fn`, success tier): the same for readable files
  whose names are printed verbatim (`FilesSpec.Verbatim`); `sha256sum_filesK` likewise.
* `Sha256sum.sha256sum_mixed_loaded` (file-error tier, on the extended process `procG XG`):
  each operand is readable and printed verbatim, or refused at `open` and gnulib-safe (`MOp`);
  every run halts with the specification's status, standard output and standard error. The
  loader relation is `ExeLoadedP` (with the trusted loader fact `PageBase`).
* Resource preconditions: `sha256sum_stdin(K)` take `1 ≤ maxAllocs ∧ 0x8048 ≤ maxHeap`,
  `sha256sum_files(K)` on `n` operands take `n ≤ maxAllocs ∧ 0x8048 * n ≤ maxHeap ∧ n ≤ maxOpen`.
* Non-vacuity (`Sha256sum.Wit`): `Wit.sha256sum_stdin_runs` and `Wit.sha256sum_files_runs` are
  concrete runs meeting every hypothesis. Model limit: the stream representation `slotRep` holds
  a stream's unread bytes in one 1 MiB slot, so the input fits `64 + |data| ≤ S0`.
* Trusted beyond the rest of `Dyn`: the import contracts of `Streams.Defs`, `Imports.Defs` and
  `Proc.Defs`, the stream representation `slotRep`, the concrete `Env`/`World` of `WitWorld` and
  the specification `Silmaril.Apps.Sha256sum`.
* CLI institution: `Sha256sum.stdinModel_sat`/`stdinModel_std` (`Sha256sum.Cli.Thms`): the `L1`
  model of the binary, whose runs carry exactly the hypotheses of `sha256sum_stdin`, meets
  `Std.sha256Stdin`. `Silmaril.Elf.LpsCli` reads static executables under LPS as CLI models;
  `LpsCli.Sha256sum.static_agrees_glibc`: `sha256sum-min` (static, LPS) and GNU `sha256sum`
  (glibc) agree run by run.

## Trust

A theorem here rests on:

* silmaril's `Open9` instruction semantics;
* **the loader relation `ExeLoaded`** (`Dyn.Loader`), a hand transcription of glibc 2.39's
  `ld.so`: search scope, GNU-hash lookup with symbol versions,
  `RELATIVE`/`GLOB_DAT`/`JUMP_SLOT`/`IRELATIVE` relocations, eager and lazy binding, RELRO.
  It is not proved against `ld.so`;
* the glibc contracts of `Proc.World` and `Program.Lib` (each function as stated, as one
  atomic step), and the world bridge of `Program` (the initial state for a world, glibc's stdio
  state at `main`, the flush at `exit`);
* the `include_bytes` elaborator, and that the files in `examples/dyn/pinned/` are the ones
  whose sha256 `examples/dyn/pins.txt` lists.

`libc.so.6` and `ld.so` enter only through short byte ranges (the tables symbol lookup reads),
and every theorem holds for every file agreeing with them. Their licence is in
[`NOTICES/glibc`](../../NOTICES/glibc/README.md). The generated facts (layouts, listings, block
certificates) are not trusted: Lean re-checks them with `decide +kernel`.

`Dyn.Stdio.Defs` repeats `Silmaril.Libc.Stdio.Defs` (the `%d` scanner and printer) in this
namespace, because the `Libc` region depends on `Elf`; merging the two is left for later.

## Build

    lake build Silmaril.Elf.Link.Dyn.Thms Silmaril.Elf.Link.Dyn.Program.StdExe.Examples \
      Silmaril.Elf.Link.Dyn.LibMod.Hello.Thms Silmaril.X86.BinInstitution.Cli.Thms \
      Silmaril.Elf.Link.Dyn.Sha256sum.Cli.Thms Silmaril.Elf.LpsCli.Sha256sum.Thms

Not included yet: the LeetCode solutions and the allocator library module.
