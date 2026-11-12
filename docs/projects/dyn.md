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
  every run halts with status 0 and stdout `hello, world\n`. `hello_gcc_sen` restates the gcc
  result as a sentence of `BinInstitution`.
* `Dyn.Small`: `return 0`, `return 42` and a `scanf`/`printf` adder for gcc and clang, with
  non-vacuity witnesses.
* `Dyn.Program.Examples`: hello, `cat` of stdin and `cat FILE` through the program API.
* `Dyn.Program.StdExe.Examples`: hello (gcc and clang), `cat` of stdin and the adder as
  standard executables.
* `Dyn.LibMod.Hello`: hello world through the library-module machine.

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
      Silmaril.Elf.Link.Dyn.LibMod.Hello.Thms Silmaril.X86.BinInstitution.Cli.Thms

Not included yet: the `sha256sum` executable (coreutils), the LeetCode solutions and the
allocator library module.
