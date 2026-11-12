module

public import Silmaril.Elf.Link.Dyn.Program.Cli.Examples
public import Silmaril.Raw.Elf.Link.Dyn.Program.StdExe.Examples.HelloGcc
public import Silmaril.Raw.Elf.Link.Dyn.Program.StdExe.Examples.CatStdin
public import Silmaril.Raw.Elf.Link.Dyn.Program.StdExe.Examples.HelloClang
public import Silmaril.Raw.Elf.Link.Dyn.Program.StdExe.Examples.AdderGcc

/-! # Standard executables: examples

Variants of the Program API's examples, stated as `StdExe`s and proved from `main`
(`at_main`), and their CLI readings in one line each.

## Variants

| problem | Program API (`Program.Examples`) | StdExe (`Program.StdExe.Examples`) |
|---|---|---|
| `glibc.hello.gcc` | `helloGcc_verified`: `verify_main` | `helloGccStd_verified`: `at_main`, `main_straight` |
| `glibc.hello.clang` | (`Hello.ClangRun`, direct) | `helloClangStd_verified`: `at_main`, blocks, `puts`, `main_returns` |
| `glibc.adder.gcc` | (`Small.AdderGccMain`, direct) | `adderGccStd_verified`: `at_main`, `scanf`, two branches, `__printf_chk`, `mcanary`, `main_returns` |
| `glibc.cat-stdin.gcc` | `catMain` + `catStdinGcc_verified` | `catStdinGccStd_verified`: `at_main`, …, `main_returns` |

* **Direct** (`Hello.{Gcc,Clang}Run`, `Small.Adder*Main`, before the Program API): the whole
  process is proved per binary (loader, `_start`, `__libc_start_main`, `main`, `exit`), about a
  thousand lines for hello. Nothing shared; every binary repeats the start-up.
* **Program API** (`Program.Examples`): the start-up is proved once (`Program.verified`); a proof
  is `main`'s. The statement names the five parameters of `Program.Verified` and, beyond
  straight-line `main`s, the proof begins with the 26 intros of `MainProof` and builds the entry
  facts and the frame bundle by hand: boilerplate that tracks `MainOk`'s hypothesis order
  (fragile: a change of `MainOk` breaks every proof).
* **StdExe** (here): the statement is `E.Verified` for a record naming the binary, its hash, the
  glibc pin, the compiler and the spec; `at_main` does the intros, the check's facts, the entry
  record (`Entry`), the opaque view (`GlibcView`) and the frame bundle, `main_returns` the
  return's side conditions, `mghost` the library state after a call. The body is the same `main`
  reasoning. Abstracted: `MainOk`'s hypothesis order (one tactic to update), glibc's internals
  (any `Streams.StreamRep`). Fragile: the tactics find facts by their statements (`mfind`,
  `regFacts`), so a step breaks when a fact is not in the expected normal form; a frame bundle
  after stores still has to be stated with its slots (`have K : Frm … := by mstores K`).

Lines of code (`bin/mor variants`, comments and blank lines not counted; whole modules):

| problem | direct | Program API | StdExe |
|---|---|---|---|
| `glibc.hello.gcc` | 138 (`GccRun`; with `Gcc{Start,Init,Main,Fini,Mem}` about 900) | 16 | 18 |
| `glibc.hello.clang` | 130 (`ClangRun`; with its five modules about 1000) | — | 54 (with `Task.helloClangLazy`) |
| `glibc.cat-stdin.gcc` | — | 106 | 83 |
| `glibc.adder.gcc` | 560 (`AdderGccMain`; with `AdderGcc` 690) | — | 119 |

The CLI readings (`StdExe.Verified.sat_liftAll`, `.sat_lift`) are one line each. -/

@[expose] public section

namespace Silmaril.Elf.Link.Dyn.Program.Examples

open Silmaril.Cli.Institution (Level Sen)
open Silmaril.Elf.Link.Dyn.Program

/-- **hello-gcc prints `hello, world` and succeeds on every invocation** (`L1`, uniformly). -/
theorem helloGccStd_prints :
    helloGccStd.model.Sat (Level.liftAll (L := .stream) (Sen.prints (lit "hello, world\n"))) :=
  helloGccStd_verified.sat_liftAll (helloGcc_toCli .cwd)

/-- **hello-clang prints `hello, world` and succeeds on every invocation** (eager binding). -/
theorem helloClangStd_prints :
    helloClangStd.model.Sat (Level.liftAll (L := .stream) (Sen.prints (lit "hello, world\n"))) :=
  helloClangStd_verified.sat_liftAll (helloGcc_toCli .cwd)

/-- **cat-stdin-gcc copies stdin to stdout** (`L1`, no arguments). -/
theorem catStdinGccStd_filter : (Level.stream.reduct catStdinGccStd.model).Sat (Sen.filter id) :=
  catStdinGccStd_verified.sat_lift (catStdinGcc_toCli .cwd)

/-- **adder-gcc meets its CLI specification** (`L3`). -/
theorem adderGccStd_cli : adderGccStd.model.Sat adderGccStd.cli := adderGccStd_verified.sat

end Silmaril.Elf.Link.Dyn.Program.Examples
