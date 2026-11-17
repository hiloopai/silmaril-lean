module

public import Silmaril.Elf.CliExe.Glibc.Defs
public import Silmaril.Elf.CliExe.Hello.Defs
public import Silmaril.Elf.Link.Dyn.LibMod.Program.Defs

/-! # Standard problems: a glibc executable runs `main` after the standard start-up

Two shapes about **how a dynamically linked executable on glibc reaches `main`**, over the
existing models of `Silmaril.Elf.Link.Dyn` (nothing here adds a model or trusts anything new):

| name | statement | status of the model |
|---|---|---|
| `silmaril.shapes.elf.glibc_start` | `GlibcStart exe pc pl`: the library pins are checked (`pc.ok`, `pl.ok`) and **some description `B` of the file passes the per-binary check `B.ok pc pl`**: its headers, references and binding certificate against the pinned glibc lookups, **the standard gcc/clang C runtime** (`_start` → `__libc_start_main` → `_init`/`frame_dummy` → `main` → `exit` → destructors, `_fini`, placed as `B.layout`), the image facts and `main`'s listing | process model (`Proc`): the executable's code on `Open9`, glibc's entry points as trusted contracts |
| `silmaril.shapes.elf.glibc_runtime` | `GlibcRuntime X M exe pc pl start`: for such a `B`, **glibc's own code realises those contracts** on a real machine `X` with the library module `M`: initialisation and the four `Realises` obligations of `Silmaril.Elf.Link.Dyn.LibMod.Program` (the callback gate, `__libc_start_main`, `__cxa_finalize`, every import of `B`) | real machine: discharges the trust in glibc's contracts |

**`glibc_start` is a checked description, not a semantic statement.** By itself it says only that
a description of the file passes a decidable check (`B.ok`, one `decide +kernel`); it says nothing
about runs. **Its execution consequence is a separate theorem**, `Thms.cli_of_main` (and, for
hello, `Thms.hello_via_start`), which a row of this shape does not contain and must be cited.

**What `glibc_start` gives** (`Thms.cli_of_main`): with `B` from it, a proof of `main` alone
against the library contracts (`Program.MainProof B spec tier`) makes the file satisfy the
specification in the CLI model `CliExe.glibcPin` (`toCli spec tier`), from the executable's entry
`_start`: `Program.verified` runs the loader, the C runtime (`Crt.crt_run'`), `main`'s callback
and `exit` (status `main`'s return modulo 256, stdout what `main` wrote, flushed). So the standard
start-up is checked per binary (`B.ok`, one `decide +kernel`) and proved once for every binary;
only `main` is per program. It does **not** assert that the strings `PT_INTERP` and `DT_NEEDED`
imply this behaviour: the claim is about the process model and the checked description.

**What it rests on**: the process model `Proc` (glibc's `__libc_start_main`, `exit`,
`__cxa_finalize` and the imports as one atomic contract step each; the loader as the `Dyn.Loader`
relation), and the world/outcome bridge of `Program`. `glibc_runtime` is the open problem that
removes the trust in glibc's contracts. It is **a shape only**: its parameters (a real machine
`X : LibMod.Real`, a library module `M`) have **no instance yet** in this repository (the intended
machine is `Str9K` with a kernel answering `write` and `exit_group`, `Silmaril.Elf.Link.Dyn.LibMod`),
so there is no row and in particular **no open problem about glibc 2.39** yet: instantiating it
(a concrete `X`, `M` and start states) is itself unmet.

Rows: `silmaril.shapes.elf.glibc_start.glibc239` (the pinned glibc 2.39) and
`silmaril.elf.start.hello.gcc_o2` (the pinned `hello-gcc`, proved in `Thms`).
-/

@[expose] public section

namespace Silmaril.Elf.CliExe

open Silmaril.Elf.Link.Dyn.Program (Bin LibPin World lib)
open Silmaril.Elf.Link.Dyn.LibMod (Mod)

/-- **The standard start-up of a glibc executable** (module doc). -/
@[problem "silmaril.shapes.elf.glibc_start"
  (title := "A dynamically linked ELF executable has a checked standard C start-up description against pinned glibc (a decidable check; its execution consequence is the theorem cli_of_main)")]
def GlibcStart {V : Type} (exe : Silmaril.Project.Value V) (pc pl : LibPin) : Prop :=
  pc.ok = true ∧ pl.ok = true ∧ ∃ B : Bin, B.file = Shapes.file exe ∧ B.ok pc pl = true

/-- **glibc's code realises the C runtime's contracts** for a checked description of the file, on
the real machine `X` with the library module `M` (module doc). -/
@[problem "silmaril.shapes.elf.glibc_runtime"
  (title := "glibc's own code realises the C-runtime contracts of a dynamically linked executable on a real machine (shape only: no concrete machine instance yet)")]
def GlibcRuntime {V : Type} (X : Silmaril.Elf.Link.Dyn.LibMod.Real) (M : Mod) (exe : Silmaril.Project.Value V) (pc pl : LibPin)
    (start : World → X.τ → Prop) : Prop :=
  ∃ B : Bin, B.file = Shapes.file exe ∧ B.ok pc pl = true ∧
    Silmaril.Elf.Link.Dyn.LibMod.Task.crtInit X M B pc pl lib (fun _ => True) start ∧
    Silmaril.Elf.Link.Dyn.LibMod.Task.crtGate X M B lib ∧
    Silmaril.Elf.Link.Dyn.LibMod.Task.crtStartMain X M B lib ∧
    Silmaril.Elf.Link.Dyn.LibMod.Task.crtCxaFinalize X M B lib ∧
    ∀ i ∈ B.imports, Silmaril.Elf.Link.Dyn.LibMod.Task.crtNamed X M B lib i.name i.off

end Silmaril.Elf.CliExe

end

silmaril instance silmaril.shapes.elf.glibc_start.glibc239
    (title := "the checked standard start-up description on the pinned glibc 2.39 (Ubuntu 2.39-0ubuntu8.9)") :=
  silmaril.shapes.elf.glibc_start (pc := Silmaril.Elf.Link.Dyn.Program.libc)
    (pl := Silmaril.Elf.Link.Dyn.Program.ld)

silmaril instance silmaril.elf.start.hello.gcc_o2
    (title := "hello-gcc has a checked standard start-up description on the pinned glibc 2.39 (execution: cli_of_main / hello_via_start)") :=
  silmaril.shapes.elf.glibc_start (exe := Silmaril.Elf.CliExe.Hello.helloGcc)
    (pc := Silmaril.Elf.Link.Dyn.Program.libc) (pl := Silmaril.Elf.Link.Dyn.Program.ld)
