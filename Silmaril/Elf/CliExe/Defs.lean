module

public import Silmaril.Elf.Exe.Defs
public import Silmaril.Cli.Institution.Defs

/-!
# CLI executables: an ELF executable, its loading facts, and a CLI specification

A **CLI executable row** (`silmaril.shapes.elf.cli_exe`) says that an ELF executable meets a
specification of the CLI institution (`Silmaril.Cli.Institution`) under a model of how it runs,
together with **the ELF API facts its loading model rests on**:
```
 CliExe exe k ld L M φ  :=  ExeOk (file exe) k ld  ∧  (M exe.bytes).Sat φ
                            └─ API facts ───────┘     └─ CLI institution ─┘
```

| part | what | where |
|---|---|---|
| executable | the file, an object of kind `k` (`KindIs`, `k.isExe`: `ET_EXEC`, PIE, static PIE) | `Silmaril.Elf.Facts` |
| loading model | `Loading`: `glibcDyn` (`execve` and glibc's `ld.so`), `staticLps` (silmaril's LPS `ELFImage` loader) | here |
| process model | `M : Bytes → Model L.sig`: how an executable with these bytes runs, at level `L` | the caller |
| CLI spec | `φ : Sen L.sig` at level `L` of the institution | `Silmaril.Cli.Institution` |

`ExeOk F k .glibcDyn` is what the glibc loading model needs of the file: an executable of kind
`k`, interpreted by `/lib64/ld-linux-x86-64.so.2`, needing `libc.so.6`, with no loader write on
a read-only segment (`Exe.NoTextRelD`, eager binding: so its code is where `CodeAt` says, see
`Exe.Thms`). `ExeOk F k .staticLps`: an executable of kind `k` with no interpreter.

The process model is a parameter: this shape does not fix how a loaded executable runs. A model
of a program at another interface `A` reaches level `L` by a reduct (`Hom.mod`), as for the
standard CLI shapes (`Silmaril.Project.Shapes.Cli`).
-/

@[expose] public section

namespace Silmaril.Elf

open Silmaril.Cli.Institution (Level Sen Model)
open Silmaril.X86.Link (Blob)
open Silmaril.Formats.ELF (NameBytes)
open Silmaril.Elf.Exe (InterpIs NoTextRelD)

/-- **The loading model** of a CLI executable. -/
inductive CliExe.Loading where
  /-- `execve` and glibc's `ld.so` (the executable, `libc.so.6` and `ld.so`). -/
  | glibcDyn
  /-- silmaril's LPS loader of a static executable (`Silmaril.Process.LPS.ELFImage`). -/
  | staticLps
  deriving DecidableEq, Repr

/-- The program interpreter of glibc on x86-64. -/
def CliExe.ldLinux : NameBytes := nameOf "/lib64/ld-linux-x86-64.so.2"

/-- **The API facts a loading model rests on** (module doc). -/
def CliExe.ExeOk (F : Blob) (k : Kind) : CliExe.Loading → Prop
  | .glibcDyn => KindIs F k ∧ k.isExe = true ∧ InterpIs F (some CliExe.ldLinux) ∧
      (∃ ns, Needed F ns ∧ nameOf "libc.so.6" ∈ ns) ∧ NoTextRelD F false
  | .staticLps => KindIs F k ∧ k.isExe = true ∧ InterpIs F none

/-- **A CLI executable meets a CLI specification**: its API facts for the loading model `ld`, and
`φ` holds in the model `M` gives to its bytes. -/
@[problem "silmaril.shapes.elf.cli_exe"
  (title := "An ELF executable of a given kind, with the API facts its loading model rests on, satisfies a CLI specification under a CLI model")]
def CliExe {V : Type} (exe : Silmaril.Project.Value V) (k : Kind) (ld : CliExe.Loading) (L : Level)
    (M : Silmaril.Formats.Bytes → Model L.sig) (φ : Sen L.sig) : Prop :=
  CliExe.ExeOk (Shapes.file exe) k ld ∧ (M exe.bytes).Sat φ

end Silmaril.Elf

end

silmaril instance silmaril.shapes.elf.cli_exe.glibc (title := "a dynamically linked executable on glibc") :=
  silmaril.shapes.elf.cli_exe (ld := Silmaril.Elf.CliExe.Loading.glibcDyn)
silmaril instance silmaril.shapes.elf.cli_exe.static (title := "a static executable (LPS loader)") :=
  silmaril.shapes.elf.cli_exe (ld := Silmaril.Elf.CliExe.Loading.staticLps)
