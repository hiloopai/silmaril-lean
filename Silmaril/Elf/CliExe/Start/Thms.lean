module

public import Silmaril.Elf.CliExe.Start.Defs
public import Silmaril.Elf.CliExe.Glibc.Thms
public import Silmaril.Elf.Link.Dyn.Program.Thms
public import Silmaril.Elf.Link.Dyn.Program.Cli.Thms
public import Silmaril.Elf.Link.Dyn.Program.Examples.Thms
import Silmaril.Proofs.Elf.CliExe.Hello

/-! # The standard start-up: the reduction to `main`, and hello

PROVED (standard axioms):

* `cli_of_main`: **a checked description and a proof of `main` give the file's CLI
  specification** in `glibcPin`, from the executable's entry (`Program.verified`: the loader,
  `Crt.crt_run'`, `exit`; `Program.Cli.x86Model_sat`);
* `hello_start`: the row `silmaril.elf.start.hello.gcc_o2`, the **checked description** only
  (`helloGcc_ok`, `libc_ok`, `ld_ok`); it says nothing about runs by itself;
* `hello_via_start`: **the execution consequence for hello**: its L3 specification in `glibcPin`,
  through `cli_of_main` from the checked description and the proof of `main` alone
  (`Program.Examples.helloGcc_main`). It is a theorem, not a row: `glibc_start` rows are the
  check, this is what the check is for.
-/

@[expose] public section

namespace Silmaril.Elf.CliExe

open Silmaril.Elf.Link.Dyn.Program

/-- **The reduction to `main`** (module doc of `Start.Defs`). -/
theorem cli_of_main {V : Type} {exe : Silmaril.Project.Value V} {pc pl : LibPin} {B : Bin}
    (hc : pc.ok = true) (hl : pl.ok = true) (hf : B.file = Shapes.file exe)
    (hok : B.ok pc pl = true) {spec : Spec} {tier : Tier} (hrel : ∀ w, tier w → Tier.reliable w)
    (hmain : MainProof B spec tier) (conv : PathConv := .cwd) :
    (glibcPin pc pl (fun _ => True) conv exe.bytes).Sat (toCli conv spec tier) :=
  glibcPin_sat hf hok (x86Model_sat conv (verified hok hc hl hrel hmain))

/-- **`hello-gcc` has a checked standard start-up description on the pinned glibc 2.39.** The run
it gives is `hello_via_start`. -/
@[solves "silmaril.elf.start.hello.gcc_o2"]
theorem hello_start : silmaril.elf.start.hello.gcc_o2 :=
  ⟨libc_ok, ld_ok, Examples.helloGcc, Silmaril.Proofs.Elf.CliExe.Hello.hello_file,
    Examples.helloGcc_ok⟩

/-- **hello's specification through the reduction**: `GlibcStart`'s check and the proof of `main`
alone (`Examples.helloGcc_main`) give hello's L3 specification in `glibcPin`. -/
theorem hello_via_start :
    (glibcPin libc ld (fun _ => True) .cwd Hello.helloGcc.bytes).Sat
      (toCli .cwd Examples.helloSpec Tier.reliable) :=
  cli_of_main libc_ok ld_ok Silmaril.Proofs.Elf.CliExe.Hello.hello_file Examples.helloGcc_ok
    (fun _ h => h) Examples.helloGcc_main

end Silmaril.Elf.CliExe

silmaril group silmaril.elf.start
  (title := "glibc executables: the checked standard start-up description (process model; execution via cli_of_main) and the real-runtime shape (no instance yet)")
  (children := [silmaril.shapes.elf.glibc_start, silmaril.shapes.elf.glibc_start.glibc239,
    silmaril.shapes.elf.glibc_runtime, silmaril.elf.start.hello.gcc_o2])
