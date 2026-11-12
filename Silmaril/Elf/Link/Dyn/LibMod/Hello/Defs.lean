-- variant-of: glibc.hello.gcc | style: crt-libmod | see-also: Silmaril.Raw.Elf.Link.Dyn.Program.Examples.Hello, Silmaril.Elf.Link.Dyn.Libc.Examples.Hello
module

public import Silmaril.Elf.Link.Dyn.LibMod.Program.Defs
public import Silmaril.Elf.Link.Dyn.Program.Examples.Thms

/-!
# `hello` (gcc -O2, glibc 2.39) on the C-runtime machine: the smallest libc subset

`hello` imports `puts` only; the C runtime around `main` calls `__libc_start_main` and
`__cxa_finalize`, and `main`'s return runs glibc's `exit` path (the callback gate). So the libc
subset `hello` needs is **puts + exit**: the four entry points of `HelloLib`.

The reduction (`Thms.helloGcc_real`): real execution of the ELF, linked against glibc and loaded by
ld.so, ends with `hello, world` on stdout and status 0, from

* `Task.helloGccCrt M`: **the problem about `main`**: `hello`'s process (`_start`, the C runtime,
  `main`) on the C-runtime machine of the module `M`, every libc call an atomic step on opaque
  state. It is `helloGcc_verified` (proved, `Program.Examples`) on `LibMod.crt` instead of
  `Proc.proc`: the same symbolic execution with the call-site rule relaxed by the scratch stack,
  and the client's writes apart from `M`'s memory (`main` writes only its stack frame).
  `Thms.helloGccCrt_verified`: it implies `helloGcc_verified`;
* `HelloLib X M start`: **the problem about glibc**: initialisation (`Task.crtInit`) and the four
  realisations (`Task.crtGate`, `Task.crtStartMain`, `Task.crtCxaFinalize`, `Task.crtNamed` for
  `puts`), on a real machine `X` (Str9K with a kernel answering `write` and `exit_group`).

**Variants.** Against `Silmaril.Raw.Elf.Link.Dyn.Program.Examples.Hello` (`program-api`, the
process model, glibc's contracts trusted) this variant states what discharges the trust: the
library's obligations are named Tasks about glibc's code, the composition is proved
(`LibMod.crt_sound`). Against `Silmaril.Elf.Link.Dyn.Libc.Examples.Hello` (`loosest-libc-spec`,
every libc above `putsSpec`) it keeps the libc fixed (the module `M`) and adds the real machine.
Cost: the `main` proof must be (re)run on the C-runtime machine (`Task.helloGccCrt`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.LibMod

open Silmaril.Elf.Link.Dyn.Program (lib libc ld Tier World)
open Silmaril.Elf.Link.Dyn.Program.Examples (helloGcc helloSpec)

/-- **Open: `hello` on the C-runtime machine of `M`** (module doc). -/
def Task.helloGccCrt (M : Mod) : Prop :=
  VerifiedCrt M helloGcc libc ld helloSpec Tier.reliable

/-- **The library obligations of `hello`** on the real machine `X` with start states `start`:
initialisation and the four entry points of the puts + exit subset. -/
structure HelloLib (X : Real) (M : Mod) (start : World → X.τ → Prop) : Prop where
  init : Task.crtInit X M helloGcc libc ld lib (fun _ => True) start
  gate : Task.crtGate X M helloGcc lib
  startMain : Task.crtStartMain X M helloGcc lib
  cxaFinalize : Task.crtCxaFinalize X M helloGcc lib
  puts : ∀ i ∈ helloGcc.imports, Task.crtNamed X M helloGcc lib i.name i.off

end Silmaril.Elf.Link.Dyn.LibMod
