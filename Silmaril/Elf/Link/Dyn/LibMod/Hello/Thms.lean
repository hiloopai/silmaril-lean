-- variant-of: glibc.hello.gcc | style: crt-libmod | see-also: Silmaril.Raw.Elf.Link.Dyn.Program.Examples.Hello, Silmaril.Elf.Link.Dyn.Libc.Examples.Hello
module

public import Silmaril.Elf.Link.Dyn.LibMod.Hello.Defs
public import Silmaril.Elf.Link.Dyn.LibMod.Program.Thms

/-!
# `hello` on the C-runtime machine: the reduction

PROVED (standard axioms), names in `Silmaril.Elf.Link.Dyn.LibMod`:

* `helloGcc_imports`: `hello`'s only import is `puts`;
* `helloGccCrt_verified`: the C-runtime claim implies `helloGcc_verified`'s statement;
* **`helloGcc_real`**: real execution of `hello` ends with `hello, world` and status 0, from
  `Task.helloGccCrt` (the problem about `main`) and `HelloLib` (the problem about glibc).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.LibMod

open Silmaril.Elf.Link.Dyn.Program (lib libc ld Tier World Verified)
open Silmaril.Elf.Link.Dyn.Program.Examples (helloGcc helloSpec)

/-- `hello` imports `puts` only. -/
theorem helloGcc_imports : helloGcc.imports.map (·.name) = [nm "puts"] := rfl

/-- **The C-runtime claim implies the process-model claim** of `hello`. -/
theorem helloGccCrt_verified {M : Mod} (h : Task.helloGccCrt M) :
    Verified helloGcc libc ld helloSpec Tier.reliable :=
  VerifiedCrt.verified h

/-- **`hello` on a real machine**: every real start state of a reliable world runs to a state
representing the ended process with outcome `hello, world`, status 0. -/
theorem helloGcc_real {X : Real} {M : Mod} {start : World → X.τ → Prop} (hm : Task.helloGccCrt M)
    (hl : HelloLib X M start) : RealVerified X M helloSpec Tier.reliable start :=
  realVerified_of hm hl.init (realisesWorld_program hl.gate hl.startMain hl.cxaFinalize hl.puts)

end Silmaril.Elf.Link.Dyn.LibMod
