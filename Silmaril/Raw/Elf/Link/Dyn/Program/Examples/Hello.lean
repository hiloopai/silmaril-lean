-- variant-of: glibc.hello.gcc | style: program-api | see-also: Silmaril.Raw.Elf.Link.Dyn.Hello.GccRun, Silmaril.Raw.Elf.Link.Dyn.Program.StdExe.Examples.HelloGcc
module

public import Silmaril.Elf.Link.Dyn.Program.Examples.HelloGccBin
public import Silmaril.Elf.Link.Dyn.Program.Glibc
public import Silmaril.Raw.Elf.Link.Dyn.Program.Block

/-! # Hello, world (`gcc -O2`, glibc 2.39), verified

`examples/dyn/hello/hello.c` is `printf("hello, world\n"); return 0;`. The pinned executable and
its facts are generated (`HelloGccBin`); everything else comes from the library. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program.Examples

/-- What `hello` does, in every world. -/
def helloSpec : Spec := fun _ => { stdout := lit "hello, world\n", stderr := [], status := 0 }

/-- The per-binary check: headers, references, binding certificate, image, listings. -/
theorem helloGcc_ok : helloGcc.ok libc ld = true := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `main`, by symbolic execution and `puts`'s contract. -/
theorem helloGcc_main : MainProof helloGcc helloSpec Tier.reliable := by
  verify_main helloGcc_ok helloSpec

/-- **Every run of `hello-gcc` writes `hello, world` and exits 0.** -/
theorem helloGcc_verified : Verified helloGcc libc ld helloSpec Tier.reliable :=
  verified helloGcc_ok libc_ok ld_ok (fun _ h => h) helloGcc_main

end Silmaril.Elf.Link.Dyn.Program.Examples
