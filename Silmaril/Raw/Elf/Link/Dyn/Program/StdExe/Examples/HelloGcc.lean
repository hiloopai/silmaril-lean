-- variant-of: glibc.hello.gcc | style: stdexe-at-main | see-also: Silmaril.Raw.Elf.Link.Dyn.Program.Examples.Hello, Silmaril.Raw.Elf.Link.Dyn.Hello.GccRun
module

public import Silmaril.Elf.Link.Dyn.Program.StdExe.Thms
public import Silmaril.Raw.Elf.Link.Dyn.Program.Examples.Hello

/-! # Hello, world (`gcc -O2`) as a standard executable

The same binary and specification as `Program.Examples.Hello` (`helloGcc`, `helloSpec`), stated
as a `StdExe` and proved from `main`'s first instruction (`at_main`): one block, the call of
`puts`, one block ending in `ret`, the outcome. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program.Examples

open Silmaril.Elf.Link.Dyn Silmaril.Elf.Link.Dyn.Program

/-- `hello-gcc` as a standard executable. -/
def helloGccStd : StdExe where
  bin := helloGcc
  sha256 := "6964f3f23e27cfd2b6c26bd469cb210ff000dd359fc9988138cadc96683065c7"
  spec := helloSpec

theorem helloGccStd_ok : helloGccStd.ok = true := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Every run of `hello-gcc` writes `hello, world` and exits 0.** -/
theorem helloGccStd_verified : helloGccStd.Verified := by
  at_main helloGccStd_ok
  main_straight helloSpec

end Silmaril.Elf.Link.Dyn.Program.Examples
