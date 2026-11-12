module

public import Silmaril.Elf.Link.Dyn.Hello.Defs
public import Silmaril.Elf.Link.Dyn.Hello.Cert
public import Silmaril.Elf.Link.Dyn.Hello.Listing
public import Silmaril.Raw.Elf.Link.Dyn.Hello.GccRun
public import Silmaril.Raw.Elf.Link.Dyn.Hello.ClangRun
public import Silmaril.Raw.Elf.Link.Dyn.Hello.GccNonVacuous
public import Silmaril.Raw.Elf.Link.Dyn.Hello.GccSen

/-! # Hello world (gcc and clang), end to end: theorems

`hello_gcc` and `hello_clang` (`Raw/…/Hello/{Gcc,Clang}Run`): every run of the pinned
`hello-{gcc,clang}` (built from `examples/dyn/hello/hello.c`, pinned in `examples/dyn/pins.txt`), loaded with the pinned glibc by the loader relation, halts with
status 0 and stdout `hello, world\n` (a prefix of it if writes may fail). `gcc_nonvacuous`: the
hypotheses are met by a concrete loaded state, which has a run. `hello_gcc_sen`: the same result as a
process sentence of `Silmaril.X86.BinInstitution`. -/
