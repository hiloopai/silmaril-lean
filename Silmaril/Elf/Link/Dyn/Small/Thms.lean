module

public import Silmaril.Elf.Link.Dyn.Small.Defs
public import Silmaril.Elf.Link.Dyn.Small.Adder
public import Silmaril.Elf.Link.Dyn.Small.Libc
public import Silmaril.Raw.Elf.Link.Dyn.Small.Ret
public import Silmaril.Raw.Elf.Link.Dyn.Small.AdderGccMain
public import Silmaril.Raw.Elf.Link.Dyn.Small.AdderClangMain
public import Silmaril.Raw.Elf.Link.Dyn.Small.AdderClangLazyMain
public import Silmaril.Raw.Elf.Link.Dyn.Small.NonVacuous.Ret
public import Silmaril.Raw.Elf.Link.Dyn.Small.NonVacuous.Adder
public import Silmaril.Raw.Elf.Link.Dyn.Small.NonVacuous.AdderLazy
public import Silmaril.Raw.Elf.Link.Dyn.Small.NonVacuous.Stdio

/-! # Small dynamically linked executables (gcc and clang): theorems

`return 0`, `return 42` and an adder reading two integers with `scanf` and printing their sum with
`printf`, each built by gcc and clang (the clang adder also with lazy binding), proved end to end
over the loader relation, with non-vacuity witnesses (`NonVacuous.*`). -/
