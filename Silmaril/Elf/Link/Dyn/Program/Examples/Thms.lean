module

public import Silmaril.Elf.Link.Dyn.Program.Thms
public import Silmaril.Raw.Elf.Link.Dyn.Program.Examples.Hello
public import Silmaril.Raw.Elf.Link.Dyn.Program.Examples.HelloNonVacuous
public import Silmaril.Raw.Elf.Link.Dyn.Program.Examples.CatStdin
public import Silmaril.Raw.Elf.Link.Dyn.Program.Examples.CatFile
public import Silmaril.Raw.Elf.Link.Dyn.Program.Examples.CatFileNonVacuous

/-! # Program API examples: theorems

`helloGcc_verified`, `catStdinGcc_verified`, `catFileGcc_verified`: `Program.Verified` for
hello-gcc, cat-stdin-gcc and cat-file-gcc (`examples/dyn/ladder`); `helloGcc_premises`,
`catFileGcc_premises`: concrete instances of their premises (`catFileGcc_s0`: cat-file's
conclusion for one; `cfAtMain_sat`: its world's `World.atMain` is met by a memory holding the
streams in `slotRep`'s encoding). -/
