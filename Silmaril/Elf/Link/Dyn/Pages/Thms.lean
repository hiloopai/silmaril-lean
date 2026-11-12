module

public import Silmaril.Raw.Elf.Link.Dyn.Pages

/-! # Pages of an included file are chunks of it

`pages_of`: for every chunk size `c` and chunk list, every page lies in the file
`⟨chunksVal c len cs, chunksLen c len cs⟩` (silmaril's value of an `include_bytes` file) and
holds its bytes. Proved with the standard axioms. -/

/-! The proofs are in `Silmaril.Raw.Elf.Link.Dyn.Pages` (valid, not yet in Isar style), re-exported here. -/
