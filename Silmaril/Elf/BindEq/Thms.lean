module

public import Silmaril.Proofs.Elf.BindEq.Code

/-! # The ELF API against `ElfBind`: contents and placement

PROVED (standard axioms; proofs in `Silmaril.Proofs.Elf.BindEq`):

* `Silmaril.Proofs.Elf.BindEq.phdrs_rd`: on a file that parses to `A` (x86-64, `e_phentsize = 56`),
  the loader's reader `DynElf.Elf.phdrs` returns `A.phdrs`; `etype_rd`: `e_type`;
* `codeAt_iff : Task.codeAt_iff` and `placement_iff : Task.placement_iff`: the API's `CodeAt`
  and `Placement` are `ElfBind.CodeAt` and `ElfBind.Placement`;
* `directCall_of_roLoaded'`, `directCall_of_binds`: the code a `CodeAt` (or `Binds`) row names is
  fetchable at `base + v` in memory where `ElfBind.RoLoaded F base` holds (no open goal).
-/
