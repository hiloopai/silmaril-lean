module

public import Silmaril.Elf.Staged.Pinned.HelloGcc.Regions.Defs
public import Silmaril.Elf.Staged.Pinned.HelloGcc.Thms
public import Silmaril.Elf.Staged.Reader.Thms

/-! # Kernel-checked byte and direct-CFG certificates

Both byte windows are read from the same included corpus file. The remaining
execution, load-bias, fetch and interference assumptions are separate contracts.
-/

set_option maxRecDepth 100000

@[expose] public section
namespace Silmaril.Elf.Staged.Pinned.HelloGcc.Regions
open Silmaril.Elf.Staged.Reader

theorem compare_certified : Silmaril.Elf.Region.CFG.Valid F compareRow :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3) (by decide) (by decide +kernel),
    by decide +kernel⟩

theorem tail_certified : Silmaril.Elf.Region.CFG.Valid F tailRow :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3) (by decide) (by decide +kernel),
    by decide +kernel⟩

end Silmaril.Elf.Staged.Pinned.HelloGcc.Regions
