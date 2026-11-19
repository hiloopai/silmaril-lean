module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.Regions.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.Functions
public import Silmaril.Elf.Staged.Reader.Thms

@[expose] public section
namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.Regions.Proofs
open Silmaril.Elf.Staged.Reader

set_option maxRecDepth 100000

theorem updwtmpx_complete : updwtmpxFunction.Valid F := by
  refine ⟨layout, ?_, by decide, by decide, rfl, rfl, rfl, ?_, ?_⟩
  · refine ⟨sh6, sh7, by decide, Or.inr rfl, by decide, by decide, ?_⟩
    exact sym_6_103.run
  · exact ⟨sh17, by decide, by decide, by decide, by decide⟩
  · exact ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
      (by decide) (by decide +kernel), by decide +kernel⟩

end Silmaril.Elf.Staged.Pinned.GlibcLibc.Regions.Proofs
