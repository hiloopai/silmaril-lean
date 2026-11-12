module

public import Silmaril.Libc.X86Alloc.Ladder.BoundaryTextbook.Defs
public import Silmaril.Libc.X86Alloc.Pinned.BoundaryTextbook
public import Silmaril.X86.Ladder.Pinned.Thms

/-! # Rung 08t (`boundary_textbook`): the loader facts (the `safe` row is open) -/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.BoundaryTextbook

theorem code_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.BoundaryTextbook.exe
    "rx" layout.codeAddr layout.code = true := by decide +kernel

theorem data_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.BoundaryTextbook.exe
    "rw" layout.dataAddr layout.data = true := by decide +kernel

end Silmaril.Libc.X86Alloc.Ladder.BoundaryTextbook
