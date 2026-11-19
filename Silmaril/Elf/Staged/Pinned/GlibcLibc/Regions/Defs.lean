module

public import Silmaril.Elf.Region.CFG.Function.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.Defs

/-! # An entire direct-transfer function of the pinned libc

`updwtmpx` is a nonzero-size STT_FUNC: ENDBR64 followed by a tail JMP to
`updwtmp`. Its external target is an outward label, not a synthetic return.
The entire nine-byte symbol extent is included; no terminal RET is omitted.
-/

@[expose] public section
namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.Regions
open Silmaril.Machine.Region.X86.CFG

def updwtmpxRow : Row where
  code := ⟨0x183d30, [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0x07, 0xf2, 0xff, 0xff]⟩
  fuel := 2
  listing := [⟨0x183d30, .endbr64, 4⟩, ⟨0x183d34, .jmp 0xfffff207, 5⟩]
  entry := 0x183d30
  edges := [(0x183d30, 0x183d34), (0x183d34, 0x182f40)]
  exits := [0x182f40]

def updwtmpxFunction : Silmaril.Elf.Region.CFG.FunctionRow :=
  ⟨L, 6, 103, s6_103, updwtmpxRow⟩

/-- A valid byte window which covers only the first instruction, for comparison. -/
def prefixOnly : Silmaril.Elf.Region.CFG.FunctionRow :=
  { updwtmpxFunction with cfg :=
    ⟨⟨0x183d30, [0xf3, 0x0f, 0x1e, 0xfa]⟩, 1, [⟨0x183d30, .endbr64, 4⟩],
      0x183d30, [(0x183d30, 0x183d34)], [0x183d34]⟩ }

end Silmaril.Elf.Staged.Pinned.GlibcLibc.Regions
