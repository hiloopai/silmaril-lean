module

public import Silmaril.X86.Sep.Insn.Defs

/-!
# Instruction forms of the allocator ladder

The allocator rungs are `gcc -O2` code of a static non-PIE executable: their globals are
reached RIP-relatively (`mov disp(%rip), %rax`, `mov %rdi, disp(%rip)`), which
`Silmaril.X86.Sep.Insn` does not cover (its memory forms take a base register).

* `ripMem disp`: the operand `disp(%rip)`.

The triples are in `Silmaril.Libc.X86Alloc.Insn.Thms`.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Insn

/-- The RIP-relative operand `disp(%rip)`. -/
def ripMem (disp : BitVec 32) : Silmaril.X86.Ext.Mem := ⟨.rip, none, disp, fun _ => rfl⟩

end Silmaril.Libc.X86Alloc.Insn
