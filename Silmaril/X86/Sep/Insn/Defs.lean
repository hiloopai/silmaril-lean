module

public import Silmaril.X86.Sep.Defs
public import Silmaril.X86.Ext.Machine

/-!
# Single-instruction triples: operands

Two definitions used by the instruction triples of `Sep/Insn/Thms.lean`:

* `memAt base disp`: the `X86.Ext` memory operand `disp(%base)` (no index register).
* `testFlags v`: the flags `test %r32, %r32` leaves on the value `v` (`v &&& v = v`, the
  logic flags of the low 32 bits).
-/

@[expose] public section

namespace Silmaril.X86.Sep.Insn

open Silmaril.X86 (Word Reg Flags)
open Silmaril.X86.Ext (Mem)

/-- The memory operand `disp(%base)` (no index). -/
def memAt (base : Reg) (disp : BitVec 32) : Mem := ⟨.reg base, none, disp, fun h => by cases h⟩

/-- The flags of `test %r32, %r32` on the value `v` (`v &&& v = v`). -/
def testFlags (v : Word) : Flags :=
  Silmaril.X86.Ext.logicFlagsN (v.setWidth 32)

end Silmaril.X86.Sep.Insn
