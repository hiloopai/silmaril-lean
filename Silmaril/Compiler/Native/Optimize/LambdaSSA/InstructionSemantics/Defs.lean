module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Thms
/-! Register projection for the actual namespace adapter. The older RTL frame
has no slots. Memory is kept explicit on both sides; accepted adapter operations
do not access either memory or slots. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.InstructionSemantics

open Silmaril.Compile Silmaril.Machine

def frame (source : Lir.Frame Nat) : Silmaril.Machine.RTL.Frame Nat := ⟨source.regs⟩

/-- The actual native primitive executor, with all nonprimitive MIR forms
rejected. Successful oldOp admission will exclude those forms separately. -/
def execute : Mir.Instr → Lir.Frame Nat → Lir.Memory → Option (Lir.Frame Nat × Lir.Memory)
  | .op op, source, memory => op.exec source memory
  | _, _, _ => none

end Silmaril.Compiler.Native.Optimize.LambdaSSA.InstructionSemantics
