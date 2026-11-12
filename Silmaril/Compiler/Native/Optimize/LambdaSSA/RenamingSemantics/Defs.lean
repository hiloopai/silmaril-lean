module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.InstructionSemantics.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.RestoreAdmission.Defs
/-! Concrete native-to-old register pullback for the actual reverse adapter. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.RenamingSemantics
open Silmaril.Machine

def pullback (register : Nat → Nat) (source : Lir.Frame Nat) : Silmaril.Machine.RTL.Frame Nat :=
  ⟨fun index => source.get (register index)⟩

end Silmaril.Compiler.Native.Optimize.LambdaSSA.RenamingSemantics
