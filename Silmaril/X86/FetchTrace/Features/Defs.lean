module

public import Silmaril.X86.FetchTrace.Defs
public import Silmaril.Machine.X86.Decompile.Features.Defs
/-! The independently stated ordinary-integer instruction fragment for an
actual Features dispatch lift of a proved decoded instruction trace. -/
@[expose] public section
namespace Silmaril.X86.FetchTrace.Features
open Silmaril Silmaril.X86

def Admitted (instructions : List Ext.Instr) : Prop :=
  ∀ instruction ∈ instructions, Silmaril.X86.Features.baseRequirement instruction = none

end Silmaril.X86.FetchTrace.Features
