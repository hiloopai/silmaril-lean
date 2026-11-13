module

public import Silmaril.Machine.X86.Decompile.SemLift.Defs
public import Silmaril.X86.Features.Machine

/-! The actual byte-summary checker and actual feature machine. The explicit state update replaces the integer core/memory of a real Features state while
retaining its actual extended fields. It supplies no direction/MMX-mode state. -/
@[expose] public section
namespace Silmaril.Machine.X86.Decompile.Features

abbrev lift (original : Silmaril.X86.Features.State) (machine : Silmaril.X86.MState) :
    Silmaril.X86.Features.MState :=
  ⟨original.setCore machine.core, machine.memory⟩

end Silmaril.Machine.X86.Decompile.Features
