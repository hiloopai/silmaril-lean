module

public import Silmaril.Compiler.Native.Optimize.Validation.Roots.Thms
/-! Admitted instruction lists use the actual validator traversal and actual
open-Mir list semantics. Terminators and candidate-success derivation remain
separate obligations. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Lists

def AdmittedInstr : Silmaril.Compile.Mir.Instr → Prop
  | .op op => Roots.Admitted op
  | _ => False

def Admitted (instructions : List Silmaril.Compile.Mir.Instr) : Prop :=
  ∀ instruction ∈ instructions, AdmittedInstr instruction

end Silmaril.Compiler.Native.Optimize.Validation.Lists
