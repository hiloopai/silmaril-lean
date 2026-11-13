module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Source.Thms
/-! Independent syntax admission extends actual primitive operations with the
existing total word-valued floating operation. Address/calls remain excluded;
the existing Effects admission and its results are unchanged. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Floating
open Silmaril.Compile

def AdmittedInstr : Mir.Instr → Prop
  | .op _ | .fop .. => True
  | _ => False

def Admitted (instructions : List Mir.Instr) : Prop :=
  ∀ instruction ∈ instructions, AdmittedInstr instruction

end Silmaril.Compiler.Native.Optimize.Validation.Floating
