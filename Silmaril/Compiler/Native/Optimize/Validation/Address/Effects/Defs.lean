module

public import Silmaril.Compiler.Native.Optimize.Validation.Address.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Floating.Candidate.Thms
/-! Address-bearing primitive/floating source sequences share the actual
ordered-effects invariant. Candidate address replay is a separate local result;
this header makes no whole-checker, CFG or default-optimizer correctness claim. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Address.Effects
open Silmaril.Compile

def AdmittedInstr : Mir.Instr → Prop
  | .op _ | .fop .. => True
  | .addr _ symbol _ => Ordinary symbol
  | _ => False

def Admitted (instructions : List Mir.Instr) : Prop :=
  ∀ instruction ∈ instructions, AdmittedInstr instruction

end Silmaril.Compiler.Native.Optimize.Validation.Address.Effects
