module

public import Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Caller.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Machine.Instructions.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Cleanup.Thms
/-! Finite successful actual address-bearing Mir execution and the unchanged
native optimizer. Source admission independently excludes calls and both native
frame pseudo-symbols; the raw address resolver has no frame-relative meaning. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Finite
open Silmaril.Compile

def reservedOverflow : String := "__ccomp_va_overflow"

/-- Syntax-only source admission; no checker, candidate run or successful
address resolution is assumed. -/
def AdmittedInstr : Mir.Instr → Prop
  | .op _ | .fop .. => True
  | .addr _ symbol _ => Ordinary symbol ∧ symbol ≠ reservedOverflow
  | _ => False

def Admitted (instructions : List Mir.Instr) : Prop :=
  ∀ instruction ∈ instructions, AdmittedInstr instruction

def AdmittedFunction (function : Mir.Func) : Prop :=
  ∀ block ∈ function.blocks.toList, Admitted block.instrs.toList

end Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Finite
