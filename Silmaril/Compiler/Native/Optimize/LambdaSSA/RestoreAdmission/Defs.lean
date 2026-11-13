module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Defs
/-! The exact register renaming used inside actual restore. Input indices retain
actual view input names; all later indices use a separate fresh range. Bounds
are proved from the real per-function freshBase caller in the theorem header. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.RestoreAdmission

def register (base : Nat) (inputs : List Nat) (index : Nat) : Nat :=
  if index < inputs.length then inputs.getD index 0 else base + (index - inputs.length)

end Silmaril.Compiler.Native.Optimize.LambdaSSA.RestoreAdmission
