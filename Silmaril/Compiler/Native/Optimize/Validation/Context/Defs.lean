module

public import Silmaril.Compiler.Native.Optimize.Validation.PureSoundness.Thms
/-! Source-read bounds for composing checked pure blocks between different
incoming partial frames. Bounds come from the actual original function. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Context
open Silmaril.Machine Silmaril.Compile

def ReadsBelow (base : Nat) (block : Mir.Block) : Prop :=
  (∀ instruction ∈ block.instrs.toList, ∀ reg ∈ Optimize.uses instruction, reg < base) ∧
    ∀ reg ∈ Mir.DeadCode.termUses block.term, reg < base

end Silmaril.Compiler.Native.Optimize.Validation.Context
