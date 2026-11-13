module

public import Silmaril.Compiler.Native.Semantics.OpenFrame.Defs
public import Silmaril.Compiler.Mir.JumpThread.Defs
/-! Actual bounded jump threading with explicit native open meanings.
Only terminator labels change; instruction effects, frames and memory remain exact. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Open.JumpThread

open Silmaril.Compile

/-- The exact block transformation used by the actual function pass. -/
def threadedBlock (function : Mir.Func) (block : Mir.Block) : Mir.Block :=
  { block with term := Mir.JumpThread.threadTerm function block.term }

/-- The exact selected successor of a threaded terminator. -/
def threadedExit (function : Mir.Func) : BlockExit → BlockExit
  | .jump label => .jump (Mir.JumpThread.dest function label)
  | .returned values => .returned values
  | .trapped => .trapped

end Silmaril.Compiler.Native.Optimize.Open.JumpThread
