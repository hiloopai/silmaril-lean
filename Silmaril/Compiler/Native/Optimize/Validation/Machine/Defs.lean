module

public import Silmaril.Compiler.Native.Optimize.Validation.Context.Thms
public import Silmaril.Compiler.Mir.FuncPass.Defs
/-! Exact independent Mir machine outcomes at local block boundaries. Caller
return writes retain their real partial failure, rather than being completed. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Machine
open Silmaril.Machine Silmaril.Compile
open Silmaril.Compile.Contract

def termOut : BlockExit → Mir.FuncPass.TermOut
  | .jump label => .goto label
  | .returned words => .ret words
  | .trapped => .trap

/-- The real Mir return continuation may itself fail a caller write. This exact
result is retained rather than treating every local return as whole-program termination. -/
def finish (state : MirSem.State) : BlockExit → MirSem.Result
  | .jump label => .running { state with label, index := 0 }
  | .returned words =>
    match state.stack with
    | [] => .returned words state.mem
    | caller :: rest =>
      match caller.frame.writeAll (caller.results.map .reg) words with
      | some frame => .running ⟨caller.func, caller.label, caller.index + 1, frame, rest, state.mem⟩
      | none => .stuck
  | .trapped => .trapped state.mem

end Silmaril.Compiler.Native.Optimize.Validation.Machine
