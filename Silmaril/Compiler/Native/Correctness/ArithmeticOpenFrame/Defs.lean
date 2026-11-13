module

public import Silmaril.Compiler.Native.Correctness.ArithmeticLower.Defs
public import Silmaril.Compiler.Native.Semantics.OpenFrame.Defs
/-! Named invocation of the actual recursive arithmetic native Artifact.
The frame word remains the explicit open environment's interpretation. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.ArithmeticOpenFrame
open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Core.SignedArithmetic
open Silmaril.Compiler.Native.Semantics
open Silmaril.Compiler.Native.Correctness.ArithmeticLower

def initial (memory : Lir.Memory) : OpenFrame.State := ⟨0, .empty, memory⟩

def afterPrologue (environment : OpenFrame.Environment) (memory : Lir.Memory) : OpenFrame.State :=
  ⟨1, Lir.Frame.empty.set 0 environment.frameAddress, memory⟩

def invocation (expression : Expression) (memory : Lir.Memory) : OpenFrame.Invocation :=
  ⟨function expression, {
    name := "main", signature := ⟨.int 4 true, [], false, true⟩,
    tags := ∅, frameBytes := 0, frameAlign := 16 }, initial memory⟩

end Silmaril.Compiler.Native.Correctness.ArithmeticOpenFrame
