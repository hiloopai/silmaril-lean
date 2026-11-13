module

public import Silmaril.Compiler.Native.Semantics.OpenFrame.Defs
public import Silmaril.Compiler.Native.Correctness.AdditionLower.Defs
/-! Actual independently bounded addition in explicit open-frame semantics.
The compiled Artifact is unchanged; frame/ABI realization stays external. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionOpenFrame

open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Native.Semantics

def initial (memory : Lir.Memory) : OpenFrame.State := ⟨0, .empty, memory⟩

def afterPrologue (environment : OpenFrame.Environment) (memory : Lir.Memory) : OpenFrame.State :=
  ⟨1, Lir.Frame.empty.set 0 environment.frameAddress, memory⟩

def invocation (left right : Lir.Word) (memory : Lir.Memory) : OpenFrame.Invocation :=
  ⟨AdditionLower.function left right, {
    name := "main", signature := ⟨.int 4 true, [], false, true⟩,
    tags := ∅, frameBytes := 0, frameAlign := 16 }, initial memory⟩

end Silmaril.Compiler.Native.Correctness.AdditionOpenFrame
