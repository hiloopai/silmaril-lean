module

public import Silmaril.Compiler.Native.Optimize.Validation.Finite.Defs
/-! A reusable bridge between actual Mir steps and the independent open-block
instruction relation. Concrete instances prove both directions; final compiler
statements need not assume an arbitrary address or call interpretation. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Machine.Instructions
open Silmaril.Machine Silmaril.Compile Silmaril.Compile.Contract

/-- An admitted instruction has exactly the actual straight-line machine effect.
Completeness starts from nonstuckness and determines the entire next-state
shape, including unchanged function, label and stack. -/
structure Bridge (units : Array Mir.Unit) (placement : MirSem.Placement)
    (calls : OpenCalls) (admitted : Mir.Instr → Prop) : Prop where
  sound : ∀ (function : Mir.Func) (label index : Nat) (block : Mir.Block)
    (instruction : Mir.Instr), function.blocks[label]? = some block →
    block.instrs[index]? = some instruction → admitted instruction →
    ∀ (frame finalFrame : Lir.Frame Nat) (stack : List MirSem.Act)
      (memory finalMemory : Lir.Memory),
    InstructionExec calls instruction frame memory finalFrame finalMemory →
    MirSem.Step units placement ⟨function, label, index, frame, stack, memory⟩
      ⟨function, label, index + 1, finalFrame, stack, finalMemory⟩
  complete : ∀ (function : Mir.Func) (label index : Nat) (block : Mir.Block)
    (instruction : Mir.Instr), function.blocks[label]? = some block →
    block.instrs[index]? = some instruction → admitted instruction →
    ∀ (frame : Lir.Frame Nat) (stack : List MirSem.Act) (memory : Lir.Memory),
    MirSem.step units placement ⟨function, label, index, frame, stack, memory⟩ ≠ .stuck →
    ∃ finalFrame finalMemory,
      InstructionExec calls instruction frame memory finalFrame finalMemory ∧
      MirSem.step units placement ⟨function, label, index, frame, stack, memory⟩ =
        .running ⟨function, label, index + 1, finalFrame, stack, finalMemory⟩

end Silmaril.Compiler.Native.Optimize.Validation.Machine.Instructions
