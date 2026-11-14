module

public import Silmaril.Compiler.Native.Optimize.Validation.PureSoundness.Thms
/-! Slot reads/writes extend the checker fragment while retaining real partial slots. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Slots
open Silmaril.Machine Silmaril.Compile
open Validation.Roots

def AdmittedOp : Lir.Op Nat → Prop
  | .slotGet .. | .slotSet .. => True
  | operation => Validation.Roots.Admitted operation

def AdmittedInstr : Mir.Instr → Prop
  | .op operation => AdmittedOp operation
  | _ => False

def Admitted (instructions : List Mir.Instr) : Prop :=
  ∀ instruction ∈ instructions, AdmittedInstr instruction

structure PartialSlotReads (before after : State) (frame : Lir.Frame Nat) (slots indices : List Nat)
    (oldMeaning newMeaning : Interpretation) : Prop where
  result : OpResult before after frame oldMeaning newMeaning
  bounded : ∀ index ∈ indices, index < after.nodes.size
  selected : indices.map newMeaning.value = slots.map frame.slots


end Silmaril.Compiler.Native.Optimize.Validation.Slots
