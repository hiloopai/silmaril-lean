module

public import Silmaril.Compiler.Native.Optimize.Validation.Intern.Thms
public import Silmaril.Compiler.Native.Optimize.LocalSSA.Defs
/-! Real symbolic map roots interpreted against the actual partial Lir frame.
Effectful operations and whole-validator correctness are separate obligations. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Roots
open Silmaril.Machine

def regValue (state : State) (meaning : Interpretation) (reg : Nat) : Option Lir.Word :=
  match state.regs.find? (·.1 == reg) with
  | some (_, index) => meaning.value index
  | none => meaning.input reg

def slotValue (state : State) (meaning : Interpretation) (slot : Nat) : Option Lir.Word :=
  match state.slots.find? (·.1 == slot) with
  | some (_, index) => meaning.value index
  | none => meaning.slot slot

structure Rooted (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation) : Prop where
  wellScoped : Intern.WellScoped state.nodes
  coherent : Intern.Coherent state.nodes meaning
  regsBounded : ∀ root ∈ state.regs, root.2 < state.nodes.size
  slotsBounded : ∀ root ∈ state.slots, root.2 < state.nodes.size
  regs : ∀ reg, regValue state meaning reg = frame.get reg
  slots : ∀ slot, slotValue state meaning slot = frame.slots slot

/-- Concrete agreement of partial external observers and pre-existing values. -/
structure Extends (bound : Nat) (oldMeaning newMeaning : Interpretation) : Prop where
  values : ∀ index < bound, newMeaning.value index = oldMeaning.value index
  input : newMeaning.input = oldMeaning.input
  slot : newMeaning.slot = oldMeaning.slot
  address : newMeaning.address = oldMeaning.address
  load : newMeaning.load = oldMeaning.load
  result : newMeaning.result = oldMeaning.result

structure ReadResult (before after : State) (frame : Lir.Frame Nat) (expected : Option Lir.Word)
    (index : Nat) (oldMeaning newMeaning : Interpretation) : Prop where
  rooted : Rooted after frame newMeaning
  bounded : index < after.nodes.size
  selected : newMeaning.value index = expected
  extension : Extends before.nodes.size oldMeaning newMeaning
  grows : before.nodes.size ≤ after.nodes.size
  effects : after.effects = before.effects

/-- This admitted fragment records no faulting or memory/call effects. -/
def Admitted : Lir.Op Nat → Prop
  | .const .. | .move .. | .unary .. => True
  | .binary op .. => Silmaril.Compile.Mir.DeadCode.faults op = false
  | _ => False

structure OpResult (before after : State) (frame : Lir.Frame Nat)
    (oldMeaning newMeaning : Interpretation) : Prop where
  rooted : Rooted after frame newMeaning
  extension : Extends before.nodes.size oldMeaning newMeaning
  grows : before.nodes.size ≤ after.nodes.size
  effects : after.effects = before.effects

end Silmaril.Compiler.Native.Optimize.Validation.Roots
