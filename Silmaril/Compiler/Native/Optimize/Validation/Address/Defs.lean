module

public import Silmaril.Compiler.Native.Optimize.Validation.Leaf.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Context.Thms
public import Silmaril.Compiler.Mir.FuncPass.Defs
/-! Ordinary symbolic addresses use the actual Mir resolver. The native frame
pseudo-symbol has a different interpretation and is explicitly excluded here.
This is a leaf validation foundation, not an effect replay or whole-block theorem. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Address
open Silmaril.Machine Silmaril.Compile
open Silmaril.Compile.Contract

def reservedFrame : String := "__ccomp_frame"

def Ordinary (symbol : String) : Prop := symbol ≠ reservedFrame

/-- The actual Mir address, including byte offset and 64-bit truncation.
The reserved native frame pseudo-symbol is outside this resolver's domain. -/
def resolve (units : Array Mir.Unit) (placement : MirSem.Placement)
    (symbol : String) (offset : Nat) : Option Lir.Word :=
  if symbol = reservedFrame then none else
    (MirSem.symValue units placement symbol).map (fun value => BitVec.ofNat 64 (value + offset))

/-- No direct or indirect calls are admitted by the address-leaf foundation. -/
def calls (units : Array Mir.Unit) (placement : MirSem.Placement) : OpenCalls where
  address := resolve units placement
  direct := fun _ _ _ _ _ => False
  indirect := fun _ _ _ _ _ => False

/-- Partial frame roots and total retained DAG values with a fixed real address
resolver. This does not assert the full ordered-effects replay invariant. -/
structure Invariant (units : Array Mir.Unit) (placement : MirSem.Placement)
    (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation) : Prop where
  rooted : Roots.Rooted state frame meaning
  total : Total.TotalNodes state.nodes meaning
  address : meaning.address = resolve units placement

end Silmaril.Compiler.Native.Optimize.Validation.Address
