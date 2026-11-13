module

public import Silmaril.Compiler.Native.Optimize.Validation.Candidate.Thms
/-! Shared partial-leaf reasoning for the unchanged executable checker.
External address meanings are parameters, not silently completed globals. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Leaf
open Silmaril.Machine

/-- Generalize only the external address field of the initial partial meaning.
Registers/slots remain the real Option maps; every initial DAG/load/result is absent. -/
def initialMeaning (frame : Lir.Frame Nat) (address : String → Nat → Option Lir.Word) : Interpretation :=
  { Total.initialMeaning frame with address }

end Silmaril.Compiler.Native.Optimize.Validation.Leaf
