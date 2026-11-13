module

public import Silmaril.Compiler.Native.Optimize.Validation.Finite.Defs
public import Silmaril.Compiler.Native.Optimize.Defs
/-! Exact actual-start behavior and initial-memory preservation of the concrete
cleanup stages and their real compiler composition, at the same placement. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Cleanup
open Silmaril.Machine Silmaril.Compile
open Silmaril.Compile.Contract

/-- Every behavior is the existing raw machine relation from actual startup. -/
def ProgramBehaves (units : Array Mir.Unit) (placement : MirSem.Placement) (size : Nat)
    (behavior : Lir.Behavior) : Prop :=
  ∃ state, MirSem.start units placement size = some state ∧ MirSem.Behaves units placement state behavior

/-- Same actual placement, startup size, returned words and final memory.
Only stuck source behaviors are excluded by this concrete cleanup interface. -/
def Preserves (transform : Array Mir.Unit → Array Mir.Unit) : Prop :=
  ∀ units placement size behavior, behavior ≠ .stuck →
    ProgramBehaves units placement size behavior → ProgramBehaves (transform units) placement size behavior

def KeepsInitialMemory (transform : Array Mir.Unit → Array Mir.Unit) : Prop :=
  ∀ units placement size, MirSem.initMem (transform units) placement size = MirSem.initMem units placement size

end Silmaril.Compiler.Native.Optimize.Validation.Cleanup
