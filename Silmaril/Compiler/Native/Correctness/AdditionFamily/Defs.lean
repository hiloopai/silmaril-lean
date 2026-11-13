module

public import Silmaril.Compiler.Native.Correctness.AdditionMain.Defs
public import Silmaril.Compiler.Native.Correctness.AdditionText.Defs
/-! Independent signed32 addition input domain for the actual O0 native driver.
The source retains the constructed conversion runtime and explicit partial
Linux LP64 profile. This is not an arbitrary-C or external-toolchain domain. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionFamily

abbrev source := AdditionSource.source

/-- Only mathematical bounds and exact independently fixed source inputs
select membership. No acceptance, source run or target behavior is supplied. -/
def domain (candidate : Source) : Prop :=
  ∃ left right, AdditionSource.Bounds left right ∧ candidate = source left right

/-- Independently stated full native driver text and its real process argv. -/
def target (left right : Int) : Target :=
  ⟨AdditionText.assembly (BitVec.ofInt 64 left) (BitVec.ofInt 64 right), ["a.out"]⟩

/-- The independent full grammar/layout/encoding relation and concrete loader,
without successful execution or membership in a compiler image as a premise. -/
abbrev Loads := AdditionText.Loads

end Silmaril.Compiler.Native.Correctness.AdditionFamily
