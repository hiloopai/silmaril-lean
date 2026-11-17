module

public import Silmaril.Cerberus.TV.Validate.Defs
public import Silmaril.Compiler.Native.Correctness.AdditionSource.Defs

/-!
# Whole-program validation examples over elaborated Core

The programs are the Core files of `int main(void) { return a + b; }` that the Lean port of
Cerberus's elaborator produces for the LP64 primitive configuration with the explicitly
constructed conversion runtime (`Silmaril.Compiler.Native.Correctness.AdditionSource`): the
actual elaborated arithmetic, including the unsequenced evaluation of both operands, the
`catch_exceptional_condition` overflow check and the return through the saved return label.
Comparing two of them is the shape of validating a constant-folding step on Core.

They are closed (no arguments), deterministic up to the unsequenced operand evaluation, and
small; they are examples of the validator's statements, not a corpus. Programs with memory,
calls, loops and output are the next corpus stage (docs/projects/c-tv.md).
-/

@[expose] public section

namespace Silmaril.Project.CTV.Examples

open Silmaril.Cerberus
open Silmaril.Cerberus.TV
open Silmaril.Compiler.Native.Correctness

/-- `int main(void) { return a + b; }` as elaborated Core. -/
def add (a b : Int) : Closed := ⟨(AdditionSource.bindings a b).toFile, ∅, []⟩

/-- The same file without a `main` symbol: its startup ends in an `error` gap. -/
def noMain : Closed := ⟨{ (add 1 2).file with main := none }, ∅, []⟩

/-- `INT_MAX + 1`: signed overflow, undefined behaviour (C11 §6.5p5). -/
def overflow : Closed := add 2147483647 1

/-- An implementation whose exit status keeps only the low bit (a deliberately unusual host, to
show that observations depend on the implementation-defined choices). -/
def lowBitHost : Spec.Impl := { status := fun n => (n % 2).toNat }

end Silmaril.Project.CTV.Examples
