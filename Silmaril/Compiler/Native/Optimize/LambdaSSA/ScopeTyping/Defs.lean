module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Admission.Defs
/-! The shape context of the actual tuples bound by an RTL translation scope.
The extra function argument is deliberately absent from this context. -/
@[expose] public section

namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.ScopeTyping
open Silmaril.Isotope.LambdaSSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Machine.RTL.SSA (Scope)
open Admission

/-- Actual bound register tuples, without a second function-argument capture. -/
def scopeContext (scope : Scope Nat) : List Shape :=
  scope.vals.map (fun registers => .tuple registers.length)


end Silmaril.Compiler.Native.Optimize.LambdaSSA.ScopeTyping
