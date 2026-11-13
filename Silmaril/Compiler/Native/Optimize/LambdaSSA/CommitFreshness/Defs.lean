module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.RenamingSemantics.Defs
/-! A structural invariant of actual source-scope and flattened register lookups.
It is initialized from real entry/output separation and extended by actual
operator-result allocations in the theorem header. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.CommitFreshness
open Silmaril.Machine.RTL.SSA

/-- The actual source scope lookup selects a defined flattened register above
`bound` for every register needed at the output boundary. -/
def FreshScope (bound : Nat) (needed : List Nat) (groups : List (List Nat))
    (env : List (List Nat)) : Prop :=
  ∀ source ∈ needed, ∀ base index offset,
    Scope.findReg groups source base = some (index, offset) →
      ∃ target, (env[index - base]?.bind (fun group => group[offset]?)) = some target ∧ bound ≤ target

end Silmaril.Compiler.Native.Optimize.LambdaSSA.CommitFreshness
