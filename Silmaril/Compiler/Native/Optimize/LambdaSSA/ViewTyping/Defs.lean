module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.ScopeTyping.Defs
/-! Static current-version availability and actual arithmetic-view prefix coverage.
No successful execution is required by these predicates. -/
@[expose] public section

namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.ViewTyping
open Silmaril.Machine.RTL.SSA (Scope)

/-- Every recorded current version is an actual in-scope register. -/
def Available (scope : Scope Nat) (state : Rename) : Prop :=
  ∀ pair ∈ state.versions, scope.HasReg pair.2

/-- Each version after allocation is old or among the actual emitted names. -/
def Allocates (before after : Rename) (emitted : List Nat) : Prop :=
  ∀ pair ∈ after.versions, pair ∈ before.versions ∨ pair.2 ∈ emitted

/-- Every translated instruction reads only the tuples bound before it. -/
def PrefixCovers (scope : Scope Nat) : List Old.Op → Prop
  | [] => True
  | instruction :: rest => scope.Covers instruction.uses ∧
      PrefixCovers (scope.push instruction.defs) rest

/-- The actual tuple bound on entry to the arithmetic block. -/
def entryScope (inputs : List Nat) : Scope Nat := ⟨[inputs], [(none, 1)]⟩

/-- The exact single arithmetic function assembled by `view`. -/
def singleFunction (inputs : List Nat) (instructions : List Old.Op) (outputs : List Nat) : Old.Func :=
  { sig := ⟨inputs.length, outputs.length⟩, entry := 0,
    blocks := [⟨inputs, instructions, .ret outputs⟩] }

end Silmaril.Compiler.Native.Optimize.LambdaSSA.ViewTyping
