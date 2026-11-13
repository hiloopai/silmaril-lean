module

public import Silmaril.Cerberus.Ail.Syntax.Defs
public import Silmaril.Compile.Category.Lattice

@[expose] public section

/-!
# C semantics on typed Ail: the shared syntax and observations

Every rung of the C semantics ladder (C0 integers, C1 flat memory, …, C7 the
full Cerberus semantics) is a semantics of one `Syntax`, `cSyntax`: programs are typed-Ail
programs (`Ail.TypedProgram`, closed: one translation unit with `main`), interfaces are trivial
for now, and an observation is what a process shows (`Obs`): its standard output and how it
ended (an exit status, a signal, or divergence). This is also what ccomp's runtime makes
observable (`Silmaril.Compile.Target.Interp.observe`), so the C semantics and the Mir/Lir
semantics meet through a read-back convention.

The rungs are ordered by refinement on fragments (`Syntax.RefinesOn`,
`Silmaril.Compile.Category.Lattice`): `Cᵢ ⊑[Fᵢ] Cᵢ₊₁` and, eventually, `Cᵢ ⊑[Fᵢ] ⟦·⟧`.
-/

namespace Silmaril.Compile.C.Sem

open Silmaril.Compile.Category

/-- How a process ends. -/
inductive Exit where
  /-- `exit(n)` or `return n` from `main`, reduced modulo 256. -/
  | status (n : Nat)
  /-- Killed by a signal (`SIGABRT` = 6 after `abort()`). -/
  | signal (n : Nat)
  /-- The run does not end. -/
  | diverges
  deriving DecidableEq, Repr, Inhabited

/-- What a process shows: its standard output and how it ended. -/
structure Obs where
  stdout : List UInt8
  exit : Exit
  deriving DecidableEq, Repr, Inhabited

/-- The syntax of all C semantics: closed typed-Ail programs observed as processes. -/
def cSyntax : Syntax.{0} := ⟨PUnit, Silmaril.Cerberus.Ail.TypedProgram, fun _ => ⟨⟩, Obs⟩

/-- A semantics of C. -/
abbrev Semantics : Type := cSyntax.Sem

end Silmaril.Compile.C.Sem
