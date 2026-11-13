module

public import Init

@[expose] public section

/-!
# Propositional CNF formulas and DIMACS

Literals, clauses and CNF formulas in the DIMACS convention:

* a **literal** is a nonzero integer `l`; its variable is `l.natAbs` and it is positive when
  `0 < l` (`Lit`; the integer `0` is the clause terminator of DIMACS and never a literal of a
  parsed clause);
* a **clause** is a list of literals, read as their disjunction (`Clause`); a **CNF formula** is
  a list of clauses, read as their conjunction (`CNF`);
* an **assignment** gives every variable a truth value (`Assignment := Nat → Bool`);
  `Lit.eval`, `Clause.eval`, `CNF.eval` evaluate under an assignment;
* `CNF.Sat F` (some assignment satisfies `F`), `CNF.Unsat F` (none does),
  `CNF.Implies F C` (every assignment satisfying `F` satisfies `C`).

**DIMACS** clause bodies are a stream of integers in which each clause is terminated by `0`
(`p cnf` headers and comments are not part of the stream). `Dimacs.read xs` reads a stream into
the completed clauses and the literals of a clause not yet terminated
(`Dimacs.step` is one integer of the stream, so `read` is a left fold and streaming readers can
follow it integer by integer); `Dimacs.cnf xs` is the formula of the completed clauses.

Lean core has another CNF representation (`Std.Sat.CNF`, used by `bv_decide` and its verified
LRAT checker `Std.Tactic.BVDecide.LRAT.check`); this one is the plain list form in which DIMACS
streams and Wasm memory words are read. A Silmaril addition.
-/

namespace Silmaril.Logic.SAT

/-- A DIMACS literal: variable `l.natAbs`, positive when `0 < l`. -/
abbrev Lit := Int

/-- A clause: the disjunction of its literals. -/
abbrev Clause := List Lit

/-- A CNF formula: the conjunction of its clauses. -/
abbrev CNF := List Clause

/-- A total assignment of truth values to variables. -/
abbrev Assignment := Nat → Bool

/-- The variable of a literal. -/
def Lit.var (l : Lit) : Nat := l.natAbs

/-- The polarity of a literal: `true` for a positive literal. -/
def Lit.pos (l : Lit) : Bool := decide (0 < l)

/-- The value of a literal under an assignment. -/
def Lit.eval (τ : Assignment) (l : Lit) : Bool := τ l.var == l.pos

/-- The value of a clause (a disjunction) under an assignment. -/
def Clause.eval (τ : Assignment) (C : Clause) : Bool := C.any (Lit.eval τ)

/-- The value of a formula (a conjunction) under an assignment. -/
def CNF.eval (τ : Assignment) (F : CNF) : Bool := F.all (Clause.eval τ)

/-- `F` is satisfiable. -/
def CNF.Sat (F : CNF) : Prop := ∃ τ : Assignment, F.eval τ = true

/-- `F` is unsatisfiable. -/
def CNF.Unsat (F : CNF) : Prop := ∀ τ : Assignment, F.eval τ = false

/-- `F` implies the clause `C`: every assignment satisfying `F` satisfies `C`. -/
def CNF.Implies (F : CNF) (C : Clause) : Prop :=
  ∀ τ : Assignment, F.eval τ = true → C.eval τ = true

namespace Dimacs

/-- The state of a DIMACS reader: the completed clauses, and the literals of the clause being
read. -/
abbrev State := CNF × Clause

/-- One integer of a DIMACS stream: `0` terminates the current clause, any other integer is a
literal of it. -/
def step : State → Int → State
  | (F, c), 0 => (F ++ [c], [])
  | (F, c), x => (F, c ++ [x])

/-- Read a DIMACS stream of clause bodies. -/
def read (xs : List Int) : State := xs.foldl step ([], [])

/-- The formula of the clauses of a DIMACS stream that are terminated. -/
def cnf (xs : List Int) : CNF := (read xs).1

/-- The literals of the last, unterminated clause of a stream. -/
def pending (xs : List Int) : Clause := (read xs).2

end Dimacs

end Silmaril.Logic.SAT
