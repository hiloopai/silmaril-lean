module

public import Silmaril.Logic.SAT.CNF.Defs

@[expose] public section

/-!
# A reference LRAT checker (RUP and RAT steps)

An **LRAT proof** of the unsatisfiability of a CNF formula `F` is a list of steps (`Step`):

* `add id lits hints`: add the clause `lits` under the id `id`, justified by **reverse unit
  propagation** (RUP) along the clauses `hints`, in order;
* `del ids`: remove the clauses with these ids from the database;
* `rat id lits groups`: add the clause `lits` under the id `id`, justified by **resolution
  asymmetric tautology** (RAT) on its first literal, one group of RUP hints per candidate.

The **clause database** (`DB`) is a list of `(id, clause)` pairs, newest first; `lookup` finds the
first (newest) clause with an id. Initially it holds the input clauses numbered `1, 2, …, n` in
order (`init 1 F`, the LRAT convention).

The **RUP check** of `add id lits hints` (`rup`) starts from the partial assignment falsifying
every literal of `lits` (a partial assignment is the list of literals assumed true; `lits.map
(- ·)`). For each hint in order it looks the clause up (a missing id fails) and keeps its
literals not falsified by the current partial assignment (`unfalsified`): none is a conflict
(the step succeeds), exactly one becomes true and is assumed, more than one fails. Hints
exhausted without a conflict fail.

The DIMACS integer `0` is not a literal: a step whose clause contains `0` fails, and so does a
hint whose remaining literal is `0` (`Lit.eval` reads `0` as a literal of variable `0`, which is
not the negation of `-0 = 0`, so assuming it would be unsound).

The **RAT check** of `rat id lits groups` (`ratOk`) takes the first literal `p` of `lits` as
the pivot. For every database entry `(j, D)` with `-p ∈ D` (every entry, also one shadowed by a
newer entry with the same id), some group `(j, hs)` must justify the resolvent
`lits ++ (D without -p)` by a RUP check (`addOk`) along `hs`. Unlike LRAT's text format, a group
carries all its hints: hints shared by every group (LRAT's hints before the first negative id)
are repeated in each group. A RAT clause need not be implied by the database, but adding it keeps the
database satisfiable (`ratOk_sat`); so `check` is sound by the invariant "the database is
unsatisfiable" read backwards from the empty clause.

`check F proof` runs the steps from `init 1 F`; it is `true` iff every step up to a step adding
the empty clause succeeds. A failing step is fatal. Steps after the empty clause are ignored.
Soundness, `check F proof = true → F.Unsat`, is in `Silmaril.Logic.SAT.LRAT.Thms`. Lean core's
`Std.Tactic.BVDecide.LRAT` checker (over `Std.Sat.CNF`) is not related to this one. A Silmaril
addition.
-/

namespace Silmaril.Logic.SAT.LRAT

/-- One LRAT step. -/
inductive Step where
  /-- Add the clause `lits` with id `id`, by RUP along the clauses `hints`. -/
  | add (id : Nat) (lits : Clause) (hints : List Nat)
  /-- Delete the clauses with ids `ids`. -/
  | del (ids : List Nat)
  /-- Add the clause `lits` with id `id` by **RAT** on its first literal `p` (the pivot): for
  every database clause `D` containing `-p`, a group `(j, hints)` with the id `j` of `D` whose
  hints refute, by RUP, the resolvent `lits ++ (D without -p)`. -/
  | rat (id : Nat) (lits : Clause) (groups : List (Nat × List Nat))
  deriving DecidableEq, Repr

/-- A clause database: `(id, clause)` pairs, newest first. -/
abbrev DB := List (Nat × Clause)

/-- The input clauses numbered `n, n + 1, …` in order. -/
def init : Nat → CNF → DB
  | _, [] => []
  | n, C :: F => (n, C) :: init (n + 1) F

/-- The newest clause with id `i`. -/
def lookup : DB → Nat → Option Clause
  | [], _ => none
  | (j, C) :: db, i => if j == i then some C else lookup db i

/-- Remove the clauses with ids in `ids`. -/
def delete (db : DB) (ids : List Nat) : DB := db.filter fun p => !ids.contains p.1

/-- The literals of `D` not falsified by the partial assignment `σ` (the literals assumed
true): those `l` with `-l ∉ σ`. -/
def unfalsified (σ : List Lit) (D : Clause) : Clause := D.filter fun l => !σ.contains (-l)

/-- Reverse unit propagation along the hints from the partial assignment `σ`: `true` iff a hint
clause becomes a conflict, each earlier hint clause being unit with a nonzero literal. -/
def rup (db : DB) : List Lit → List Nat → Bool
  | _, [] => false
  | σ, h :: hs =>
    match lookup db h with
    | none => false
    | some D =>
      match unfalsified σ D with
      | [] => true
      | [u] => u != 0 && rup db (u :: σ) hs
      | _ => false

/-- A RUP addition of `lits` along `hints` is valid: no literal is `0`, and propagation from the
assignment falsifying `lits` reaches a conflict. -/
def addOk (db : DB) (lits : Clause) (hints : List Nat) : Bool :=
  !lits.contains 0 && rup db (lits.map (- ·)) hints

/-- The resolvent of the RAT candidate `D` with the clause `lits` on the pivot `p`:
`lits ++ (D without -p)`. -/
def resolvent (lits : Clause) (p : Lit) (D : Clause) : Clause := lits ++ D.filter (· != -p)

/-- A RAT addition of `lits` (pivot: its first literal `p`) along `groups` is valid: `lits` is
nonempty without `0`, and every database entry `(j, D)` with `-p ∈ D` has a group `(j, hs)`
along which the resolvent passes `addOk` (no `0`, RUP conflict). Every entry is a candidate,
including entries shadowed by a newer one with the same id. -/
def ratOk (db : DB) (lits : Clause) (groups : List (Nat × List Nat)) : Bool :=
  match lits with
  | [] => false
  | p :: _ => !lits.contains 0 && db.all fun e =>
      !e.2.contains (-p) || groups.any fun g => g.1 == e.1 && addOk db (resolvent lits p e.2) g.2

/-- Run the steps of a proof on a database: `true` iff every step up to one adding the empty
clause succeeds. -/
def run : DB → List Step → Bool
  | _, [] => false
  | db, .add id lits hints :: ps =>
    addOk db lits hints &&
      match lits with
      | [] => true
      | _ :: _ => run ((id, lits) :: db) ps
  | db, .del ids :: ps => run (delete db ids) ps
  | db, .rat id lits groups :: ps => ratOk db lits groups && run ((id, lits) :: db) ps

/-- The clauses of a database (every entry, shadowed or not). -/
def clauses (db : DB) : CNF := db.map Prod.snd

/-- The check of one step on a database (`run` performs it and stops on failure). -/
def Step.ok : DB → Step → Bool
  | db, .add _ lits hints => addOk db lits hints
  | _, .del _ => true
  | db, .rat _ lits groups => ratOk db lits groups

/-- The database after one step. -/
def Step.apply : DB → Step → DB
  | db, .add id lits _ => (id, lits) :: db
  | db, .del ids => delete db ids
  | db, .rat id lits _ => (id, lits) :: db

/-- Check an LRAT (RUP and RAT) refutation of `F`: the input clauses get ids `1, …, n`. -/
def check (F : CNF) (proof : List Step) : Bool := run (init 1 F) proof

end Silmaril.Logic.SAT.LRAT
