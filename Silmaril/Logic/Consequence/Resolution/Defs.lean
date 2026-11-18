module

public import Silmaril.Logic.Consequence.Derivation.Defs
public import Silmaril.Logic.Smt.SExpr.Defs

/-!
# Propositional clause reasoning over SMT terms: a derivation system

The fragment of Alethe proofs (`Silmaril.ProofFormats.Alethe`) that this repository checks, as a
derivation system in the sense of `Silmaril.Logic.Consequence.Derivation`.

**Terms and truth.** Terms are S-expressions (`SE`, SMT-LIB syntax). A valuation `v : SE → Prop`
interprets *atoms*; `Holds v t` interprets the Boolean connectives `true`, `false`, `(not a)`,
`(or a…)` and `(and a…)` and treats every other term as an atom. So a refutation here shows that no
assignment of truth values to the atoms satisfies the assumptions: **propositional**
unsatisfiability, which implies unsatisfiability for every SMT interpretation that respects these
connectives. Nothing is claimed about theory reasoning.

**Judgments** are clauses (`Clause := List SE`, a disjunction); a clause holds when one of its
literals does.

**Rules** (`Rule`), each computing its conclusion from its premises (`Rule.apply`); a step is an
instance when the computed clause is a sub*set* of the stated conclusion (`Instance`), which allows
weakening, reordering and duplicates:

| rule | premises | computed conclusion |
|---|---|---|
| `resolution ps` | `c₁ … cₙ` | resolve left to right on the pivots `ps` (`(p, true)`: `p` in the left clause, `(not p)` in the right; `(p, false)`: the reverse) |
| `orElim` | `[(or a₁ … aₙ)]` | `[a₁ … aₙ]` |
| `andElim i` | `[(and a₁ … aₙ)]` | `[aᵢ]` |
| `notOrElim i` | `[(not (or a₁ … aₙ))]` | `[(not aᵢ)]` |
| `orPos as` | — | `[(not (or as…)), a₁ … aₙ]` |
| `orNeg as i` | — | `[(or as…), (not aᵢ)]` |
| `andPos as i` | — | `[(not (and as…)), aᵢ]` |
| `andNeg as` | — | `[(and as…), (not a₁) … (not aₙ)]` |
| `contraction` | `[c]` | `c` |
| `trueTaut`, `falseTaut` | — | `[true]`, `[(not false)]` |

A pivot that does not occur as required makes the step fail.
-/

@[expose] public section

namespace Silmaril.Consequence.Resolution

open Silmaril.Logic.Smt (SE)

/-- A clause: a disjunction of terms. -/
abbrev Clause := List SE

mutual

/-- **Truth of a term** under a valuation of atoms. -/
def Holds (v : SE → Prop) : SE → Prop
  | .atom "true" => True
  | .atom "false" => False
  | .list [.atom "not", a] => ¬ Holds v a
  | .list (.atom "or" :: as) => HoldsAny v as
  | .list (.atom "and" :: as) => HoldsAll v as
  | t => v t

/-- Some term of the list holds. -/
def HoldsAny (v : SE → Prop) : List SE → Prop
  | [] => False
  | a :: as => Holds v a ∨ HoldsAny v as

/-- Every term of the list holds. -/
def HoldsAll (v : SE → Prop) : List SE → Prop
  | [] => True
  | a :: as => Holds v a ∧ HoldsAll v as

end

/-- A clause holds when one of its terms does. -/
def ClauseHolds (v : SE → Prop) (c : Clause) : Prop := ∃ t ∈ c, Holds v t

/-- `(not t)`. -/
def neg (t : SE) : SE := .list [.atom "not", t]

/-- `(or as…)`. -/
def mkOr (as : List SE) : SE := .list (.atom "or" :: as)

/-- `(and as…)`. -/
def mkAnd (as : List SE) : SE := .list (.atom "and" :: as)

/-- Resolve `c` and `d` on `p`: `p` from `c` and `(not p)` from `d` when `pos`, else the
reverse. Fails when the pivot literals are absent. -/
def resolve (pos : Bool) (p : SE) (c d : Clause) : Option Clause :=
  let (l, r) := if pos then (p, neg p) else (neg p, p)
  if l ∈ c ∧ r ∈ d then some (c.filter (· ≠ l) ++ d.filter (· ≠ r)) else none

/-- Resolve a chain of clauses left to right on the pivots. -/
def resolveChain : Clause → List (SE × Bool) → List Clause → Option Clause
  | c, [], [] => some c
  | c, (p, pos) :: ps, d :: ds => (resolve pos p c d).bind fun c' => resolveChain c' ps ds
  | _, _, _ => none

/-- The rule labels of the fragment. -/
inductive Rule where
  | resolution (pivots : List (SE × Bool))
  | orElim
  | andElim (i : ℕ)
  | notOrElim (i : ℕ)
  | orPos (as : List SE)
  | orNeg (as : List SE) (i : ℕ)
  | andPos (as : List SE) (i : ℕ)
  | andNeg (as : List SE)
  | contraction
  | trueTaut
  | falseTaut
  deriving DecidableEq

/-- **The computed conclusion** of a rule on its premises, when it applies. -/
def Rule.apply : Rule → List Clause → Option Clause
  | .resolution ps, c :: ds => resolveChain c ps ds
  | .orElim, [[.list (.atom "or" :: as)]] => some as
  | .andElim i, [[.list (.atom "and" :: as)]] => as[i]?.map ([·])
  | .notOrElim i, [[.list [.atom "not", .list (.atom "or" :: as)]]] => as[i]?.map (fun a => [neg a])
  | .orPos as, [] => some (neg (mkOr as) :: as)
  | .orNeg as i, [] => as[i]?.map fun a => [mkOr as, neg a]
  | .andPos as i, [] => as[i]?.map fun a => [neg (mkAnd as), a]
  | .andNeg as, [] => some (mkAnd as :: as.map neg)
  | .contraction, [c] => some c
  | .trueTaut, [] => some [.atom "true"]
  | .falseTaut, [] => some [neg (.atom "false")]
  | _, _ => none

/-- **The derivation system**: a step is an instance when its rule applies to its premises and
every computed literal is in the stated conclusion. -/
def system : DerivationSystem Clause where
  Rule := Rule
  Instance r ps c := ∃ d, r.apply ps = some d ∧ ∀ t ∈ d, t ∈ c

instance : ∀ r ps c, Decidable (system.Instance r ps c) := fun r ps c =>
  match h : r.apply ps with
  | some d => decidable_of_iff (∀ t ∈ d, t ∈ c) (by simp [system, h])
  | none => .isFalse (by simp [system, h])

end Silmaril.Consequence.Resolution
