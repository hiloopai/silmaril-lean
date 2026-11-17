module

public import Silmaril.Logic.Institution.Examples.Unsorted
public import Silmaril.Logic.Concrete.SExp.Defs

/-!
# First-order logic as S-expressions (presentation `silmaril.fol.formula`, version 1)

A concrete presentation of unsorted first-order logic (`Silmaril.Logic.Institution.Examples.UFOL`:
de Bruijn terms and formulas over a signature) over a **named signature**: operation and relation
symbols are strings, with arities given by `opArity` and `relArity` (`named`).

```
term    ::= (var i) | (app f term*)
formula ::= true | (= term term) | (rel r term*) | (not formula) | (and formula formula)
          | (forall formula)
```

`(var i)` is a de Bruijn index, well formed below the number of variables in scope; `forall` binds
one variable. `(app f t₁ … tₙ)` is well formed when `f` is an operation symbol of arity `n`
(likewise `rel`). The decoder accepts exactly the canonical forms (`Thms`).
-/

@[expose] public section

namespace Silmaril.Logic.Institution.Examples.UFOL

/-- **A named signature**: symbols are strings, with their arities. -/
def named (opArity relArity : String → Option ℕ) : Signature where
  Op n := {f : String // opArity f = some n}
  Rel n := {r : String // relArity r = some n}

namespace SExp

open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Concrete.SExp (num num?)

variable {opArity relArity : String → Option ℕ}

/-- The concrete form of a term. -/
def encodeTerm {k : ℕ} : Term (named opArity relArity) k → SE
  | .var i => .list [.atom "var", num i.val]
  | .app (n := n) o args => .list (.atom "app" :: .atom o.1 :: List.ofFn fun j : Fin n => encodeTerm (args j))

mutual
/-- Read the grammar of terms with `k` variables in scope. -/
def readTerm? (opArity relArity : String → Option ℕ) (k : ℕ) :
    SE → Option (Term (named opArity relArity) k)
  | .list [.atom "var", i] => (num? i).bind fun m => if h : m < k then some (.var ⟨m, h⟩) else none
  | .list (.atom "app" :: .atom f :: args) =>
      match h : opArity f with
      | some n => (readTerms? opArity relArity k args).bind fun ts =>
          if hl : ts.length = n then some (.app (n := n) ⟨f, h⟩ fun j => ts.get ⟨j, hl ▸ j.isLt⟩)
          else none
      | none => none
  | _ => none
/-- Read a list of terms. -/
def readTerms? (opArity relArity : String → Option ℕ) (k : ℕ) :
    List SE → Option (List (Term (named opArity relArity) k))
  | [] => some []
  | t :: ts => do return (← readTerm? opArity relArity k t) :: (← readTerms? opArity relArity k ts)
end

/-- The concrete form of a formula. -/
def encodeFormula : {k : ℕ} → Formula (named opArity relArity) k → SE
  | _, .eq t u => .list [.atom "=", encodeTerm t, encodeTerm u]
  | _, .rel (n := n) r args =>
      .list (.atom "rel" :: .atom r.1 :: List.ofFn fun j : Fin n => encodeTerm (args j))
  | _, .tt => .atom "true"
  | _, .not φ => .list [.atom "not", encodeFormula φ]
  | _, .and φ ψ => .list [.atom "and", encodeFormula φ, encodeFormula ψ]
  | _, .all φ => .list [.atom "forall", encodeFormula φ]

/-- Read the grammar of formulas with `k` variables in scope. -/
def readFormula? (opArity relArity : String → Option ℕ) :
    (k : ℕ) → SE → Option (Formula (named opArity relArity) k)
  | k, .list [.atom "=", t, u] =>
      do return .eq (← readTerm? opArity relArity k t) (← readTerm? opArity relArity k u)
  | k, .list (.atom "rel" :: .atom r :: args) =>
      match h : relArity r with
      | some n => (readTerms? opArity relArity k args).bind fun ts =>
          if hl : ts.length = n then some (.rel (n := n) ⟨r, h⟩ fun j => ts.get ⟨j, hl ▸ j.isLt⟩)
          else none
      | none => none
  | _, .atom "true" => some .tt
  | k, .list [.atom "not", φ] => (readFormula? opArity relArity k φ).map .not
  | k, .list [.atom "and", φ, ψ] =>
      do return .and (← readFormula? opArity relArity k φ) (← readFormula? opArity relArity k ψ)
  | k, .list [.atom "forall", φ] => (readFormula? opArity relArity (k + 1) φ).map .all
  | _, _ => none

/-- **Decode a formula**: the formula a canonical form denotes. -/
def decodeFormula (opArity relArity : String → Option ℕ) (k : ℕ) (e : SE) :
    Option (Formula (named opArity relArity) k) :=
  (readFormula? opArity relArity k e).bind fun φ => if encodeFormula φ = e then some φ else none

end SExp

end Silmaril.Logic.Institution.Examples.UFOL
