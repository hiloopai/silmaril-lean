module

public import Silmaril.Logic.Arithmetic.Syntax
public import Silmaril.Logic.Concrete.SExp.Defs

/-!
# First-order arithmetic as S-expressions (presentation `silmaril.arithmetic.formula`, version 1)

The default concrete presentation of the language of Peano and Robinson arithmetic
(`Silmaril.Logic.Arithmetic`: `Term n`, `Formula n` with `n` de Bruijn variables in scope).

```
term    ::= (var i) | zero | (succ term) | (+ term term) | (* term term)
formula ::= false | (= term term) | (-> formula formula) | (and formula formula)
          | (or formula formula) | (forall formula) | (exists formula)
```

`(var i)` is the de Bruijn index `i` (`0` is the innermost binder); it is well formed only when
`i` is below the number of variables in scope. `forall` and `exists` bind one variable in their
argument. Numerals are canonical decimals. A sentence is a formula with no variable in scope.

`decodeFormula n` accepts exactly the canonical forms (`Thms`: `decodeFormula_eq_some_iff`), and
every printed atom is legal, so the byte round trip holds for every formula (`Thms`).
-/

@[expose] public section

namespace Silmaril.Logic.Arithmetic.SExp

open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Concrete.SExp (num num?)

/-- The concrete form of a term. -/
def encodeTerm : {n : ℕ} → Term n → SE
  | _, .var i => .list [.atom "var", num i.val]
  | _, .zero => .atom "zero"
  | _, .succ t => .list [.atom "succ", encodeTerm t]
  | _, .add s t => .list [.atom "+", encodeTerm s, encodeTerm t]
  | _, .mul s t => .list [.atom "*", encodeTerm s, encodeTerm t]

/-- Read the grammar of terms with `n` variables in scope. -/
def readTerm? (n : ℕ) : SE → Option (Term n)
  | .list [.atom "var", i] => (num? i).bind fun k => if h : k < n then some (.var ⟨k, h⟩) else none
  | .atom "zero" => some .zero
  | .list [.atom "succ", t] => (readTerm? n t).map .succ
  | .list [.atom "+", s, t] => do return .add (← readTerm? n s) (← readTerm? n t)
  | .list [.atom "*", s, t] => do return .mul (← readTerm? n s) (← readTerm? n t)
  | _ => none

/-- The concrete form of a formula. -/
def encodeFormula : {n : ℕ} → Formula n → SE
  | _, .bot => .atom "false"
  | _, .equal s t => .list [.atom "=", encodeTerm s, encodeTerm t]
  | _, .imp φ ψ => .list [.atom "->", encodeFormula φ, encodeFormula ψ]
  | _, .conj φ ψ => .list [.atom "and", encodeFormula φ, encodeFormula ψ]
  | _, .disj φ ψ => .list [.atom "or", encodeFormula φ, encodeFormula ψ]
  | _, .all φ => .list [.atom "forall", encodeFormula φ]
  | _, .ex φ => .list [.atom "exists", encodeFormula φ]

/-- Read the grammar of formulas with `n` variables in scope. -/
def readFormula? : (n : ℕ) → SE → Option (Formula n)
  | _, .atom "false" => some .bot
  | n, .list [.atom "=", s, t] => do return .equal (← readTerm? n s) (← readTerm? n t)
  | n, .list [.atom "->", φ, ψ] => do return .imp (← readFormula? n φ) (← readFormula? n ψ)
  | n, .list [.atom "and", φ, ψ] => do return .conj (← readFormula? n φ) (← readFormula? n ψ)
  | n, .list [.atom "or", φ, ψ] => do return .disj (← readFormula? n φ) (← readFormula? n ψ)
  | n, .list [.atom "forall", φ] => (readFormula? (n + 1) φ).map .all
  | n, .list [.atom "exists", φ] => (readFormula? (n + 1) φ).map .ex
  | _, _ => none

/-- **Decode a formula**: the formula a canonical form denotes. -/
def decodeFormula (n : ℕ) (e : SE) : Option (Formula n) :=
  (readFormula? n e).bind fun φ => if encodeFormula φ = e then some φ else none

end Silmaril.Logic.Arithmetic.SExp
