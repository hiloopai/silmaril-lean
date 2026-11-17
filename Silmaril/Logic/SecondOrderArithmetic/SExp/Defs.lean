module

public import Silmaril.Logic.SecondOrderArithmetic.Base
public import Silmaril.Logic.Smt.SExpr.Writer.Defs

/-!
# Second-order arithmetic as S-expressions (presentation `silmaril.soa.formula`, version 1)

The default concrete presentation of the two-sorted language of `Silmaril.Logic.SecondOrderArithmetic`,
with names as atoms (`N := String`):

```
term    ::= (var x) | zero | (succ term) | (+ term term) | (* term term)
formula ::= (= term term) | (< term term) | (in term X) | (set= X Y) | (not formula)
          | (-> formula formula) | (iff formula formula) | (and formula formula)
          | (forall x formula) | (exists x formula) | (forall-set X formula) | (exists-set X formula)
```

Number and set variables are both atoms; the sort of a name is fixed by its position. The decoder
accepts exactly the canonical forms (`Thms`). The byte round trip holds exactly for formulas whose
names are legal atoms (`Thms`).
-/

@[expose] public section

namespace Silmaril.Logic.SecondOrderArithmetic.SExp

open Silmaril.Logic.Smt (SE)

/-- The concrete form of a term. -/
def encodeTerm : Term String → SE
  | .var x => .list [.atom "var", .atom x]
  | .zero => .atom "zero"
  | .succ t => .list [.atom "succ", encodeTerm t]
  | .add t u => .list [.atom "+", encodeTerm t, encodeTerm u]
  | .mul t u => .list [.atom "*", encodeTerm t, encodeTerm u]

/-- Read the grammar of terms. -/
def readTerm? : SE → Option (Term String)
  | .list [.atom "var", .atom x] => some (.var x)
  | .atom "zero" => some .zero
  | .list [.atom "succ", t] => (readTerm? t).map .succ
  | .list [.atom "+", t, u] => do return .add (← readTerm? t) (← readTerm? u)
  | .list [.atom "*", t, u] => do return .mul (← readTerm? t) (← readTerm? u)
  | _ => none

/-- The concrete form of a formula. -/
def encodeFormula : Formula String → SE
  | .equal t u => .list [.atom "=", encodeTerm t, encodeTerm u]
  | .less t u => .list [.atom "<", encodeTerm t, encodeTerm u]
  | .member t X => .list [.atom "in", encodeTerm t, .atom X]
  | .setEqual X Y => .list [.atom "set=", .atom X, .atom Y]
  | .neg φ => .list [.atom "not", encodeFormula φ]
  | .imp φ ψ => .list [.atom "->", encodeFormula φ, encodeFormula ψ]
  | .iff φ ψ => .list [.atom "iff", encodeFormula φ, encodeFormula ψ]
  | .conj φ ψ => .list [.atom "and", encodeFormula φ, encodeFormula ψ]
  | .all x φ => .list [.atom "forall", .atom x, encodeFormula φ]
  | .ex x φ => .list [.atom "exists", .atom x, encodeFormula φ]
  | .setAll X φ => .list [.atom "forall-set", .atom X, encodeFormula φ]
  | .setEx X φ => .list [.atom "exists-set", .atom X, encodeFormula φ]

/-- Read the grammar of formulas. -/
def readFormula? : SE → Option (Formula String)
  | .list [.atom "=", t, u] => do return .equal (← readTerm? t) (← readTerm? u)
  | .list [.atom "<", t, u] => do return .less (← readTerm? t) (← readTerm? u)
  | .list [.atom "in", t, .atom X] => (readTerm? t).map (.member · X)
  | .list [.atom "set=", .atom X, .atom Y] => some (.setEqual X Y)
  | .list [.atom "not", φ] => (readFormula? φ).map .neg
  | .list [.atom "->", φ, ψ] => do return .imp (← readFormula? φ) (← readFormula? ψ)
  | .list [.atom "iff", φ, ψ] => do return .iff (← readFormula? φ) (← readFormula? ψ)
  | .list [.atom "and", φ, ψ] => do return .conj (← readFormula? φ) (← readFormula? ψ)
  | .list [.atom "forall", .atom x, φ] => (readFormula? φ).map (.all x)
  | .list [.atom "exists", .atom x, φ] => (readFormula? φ).map (.ex x)
  | .list [.atom "forall-set", .atom X, φ] => (readFormula? φ).map (.setAll X)
  | .list [.atom "exists-set", .atom X, φ] => (readFormula? φ).map (.setEx X)
  | _ => none

/-- **Decode a formula**: the formula a canonical form denotes. -/
def decodeFormula (e : SE) : Option (Formula String) :=
  (readFormula? e).bind fun φ => if encodeFormula φ = e then some φ else none

end Silmaril.Logic.SecondOrderArithmetic.SExp
