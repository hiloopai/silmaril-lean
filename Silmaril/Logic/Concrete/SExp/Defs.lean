module

public import Silmaril.Logic.Smt.SExpr.Writer.Defs

/-!
# Concrete syntax over S-expressions: numerals

Shared pieces of the S-expression concrete syntaxes of the logics (HOL in
`Silmaril.Logic.HOLLight.SExp`, extensional MLTT in `Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp`),
over `Silmaril.Logic.Smt.SE` and its ASCII reader and writer.

A numeral `n` is the decimal atom `Nat.repr n`. `num?` reads canonical numerals only (no sign, no
leading zeros), so that every numeral has one concrete form.
-/

@[expose] public section

namespace Silmaril.Logic.Concrete.SExp

open Silmaril.Logic.Smt (SE)

/-- A numeral: the decimal atom of `n`. -/
def num (n : Nat) : SE := .atom (Nat.repr n)

/-- Read a canonical numeral. -/
def num? : SE → Option Nat
  | .atom s => match s.toNat? with
    | some n => if Nat.repr n = s then some n else none
    | none => none
  | .list _ => none

end Silmaril.Logic.Concrete.SExp
