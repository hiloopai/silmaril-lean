module

public import Silmaril.Logic.Consequence.Soundness.Defs
public import Silmaril.Logic.Arithmetic.Peano
public import Silmaril.Logic.Arithmetic.Semantics
public import Silmaril.Logic.Arithmetic.SExp.Defs

/-!
# Peano and Robinson arithmetic as consequence systems, with the standard interpretation

**Systems** on first-order arithmetic sentences (`Silmaril.Logic.Arithmetic`, de Bruijn):
* `paDerives`: `Γ ⊢ φ` when there is an explicit proof tree `PAProof Γ φ` (classical natural
  deduction; axioms: Robinson's Q, `BasicAxiom` and `predecessor`, plus the induction schema
  `inductionSchema` for every formula);
* `qDerives`: the same with Robinson's Q only (`QProof`).

**The standard interpretation** (`standard`): the single model ℕ, with `0`, successor, `+`, `×` and
`=` interpreted as Lean's on `ℕ` (`Formula.eval`). `truth` is its semantic consequence.

**Concrete syntax.** `paConcrete` and `truthConcrete` are the same systems read over the default
presentation `silmaril.arithmetic.formula` (version 1), by `System.viaCodec`.
-/

@[expose] public section

namespace Silmaril.Consequence.Arithmetic

open Silmaril.Logic.Arithmetic Silmaril.Logic.Concrete

/-- **PA derivability**: an explicit PA proof tree. -/
def paDerives : System (List Sentence) Sentence := fun Γ φ => Nonempty (PAProof Γ φ)

/-- **Q derivability**: an explicit Robinson-arithmetic proof tree. -/
def qDerives : System (List Sentence) Sentence := fun Γ φ => Nonempty (QProof Γ φ)

/-- **The standard interpretation**: one model, ℕ. -/
def standard : Satisfaction (List Sentence) Sentence where
  Model := Unit
  satAx _ Γ := Satisfies Fin.elim0 Γ
  satC _ φ := φ.eval Fin.elim0

/-- Truth in ℕ of the conclusion whenever the premises are true. -/
def truth : System (List Sentence) Sentence := standard.entails

end Silmaril.Consequence.Arithmetic
