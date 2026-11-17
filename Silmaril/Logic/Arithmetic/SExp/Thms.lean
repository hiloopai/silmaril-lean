module

public import Silmaril.Logic.Arithmetic.SExp.Defs
public import Silmaril.Logic.Concrete.Codec.Thms
public import Mathlib.Logic.Equiv.Basic
import Silmaril.Proofs.Logic.Arithmetic.SExp.Basic

/-!
# First-order arithmetic as S-expressions: the presentation and its laws

* `decodeFormula_eq_some_iff`: the decoder accepts exactly the canonical forms.
* `legal_encodeFormula`: every printed atom is legal, so `parse_print` holds for every formula.
* `wordsCodec n`: a second presentation, `silmaril.arithmetic.formula.words`, by renaming
  `+`/`*` to `add`/`mul`; `words_induces`: the renaming induces the identity on formulas.
* `codec n`: the presentation `silmaril.arithmetic.formula` (version 1) of formulas with `n`
  variables in scope, as an `SExpCodec`; `sentenceCodec := codec 0`.
-/

@[expose] public section

namespace Silmaril.Logic.Arithmetic.SExp

open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Smt.SExpr.Writer (LegalExpr)
open Silmaril.Logic.Concrete (SExpCodec)

theorem decodeFormula_eq_some_iff {n : ℕ} {e : SE} {φ : Formula n} :
    decodeFormula n e = some φ ↔ encodeFormula φ = e :=
  Proofs.Logic.Arithmetic.SExp.decodeFormula_eq_some_iff

theorem legal_encodeFormula {n : ℕ} (φ : Formula n) : LegalExpr (encodeFormula φ) :=
  Proofs.Logic.Arithmetic.SExp.legal_encodeFormula φ

/-- **The default presentation of arithmetic formulas** with `n` variables in scope. -/
def codec (n : ℕ) : SExpCodec (Formula n) where
  name := "silmaril.arithmetic.formula"
  version := "1"
  encode := encodeFormula
  decode := decodeFormula n
  decode_eq_some_iff _ _ := decodeFormula_eq_some_iff

/-- The presentation of sentences. -/
abbrev sentenceCodec : SExpCodec Sentence := codec 0

/-- **Bytes round trip**, for every formula. -/
theorem parse_print {n : ℕ} (φ : Formula n) : (codec n).parse ((codec n).print φ) = some φ :=
  (codec n).parse_print φ (legal_encodeFormula φ)

/-- The keyword renaming `+ ↔ add`, `* ↔ mul` (every other atom unchanged). -/
def wordsRenaming : String ≃ String := (Equiv.swap "+" "add").trans (Equiv.swap "*" "mul")

/-- **A second presentation** of the same formulas, `silmaril.arithmetic.formula.words`
(version 1): `(add t u)` and `(mul t u)` for `+` and `×`. -/
def wordsCodec (n : ℕ) : SExpCodec (Formula n) :=
  (codec n).rename wordsRenaming "silmaril.arithmetic.formula.words" "1"

/-- The keyword renaming induces the identity on formulas: the two presentations present the same
logic, related by a simple S-expression morphism. -/
theorem words_induces (n : ℕ) :
    SExpCodec.Induces (codec n) (wordsCodec n) (Silmaril.Logic.Concrete.mapAtoms wordsRenaming) id :=
  (codec n).rename_induces _ _ _

end Silmaril.Logic.Arithmetic.SExp
