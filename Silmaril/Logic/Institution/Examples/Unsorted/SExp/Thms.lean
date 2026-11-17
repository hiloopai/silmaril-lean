module

public import Silmaril.Logic.Institution.Examples.Unsorted.SExp.Defs
public import Silmaril.Logic.Concrete.Codec.Thms
import Silmaril.Proofs.Logic.Institution.Examples.Unsorted.SExp.Basic

/-!
# First-order logic as S-expressions: the presentation

`decodeFormula_eq_some_iff`: the decoder accepts exactly the canonical forms, checking scopes and
arities. `codec opArity relArity k` is the presentation `silmaril.fol.formula` (version 1) over the
named signature `named opArity relArity`; `sentenceCodec` is its closed fragment.
-/

@[expose] public section

namespace Silmaril.Logic.Institution.Examples.UFOL.SExp

open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Concrete (SExpCodec)

variable {opArity relArity : String → Option ℕ}

theorem decodeFormula_eq_some_iff {k : ℕ} {e : SE} {φ : Formula (named opArity relArity) k} :
    decodeFormula opArity relArity k e = some φ ↔ encodeFormula φ = e :=
  Proofs.Logic.Institution.Examples.UFOL.SExp.decodeFormula_eq_some_iff

/-- **The default presentation of first-order formulas** over a named signature. -/
def codec (opArity relArity : String → Option ℕ) (k : ℕ) :
    SExpCodec (Formula (named opArity relArity) k) where
  name := "silmaril.fol.formula"
  version := "1"
  encode := encodeFormula
  decode := decodeFormula opArity relArity k
  decode_eq_some_iff _ _ := decodeFormula_eq_some_iff

/-- The presentation of sentences. -/
abbrev sentenceCodec (opArity relArity : String → Option ℕ) := codec opArity relArity 0

end Silmaril.Logic.Institution.Examples.UFOL.SExp
