module

public import Silmaril.Logic.Metamath.Grammar.Derivation

@[expose] public section

/-!
# Decidable equality of tree statements

Tree expressions, tree hypotheses and tree assertions have decidable equality
when their labels, typecodes and variables do. Concrete axiom sets use these
instances to check membership and equality of tree assertions by `decide`.
-/

namespace Silmaril.Logic.Metamath.Grammar

deriving instance DecidableEq for TExpr
deriving instance DecidableEq for THyp
deriving instance DecidableEq for TAssertion

end Silmaril.Logic.Metamath.Grammar
