module

public import Silmaril.Logic.ACL2.Translated.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Translated.Definition

/-- The new symbol is interpreted by the checked body for every argument vector. -/
theorem equation {S : Signature} (D : Definition S) (M : Interpretation S)
    (args : Fin D.formals.length → Standard.Object) :
    D.extend M D.symbol args = D.body.eval M args := by
  simp [extend, symbol, Signature.addSymbol]

/-- The extension preserves the denotation of every imported symbol. -/
theorem preserves {S : Signature} (D : Definition S) (M : Interpretation S) {n : Nat}
    (f : S.Symbol n) (args : Fin n → Standard.Object) :
    D.extend M (D.inclusion.symbol f) args = M f args := by
  simp [extend, Signature.Hom.symbol, Signature.ne_of_fresh D.fresh f]

end Silmaril.Logic.ACL2.Translated.Definition
