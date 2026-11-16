module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Thms
public meta import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Defs

/-!
# Extensional MLTT S-expressions: examples

Printed and parsed judgments, checked by evaluation (`#guard`; a parsed judgment is compared by
its concrete form, which determines it), and malformed inputs that the parser rejects. The general statements are in `Thms` (`parseJdg_printJdg`, `legalNames_of_parseJdg`).
-/

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Examples


/-- `x : ℕ ⊢ x ≡ x : ℕ`. -/
def varRefl : EJdg := ⟨.cons .nil "x" .nats, .nats, .fv "x", .fv "x"⟩

/-- `⊢ (λ y : ℕ. y) 0 ≡ 0 : ℕ`. -/
def beta : EJdg := ⟨.nil, .nats, .app (.abs .nats (.bv 0)) .zero, .zero⟩

/-- `⊢ Π (A : U₀). A → A ≡ Π (A : U₀). A → A : U₁`, with the bound variables as de Bruijn
indices (`bv 0` is the innermost binder). -/
def polyId : EJdg :=
  ⟨.nil, .univ 1, .pi (.univ 0) (.pi (.bv 0) (.bv 1)), .pi (.univ 0) (.pi (.bv 0) (.bv 1))⟩

#guard printJdg (⟨.cons .nil "x" .nats, .nats, .fv "x", .fv "x"⟩ : EJdg) = "( jdg ( ctx ( x nat ) ) nat ( fv x ) ( fv x ) ) ".toUTF8.toList
#guard printJdg (⟨.nil, .nats, .app (.abs .nats (.bv 0)) .zero, .zero⟩ : EJdg) = "( jdg ( ctx ) nat ( app ( lam nat ( bv 0 ) ) zero ) zero ) ".toUTF8.toList
#guard (parseJdg (printJdg (⟨.cons .nil "x" .nats, .nats, .fv "x", .fv "x"⟩ : EJdg))).map encodeJdg = some (encodeJdg (⟨.cons .nil "x" .nats, .nats, .fv "x", .fv "x"⟩ : EJdg))
#guard (parseJdg (printJdg (⟨.nil, .nats, .app (.abs .nats (.bv 0)) .zero, .zero⟩ : EJdg))).map encodeJdg = some (encodeJdg (⟨.nil, .nats, .app (.abs .nats (.bv 0)) .zero, .zero⟩ : EJdg))
#guard (parseJdg (printJdg (⟨.nil, .univ 1, .pi (.univ 0) (.pi (.bv 0) (.bv 1)), .pi (.univ 0) (.pi (.bv 0) (.bv 1))⟩ : EJdg))).map encodeJdg = some (encodeJdg (⟨.nil, .univ 1, .pi (.univ 0) (.pi (.bv 0) (.bv 1)), .pi (.univ 0) (.pi (.bv 0) (.bv 1))⟩ : EJdg))
-- malformed: an index out of scope, a missing judgment part, an illegal name, a term for a context
#guard (parseJdg ("(jdg (ctx) nat (bv 0) (bv 0))".toUTF8.toList)).isNone
#guard (parseJdg ("(jdg (ctx) nat zero)".toUTF8.toList)).isNone
#guard (parseJdg ("(jdg (ctx (\"x\" nat)) nat zero zero)".toUTF8.toList)).isNone
#guard (parseJdg ("(jdg nat nat zero zero)".toUTF8.toList)).isNone
-- a name the reader cannot read is printed, but does not parse back
#guard (parseJdg (printJdg ⟨.nil, .nats, .fv "a b", .fv "a b"⟩)).isNone

/-- Every judgment with legal names round-trips (`Thms`), here at `beta` (it has no names). -/
example : parseJdg (printJdg beta) = some beta :=
  parseJdg_printJdg beta (by simp [LegalNames, beta, ctxDecls, names])

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Examples
