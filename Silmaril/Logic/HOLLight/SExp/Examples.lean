module

public import Silmaril.Logic.HOLLight.SExp.Thms
public meta import Silmaril.Logic.HOLLight.SExp.Defs

/-!
# HOL Light S-expressions: examples

Printed and parsed forms, checked by evaluation (`#guard`), and malformed inputs that the parser
rejects. The printer writes every token followed by one space; the parser accepts any whitespace
and `;` comments. The general statements are in `Thms` (`parseTm_printTm`, `decodeTm_eq_some_iff`).
-/

@[expose] public section

namespace Silmaril.Logic.HOLLight.SExp.Examples

open Silmaril.Logic.HOLLight


/-- `λ x : bool. x`. -/
def idBool : Tm := .lam .bool (.bvar 0)

/-- `(=) (λ x : bool. x) (λ x : bool. x)`, at the type `bool → bool`. -/
def idEqId : Tm := .app (.app (.const (.eq (.arr .bool .bool))) idBool) idBool

#guard printTm (Tm.lam .bool (.bvar 0)) = "( lam bool ( bvar 0 ) ) ".toUTF8.toList
#guard printTm (Tm.app (.app (.const (.eq (.arr .bool .bool))) (Tm.lam .bool (.bvar 0))) (Tm.lam .bool (.bvar 0))) = "( app ( app ( = ( -> bool bool ) ) ( lam bool ( bvar 0 ) ) ) ( lam bool ( bvar 0 ) ) ) ".toUTF8.toList
#guard parseTm ("(lam bool (bvar 0))".toUTF8.toList) = some (Tm.lam .bool (.bvar 0))
#guard parseTm ("  (lam bool ; a comment\n (bvar 0))".toUTF8.toList) = some (Tm.lam .bool (.bvar 0))
#guard parseTm (printTm (Tm.app (.app (.const (.eq (.arr .bool .bool))) (Tm.lam .bool (.bvar 0))) (Tm.lam .bool (.bvar 0)))) = some (Tm.app (.app (.const (.eq (.arr .bool .bool))) (Tm.lam .bool (.bvar 0))) (Tm.lam .bool (.bvar 0)))
#guard parseTm ("(fvar 12 (tyapp 3 ind (tyvar 0)))".toUTF8.toList) = some (.fvar 12 (.app 3 [.ind, .var 0]))
#guard parseTm ("(const 7 bool ind)".toUTF8.toList) = some (.const (.user 7 [.bool, .ind]))
-- malformed: a non-canonical numeral, a missing argument, an unknown keyword, two forms
#guard parseTm ("(bvar 007)".toUTF8.toList) = none
#guard parseTm ("(app (lam bool (bvar 0)))".toUTF8.toList) = none
#guard parseTm ("(lambda bool (bvar 0))".toUTF8.toList) = none
#guard parseTm ("(bvar 0) (bvar 1)".toUTF8.toList) = none
#guard parseTm ("(bvar 0".toUTF8.toList) = none

/-- Every term round-trips (`Thms`), here at `idEqId`. -/
example : parseTm (printTm idEqId) = some idEqId := parseTm_printTm idEqId

end Silmaril.Logic.HOLLight.SExp.Examples
