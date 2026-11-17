module

public import Silmaril.Logic.SecondOrderArithmetic.SExp.Thms
public import Silmaril.Logic.SecondOrderArithmetic.Systems
public meta import Silmaril.Logic.SecondOrderArithmetic.SExp.Thms
public meta import Silmaril.Logic.SecondOrderArithmetic.Systems

/-!
# Second-order arithmetic as S-expressions: examples

Printed and parsed formulas of `silmaril.soa.formula`, checked by evaluation (`#guard`; compared
by canonical form), and inputs that are rejected.
-/

@[expose] public section

namespace Silmaril.Logic.SecondOrderArithmetic.SExp.Examples

#guard codec.print (.comprehension "x" "X" (.equal (.var "x") (.var "x"))) =
  "( exists-set X ( forall x ( iff ( in ( var x ) X ) ( = ( var x ) ( var x ) ) ) ) ) ".toUTF8.toList
#guard (codec.parse "(not (= (succ zero) zero))".toUTF8.toList).map encodeFormula =
  some (encodeFormula (.neg (.equal (.succ .zero) .zero)))
-- rejected: a set variable in number position, an unknown keyword, a missing argument
#guard (codec.parse "(in (var x) (var X))".toUTF8.toList).isNone
#guard (codec.parse "(forall-sets X (set= X X))".toUTF8.toList).isNone
#guard (codec.parse "(forall x)".toUTF8.toList).isNone

end Silmaril.Logic.SecondOrderArithmetic.SExp.Examples
