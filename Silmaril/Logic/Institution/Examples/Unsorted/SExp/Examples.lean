module

public import Silmaril.Logic.Consequence.FirstOrder.Thms
public meta import Silmaril.Logic.Consequence.FirstOrder.Thms

/-!
# First-order logic as S-expressions: examples

Sentences of the signature `orderSig` (`zero`, `succ`, `<`) in `silmaril.fol.formula`, checked by
evaluation (`#guard`; compared by canonical form), and inputs that are rejected: a wrong arity, an
unknown symbol, a variable out of scope.
-/

@[expose] public section

namespace Silmaril.Logic.Institution.Examples.UFOL.SExp.Examples

open Silmaril.Consequence.FirstOrder

#guard orderCodec.print irrefl = "( forall ( not ( rel < ( var 0 ) ( var 0 ) ) ) ) ".toUTF8.toList
#guard (orderCodec.parse "(forall (rel < (var 0) (app succ (var 0))))".toUTF8.toList).map encodeFormula =
  some (encodeFormula ltSucc)
#guard (orderCodec.parse "(forall (rel < (var 0)))".toUTF8.toList).isNone
#guard (orderCodec.parse "(forall (rel <= (var 0) (var 0)))".toUTF8.toList).isNone
#guard (orderCodec.parse "(rel < (var 0) (var 0))".toUTF8.toList).isNone
#guard (orderCodec.parse "(forall (rel < (var 0) (app succ (var 0) (var 0))))".toUTF8.toList).isNone

end Silmaril.Logic.Institution.Examples.UFOL.SExp.Examples
