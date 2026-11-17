module

public import Silmaril.Logic.Arithmetic.SExp.Thms
public meta import Silmaril.Logic.Arithmetic.SExp.Thms

/-!
# First-order arithmetic as S-expressions: examples

Printed and parsed sentences in the default presentation `silmaril.arithmetic.formula` and in the
second presentation `silmaril.arithmetic.formula.words`, checked by evaluation (`#guard`; a parsed
formula is compared by its canonical form), and inputs that are rejected. The printer writes every
token followed by one space.
-/

@[expose] public section

namespace Silmaril.Logic.Arithmetic.SExp.Examples

#guard (codec 0).print (.equal (.add .zero .zero) .zero) = "( = ( + zero zero ) zero ) ".toUTF8.toList
#guard (wordsCodec 0).print (.equal (.add .zero .zero) .zero) = "( = ( add zero zero ) zero ) ".toUTF8.toList
#guard ((codec 0).parse "(forall (or (= (var 0) zero) (exists (= (var 1) (succ (var 0))))))".toUTF8.toList).map
    encodeFormula = some (encodeFormula (Formula.all (.disj (.equal (.var 0) .zero)
      (.ex (.equal (.var 1) (.succ (.var 0))))) : Sentence))
#guard ((wordsCodec 0).parse "(= (mul zero zero) zero)".toUTF8.toList).map encodeFormula =
    some (encodeFormula (Formula.equal (.mul .zero .zero) .zero : Sentence))
-- rejected: a free variable in a sentence, an unknown keyword, a non-canonical numeral,
-- the other presentation's keyword
#guard ((codec 0).parse "(= (var 0) zero)".toUTF8.toList).isNone
#guard ((codec 0).parse "(= (plus zero zero) zero)".toUTF8.toList).isNone
#guard ((codec 1).parse "(= (var 00) zero)".toUTF8.toList).isNone
#guard ((codec 0).parse "(= (add zero zero) zero)".toUTF8.toList).isNone
#guard ((wordsCodec 0).parse "(= (+ zero zero) zero)".toUTF8.toList).isNone

end Silmaril.Logic.Arithmetic.SExp.Examples
