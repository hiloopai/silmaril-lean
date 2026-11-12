module

public import Silmaril.Cerberus.Elaboration.ControlFlow.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.ControlFlow
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

theorem canonicalBoolean (symbol : Sym) :
    CanonicalBoolean ⟨symbol, symbolPattern symbol .boolean, symbolPure symbol⟩ := ⟨rfl, rfl⟩

theorem decision_shape (binders : Binders) : decision binders =
    .mk [] (.case_ binders.test.expression
      [(.mk [] (.ctor .specified [binders.specified.pattern]),
        .mk [] (.pure (.mk [] () (.if_
          (.mk [] () (.not (.mk [] () (.op .eq binders.specified.expression (integer 1)))))
          (boolean true) (boolean false))))),
       (.mk [] (.ctor .unspecified [wildcard .ctype]),
        .mk [] (.nd [pureEffect (boolean true), pureEffect (boolean false)]))]) := rfl

theorem finish_shape (prepared : State.WrappedSymbol) (binders : Binders)
    (condition yes no : Effect) : finish prepared binders condition yes no =
    .mk [] (.sseq binders.test.pattern condition
      (.mk [] (.sseq prepared.pattern (decision binders)
        (.mk [] (.if_ prepared.expression yes no))))) := rfl

end Silmaril.Cerberus.Elaboration.ControlFlow
