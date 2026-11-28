module

public import Silmaril.Logic.ACL2.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Term

/-- Named calls in a typed term, including built-in operators. The list preserves
multiplicity and includes calls in all branches of a conditional. -/
def directCalls {S : Signature} {vars : Nat} : Term S vars → List (Name × Nat)
  | .var _ | .nil | .truth => []
  | @Term.app _ _ arity fn args => (fn.val, arity) :: (List.ofFn fun i => directCalls (args i)).flatten
  | .cons x y => (⟨"COMMON-LISP", "CONS"⟩, 2) :: (directCalls x ++ directCalls y)
  | .car x => (⟨"COMMON-LISP", "CAR"⟩, 1) :: directCalls x
  | .cdr x => (⟨"COMMON-LISP", "CDR"⟩, 1) :: directCalls x
  | .consp x => (⟨"COMMON-LISP", "CONSP"⟩, 1) :: directCalls x
  | .equal x y => (⟨"COMMON-LISP", "EQUAL"⟩, 2) :: (directCalls x ++ directCalls y)
  | .ite x y z => (⟨"COMMON-LISP", "IF"⟩, 3) :: (directCalls x ++ directCalls y ++ directCalls z)

end Silmaril.Logic.ACL2.Term
