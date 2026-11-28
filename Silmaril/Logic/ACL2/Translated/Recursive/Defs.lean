module

public import Silmaril.Logic.ACL2.Recursive.Defs
public import Silmaril.Logic.ACL2.Translated.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Translated.Recursive

def conspName : Name := ⟨"COMMON-LISP", "CONSP"⟩
def cdrName : Name := ⟨"COMMON-LISP", "CDR"⟩
def eqName : Name := ⟨"COMMON-LISP", "EQ"⟩

variable {S : Signature} {scope : List Name}

/-- Project the old terms of the pure CDR-recursive profile. A caller using EQ must
establish that its logical definition applies EQUAL to the same two arguments. -/
def oldTerm : {raw : Raw} → Checked S scope raw → Option (Term Signature.empty scope.length)
  | _, .var slot _ => some (.var slot)
  | _, .quote (literal := .symbol name) _ _ =>
      if name = Standard.Symbol.nil.toName then some .nil else none
  | _, .ite test yes no => do
      return .ite (← oldTerm test) (← oldTerm yes) (← oldTerm no)
  | _, .call (name := name) _ (.cons arg .nil) => do
      let t ← oldTerm arg
      if name = conspName then some (.consp t)
      else if name = cdrName then some (.cdr t)
      else none
  | _, .call (name := name) _ (.cons lhs (.cons rhs .nil)) => do
      if name = eqName ∨ name = Primitive.equal.name then
        return .equal (← oldTerm lhs) (← oldTerm rhs)
      else none
  | _, _ => none

def oldArgs : {args : RawArgs} → CheckedArgs S scope args →
    Option (Fin args.arity → Term Signature.empty scope.length)
  | _, .nil => some Fin.elim0
  | _, .cons head tail => do
      return Fin.cases (← oldTerm head) (← oldArgs tail)

/-- Lower the checked term structurally. Calls to new symbols are separated from the
old terms in the tests and actuals. The member table resolves a call at its original arity. -/
def lowerBody (members : Signature) :
    {raw : Raw} → Checked S scope raw → Option (ACL2.Recursive.Body Signature.empty members scope.length)
  | _, .ite test yes no => do
      return .ite (← oldTerm test) (← lowerBody members yes) (← lowerBody members no)
  | _, .call (name := name) (actuals := actuals) (.external declared) args =>
      match members.resolve name actuals.arity with
      | some f => ACL2.Recursive.Body.call f <$> oldArgs args
      | none => ACL2.Recursive.Body.base <$> oldTerm (.call (.external declared) args)
  | _, term => ACL2.Recursive.Body.base <$> oldTerm term

end Silmaril.Logic.ACL2.Translated.Recursive
