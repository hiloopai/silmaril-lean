module

public import Silmaril.Logic.ACL2.Standard.Objects.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard

namespace Object

/-- Logical EQL is structural equality on the full ACL2 object domain. -/
def eql (x y : Object) : Object := x.equal y

/-- ACL2 NOT returns T exactly when its argument is NIL. -/
def logicalNot (x : Object) : Object := x.equal .nil

/-- Logical MV-NTH traverses the cons spine. A nonpositive or noninteger index
selects its head, and an atomic remainder yields NIL. -/
def mvNth (index : Object) : Object → Object
  | .cons head tail =>
    if index.zp = .nil then mvNth ((integer (-1)).binaryAdd index) tail else head
  | _ => .nil

end Object

namespace Pure

/-- Resolve the checked helpers by exact home package, name, and arity. -/
def binding (name : Name) (arity : Nat) : Option ((Fin arity → Object) → Object) :=
  match arity with
  | 1 =>
    if name = ⟨"COMMON-LISP", "NOT"⟩ then some (fun args => (args 0).logicalNot)
    else none
  | 2 =>
    if name = ⟨"COMMON-LISP", "EQL"⟩ then some (fun args => (args 0).eql (args 1))
    else if name = ⟨"ACL2", "MV-NTH"⟩ then some (fun args => (args 0).mvNth (args 1))
    else none
  | _ => none

end Pure

end Silmaril.Logic.ACL2.Standard
