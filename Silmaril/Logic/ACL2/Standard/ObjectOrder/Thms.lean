module

public import Silmaril.Logic.ACL2.Standard.ObjectOrder.Defs
import Silmaril.Proofs.Logic.ACL2.Standard.ObjectOrder

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.ObjectOrder

theorem stringLessIndex_spec (x y : ByteString) (i : Nat) :
    (stringLessIndex x y i).isSome = true ↔ x < y :=
  Proofs.Logic.ACL2.Standard.ObjectOrder.stringLessIndex_spec x y i

theorem stringLeIndex_spec (x y : ByteString) : (stringLeIndex x y).isSome = true ↔ x ≤ y :=
  Proofs.Logic.ACL2.Standard.ObjectOrder.stringLeIndex_spec x y

theorem symbolLess_spec (x y : Symbol) : symbolLess x y = true ↔
    x.spelling < y.spelling ∨ x.spelling = y.spelling ∧ x.package < y.package :=
  Proofs.Logic.ACL2.Standard.ObjectOrder.symbolLess_spec x y

theorem lexorder_atoms (x y : Object) (hx : x.consp = false) (hy : y.consp = false) :
    lexorder x y = true ↔ key x ≤ key y :=
  Proofs.Logic.ACL2.Standard.ObjectOrder.lexorder_atoms x y hx hy

theorem lexorder_atom_cons (x a b : Object) (hx : x.consp = false) : lexorder x (.cons a b) = true :=
  Proofs.Logic.ACL2.Standard.ObjectOrder.lexorder_atom_cons x a b hx

theorem lexorder_cons_atom (a b y : Object) (hy : y.consp = false) : lexorder (.cons a b) y = false :=
  Proofs.Logic.ACL2.Standard.ObjectOrder.lexorder_cons_atom a b y hy

theorem lexorder_cons (a b c d : Object) :
    lexorder (.cons a b) (.cons c d) = if a = c then lexorder b d else lexorder a c :=
  Proofs.Logic.ACL2.Standard.ObjectOrder.lexorder_cons a b c d

theorem lexorder_symbols (x y : Symbol) : lexorder (.symbol x) (.symbol y) = !symbolLess y x :=
  Proofs.Logic.ACL2.Standard.ObjectOrder.lexorder_symbols x y

theorem lexorder_strings (x y : ByteString) :
    lexorder (.string x) (.string y) = (stringLeIndex x y).isSome :=
  Proofs.Logic.ACL2.Standard.ObjectOrder.lexorder_strings x y

theorem lexorder_alphorder (x y : Object) (hx : x.consp = false) (hy : y.consp = false) :
    lexorder x y = alphorder x y :=
  Proofs.Logic.ACL2.Standard.ObjectOrder.lexorder_alphorder x y hx hy

/-- Stock ACL2 defines strict order as LEXORDER with the equality case removed. -/
theorem before_native (x y : Object) : before x y = (lexorder x y && decide (x ≠ y)) :=
  Proofs.Logic.ACL2.Standard.ObjectOrder.before_native x y

theorem before_irrefl (x : Object) : before x x = false :=
  Proofs.Logic.ACL2.Standard.ObjectOrder.before_irrefl x

theorem before_trans {x y z : Object} (hxy : before x y = true) (hyz : before y z = true) :
    before x z = true := Proofs.Logic.ACL2.Standard.ObjectOrder.before_trans hxy hyz

theorem before_asymm {x y : Object} (h : before x y = true) : before y x = false :=
  Proofs.Logic.ACL2.Standard.ObjectOrder.before_asymm h

theorem before_trichotomy (x y : Object) : before x y = true ∨ x = y ∨ before y x = true :=
  Proofs.Logic.ACL2.Standard.ObjectOrder.before_trichotomy x y

end Silmaril.Logic.ACL2.Standard.ObjectOrder
