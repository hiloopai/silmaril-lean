module

public import Silmaril.Semantics.ITree.Defs
import Batteries.Tactic.Alias

/-!
# Interaction trees as coherent finite observations: proofs

Proofs for `Silmaril.Semantics.ITree.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.ITree

universe u v w

namespace Visible

private theorem map_comp {E : Type u → Type u} {A : Type v} {X Y Z : Type w}
    (f : X → Y) (g : Y → Z) (x : Visible E A X) :
    map g (map f x) = map (g ∘ f) x := by
  cases x with
  | ret => rfl
  | vis e k => rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Visible.map_comp := Silmaril.Elgot.ITree.Visible.map_comp

end Visible

private theorem Tree.eq_iff_observe {E : Type u → Type u} {A : Type v}
    {x y : Tree E A} : x = y ↔ ∀ n, x.observe n = y.observe n := by
  constructor
  · rintro rfl n
    rfl
  · exact Tree.ext
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Tree.eq_iff_observe := Silmaril.Elgot.ITree.Tree.eq_iff_observe

@[simp] private theorem tau_eq {E : Type u → Type u} {A : Type v} (t : Tree E A) : tau t = t := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.tau_eq := Silmaril.Elgot.ITree.tau_eq

end Silmaril.Elgot.ITree
