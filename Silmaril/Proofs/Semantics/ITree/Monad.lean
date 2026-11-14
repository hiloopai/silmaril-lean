module

public import Silmaril.Semantics.ITree.Defs
public import Silmaril.Proofs.Semantics.ITree.Basic
import all Silmaril.Proofs.Semantics.ITree.Basic
import Batteries.Tactic.Alias

/-!
# Monad: proofs

Proofs for `Silmaril.Semantics.ITree.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.ITree

universe u v

namespace Approx

end Approx

@[simp] private theorem observe_pure {E : Type u → Type u} {A : Type v} (a : A) (n : Nat) :
    (pure a : Tree E A).observe n = match n with
      | 0 => PUnit.unit
      | _ + 1 => Part.some (.ret a) := by
  cases n <;> rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.observe_pure := Silmaril.Elgot.ITree.observe_pure

@[simp] private theorem observe_bind {E : Type u → Type u} {A B : Type v}
    (t : Tree E A) (k : A → Tree E B) (n : Nat) :
    (t >>= k).observe n = Approx.bind n (t.observe n) (fun a => (k a).observe n) := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.observe_bind := Silmaril.Elgot.ITree.observe_bind

namespace Approx

private theorem pure_bind {E : Type u → Type u} {A B : Type v}
    (n : Nat) (a : A) (k : A → Approx E B n) :
    bind n ((ret (E := E) a).observe n) k = k a := by
  cases n with
  | zero => cases k a; rfl
  | succ => simp [bind, ret]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Approx.pure_bind := Silmaril.Elgot.ITree.Approx.pure_bind

private theorem bind_pure {E : Type u → Type u} {A : Type v}
    (n : Nat) (x : Approx E A n) :
    bind n x (fun a => (ret (E := E) a).observe n) = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
      change x >>= (fun node => match node with
        | .ret a => (ret (E := E) a).observe (n + 1)
        | .vis e next => Part.some (.vis e (fun r =>
            bind n (next r) (fun a => truncate n ((ret (E := E) a).observe (n + 1)))))) = x
      calc
        _ = x >>= pure := by
          apply congrArg (x >>= ·)
          funext node
          cases node with
          | ret => rfl
          | vis e next =>
              simp [ret]
              funext r
              have hret (a : A) : truncate n (Part.some (.ret a)) =
                  (ret (E := E) a).observe n := (ret (E := E) a).coherent n
              simp_rw [hret]
              exact ih (next r)
        _ = x := _root_.bind_pure x
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Approx.bind_pure := Silmaril.Elgot.ITree.Approx.bind_pure

private theorem bind_assoc {E : Type u → Type u} {A B C : Type v}
    (n : Nat) (x : Approx E A n) (f : A → Approx E B n) (g : B → Approx E C n) :
    bind n (bind n x f) g = bind n x (fun a => bind n (f a) g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [bind, LawfulMonad.bind_assoc]
      apply congrArg (x >>= ·)
      funext node
      cases node with
      | ret a => rfl
      | vis e next =>
          simp
          funext r
          rw [ih]
          congr
          funext a
          exact (truncate_bind n (f a) g).symm
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Approx.bind_assoc := Silmaril.Elgot.ITree.Approx.bind_assoc

end Approx

instance _root_.Silmaril.Proofs.Semantics.Elgot.ITree.instLawfulMonad (E : Type u → Type u) : LawfulMonad (Tree E) :=
  LawfulMonad.mk'
    (id_map := fun t => by
      apply Tree.ext
      intro n
      change Approx.bind n (t.observe n) (fun a => (ret a).observe n) = t.observe n
      exact Approx.bind_pure n (t.observe n))
    (pure_bind := fun a f => by
      apply Tree.ext
      intro n
      exact Approx.pure_bind n a (fun x => (f x).observe n))
    (bind_assoc := fun t f g => by
      apply Tree.ext
      intro n
      exact Approx.bind_assoc n (t.observe n) (fun a => (f a).observe n)
        (fun b => (g b).observe n))
    (bind_pure_comp := fun f t => by
      apply Tree.ext
      intro n
      change Approx.bind n (t.observe n) (fun a => (ret (f a)).observe n) = _
      rfl)

end Silmaril.Elgot.ITree
