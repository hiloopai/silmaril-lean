module

public import Silmaril.Semantics.ITreeInterpret.Defs
public import Silmaril.Proofs.Semantics.ITreeInterpret.Reify
import all Silmaril.Proofs.Semantics.ITreeInterpret.Reify
import Batteries.Tactic.Alias

/-!
# Interpret.Hom: proofs

Proofs for `Silmaril.Semantics.ITreeInterpret.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.ITree.Interpret

universe u v

variable {E : Type u → Type u} {m : Type u → Type v} [Monad m] [Iterate m]

namespace Hom

variable {handler : Handler E m} (f : Hom (E := E) (m := m) handler)

private theorem map_stepTree {A : Type u} [Small.{u} (Tree E A)] (t : Tree E A) :
    f.map (stepTree (E := E) (m := Tree E) trigger t) =
      stepTree (E := E) (m := m) handler t := by
  rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, event, next, rfl⟩
  · simp only [stepTree_diverge, f.map_pure]
  · simp only [stepTree_ret, f.map_pure]
  · simp only [stepTree_vis, f.map_bind, f.map_trigger, f.map_pure]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.Hom.map_stepTree := Silmaril.Elgot.ITree.Interpret.Hom.map_stepTree

private theorem map_step {A : Type u} [Small.{u} (Tree E A)] (state : Shrink.{u} (Tree E A)) :
    f.map (step (E := E) (m := Tree E) trigger state) =
      step (E := E) (m := m) handler state :=
  f.map_stepTree ((equivShrink _).symm state)
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.Hom.map_step := Silmaril.Elgot.ITree.Interpret.Hom.map_step

private theorem unique {A : Type u} [Small.{u} (Tree E A)] (t : Tree E A) :
    f.map t = fold (E := E) (m := m) handler t := by
  calc
    f.map t = f.map (fold (E := E) (m := Tree E) trigger t) :=
      congrArg f.map (fold_self t).symm
    _ = iter (fun state => f.map (step (E := E) (m := Tree E) trigger state))
        (equivShrink _ t) := f.map_iter _ _
    _ = iter (step (E := E) (m := m) handler) (equivShrink _ t) := by
      congr 1
      funext state
      exact f.map_step state
    _ = fold (E := E) (m := m) handler t := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.Hom.unique := Silmaril.Elgot.ITree.Interpret.Hom.unique

@[ext] private theorem ext {f g : Hom (E := E) (m := m) handler}
    (h : ∀ {A : Type u} (t : Tree E A), f.map t = g.map t) : f = g := by
  cases f
  cases g
  congr
  funext A t
  exact h t
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.Hom.ext := Silmaril.Elgot.ITree.Interpret.Hom.ext

private theorem subsingleton [∀ A : Type u, Small.{u} (Tree E A)] :
    Subsingleton (Hom (E := E) (m := m) handler) := by
  constructor
  intro f g
  apply Hom.ext
  intro A t
  exact (f.unique t).trans (g.unique t).symm
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.Hom.subsingleton := Silmaril.Elgot.ITree.Interpret.Hom.subsingleton

end Hom

end Silmaril.Elgot.ITree.Interpret
